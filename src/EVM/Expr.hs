{-# LANGUAGE DataKinds #-}

{-|
   Helper functions for working with Expr instances.
   All functions here will return a concrete result if given a concrete input.
-}
module EVM.Expr where

import Prelude hiding (LT, GT)
import Data.Bits hiding (And, Xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.DoubleWord (Int256, Word256(Word256), Word128(Word128))
import Data.List
import Data.Map.Strict qualified as Map
import Data.Maybe (mapMaybe)
import Data.Semigroup (Any, Any(..), getAny)
import Data.Vector qualified as V
import Data.Vector.Storable qualified as VS
import Data.Vector.Storable.ByteString
import Data.Word (Word8, Word32)
import Witch (unsafeInto, into, tryFrom)
import Data.Text qualified as TS

import Optics.Core

import EVM.Traversals
import EVM.Types


-- ** Stack Ops ** ---------------------------------------------------------------------------------


op1 :: (Expr EWord -> Expr EWord)
    -> (W256 -> W256)
    -> Expr EWord -> Expr EWord
op1 _ concrete (Lit x) = Lit (concrete x)
op1 symbolic _ x = symbolic x

op2 :: (Expr EWord -> Expr EWord -> Expr EWord)
    -> (W256 -> W256 -> W256)
    -> Expr EWord -> Expr EWord -> Expr EWord
op2 _ concrete (Lit x) (Lit y) = Lit (concrete x y)
op2 symbolic _ x y = symbolic x y

op3 :: (Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord)
    -> (W256 -> W256 -> W256 -> W256)
    -> Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
op3 _ concrete (Lit x) (Lit y) (Lit z) = Lit (concrete x y z)
op3 symbolic _ x y z = symbolic x y z

-- | If a given binary op is commutative, then we always force Lits to the lhs if
-- only one argument is a Lit. This makes writing pattern matches in the
-- simplifier easier.
normArgs :: (Expr EWord -> Expr EWord -> Expr EWord) -> (W256 -> W256 -> W256) -> Expr EWord -> Expr EWord -> Expr EWord
normArgs sym conc l r = case (l, r) of
  (Lit _, _) -> doOp l r
  (_, Lit _) -> doOp r l
  _ -> doOp l r
  where
    doOp = op2 sym conc

-- Integers

add :: Expr EWord -> Expr EWord -> Expr EWord
add = normArgs Add (+)

sub :: Expr EWord -> Expr EWord -> Expr EWord
sub = op2 Sub (-)

mul :: Expr EWord -> Expr EWord -> Expr EWord
mul = normArgs Mul (*)

div :: Expr EWord -> Expr EWord -> Expr EWord
div = op2 Div (\x y -> if y == 0 then 0 else Prelude.div x y)

sdiv :: Expr EWord -> Expr EWord -> Expr EWord
sdiv = op2 SDiv (\x y -> let sx, sy :: Int256
                             sx = fromIntegral x
                             sy = fromIntegral y
                         in if y == 0 then 0 else fromIntegral (sx `quot` sy))

mod :: Expr EWord -> Expr EWord -> Expr EWord
mod = op2 Mod (\x y -> if y == 0 then 0 else x `Prelude.mod` y)

smod :: Expr EWord -> Expr EWord -> Expr EWord
smod = op2 SMod (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if y == 0
     then 0
     else fromIntegral (sx `rem` sy))

addmod :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
addmod = op3 AddMod (\x y z ->
  if z == 0
  then 0
  else fromIntegral $ (to512 x + to512 y) `Prelude.mod` to512 z)

mulmod :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
mulmod = op3 MulMod (\x y z ->
   if z == 0
   then 0
   else fromIntegral $ (to512 x * to512 y) `Prelude.mod` to512 z)

exp :: Expr EWord -> Expr EWord -> Expr EWord
exp = op2 Exp (^)

sex :: Expr EWord -> Expr EWord -> Expr EWord
sex = op2 SEx (\bytes x ->
  if bytes >= 32 then x
  else let n = unsafeInto bytes * 8 + 7 in
    if testBit x n
    then x .|. complement (bit n - 1)
    else x .&. (bit n - 1))

-- Booleans

lt :: Expr EWord -> Expr EWord -> Expr EWord
lt = op2 LT (\x y -> if x < y then 1 else 0)

gt :: Expr EWord -> Expr EWord -> Expr EWord
gt = op2 GT (\x y -> if x > y then 1 else 0)

leq :: Expr EWord -> Expr EWord -> Expr EWord
leq = op2 LEq (\x y -> if x <= y then 1 else 0)

geq :: Expr EWord -> Expr EWord -> Expr EWord
geq = op2 GEq (\x y -> if x >= y then 1 else 0)

slt :: Expr EWord -> Expr EWord -> Expr EWord
slt = op2 SLT (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if sx < sy then 1 else 0)

sgt :: Expr EWord -> Expr EWord -> Expr EWord
sgt = op2 SGT (\x y ->
  let sx, sy :: Int256
      sx = fromIntegral x
      sy = fromIntegral y
  in if sx > sy then 1 else 0)

eq :: Expr EWord -> Expr EWord -> Expr EWord
eq = normArgs Eq (\x y -> if x == y then 1 else 0)

iszero :: Expr EWord -> Expr EWord
iszero = op1 IsZero (\x -> if x == 0 then 1 else 0)

-- Bits

and :: Expr EWord -> Expr EWord -> Expr EWord
and = normArgs And (.&.)

or :: Expr EWord -> Expr EWord -> Expr EWord
or = normArgs Or (.|.)

xor :: Expr EWord -> Expr EWord -> Expr EWord
xor = normArgs Xor Data.Bits.xor

not :: Expr EWord -> Expr EWord
not = op1 Not complement

shl :: Expr EWord -> Expr EWord -> Expr EWord
shl = op2 SHL (\x y -> if x > 256 then 0 else shiftL y (fromIntegral x))

shr :: Expr EWord -> Expr EWord -> Expr EWord
shr = op2
  (\x y -> case (x, y) of
             -- simplify function selector checks
             (Lit 0xe0, ReadWord (Lit idx) buf)
               -> joinBytes (
                    replicate 28 (LitByte 0) <>
                      [ readByte (Lit idx) buf
                      , readByte (Lit $ idx + 1) buf
                      , readByte (Lit $ idx + 2) buf
                      , readByte (Lit $ idx + 3) buf])
             _ -> SHR x y)
  (\x y -> if x > 256 then 0 else shiftR y (fromIntegral x))

sar :: Expr EWord -> Expr EWord -> Expr EWord
sar = op2 SAR (\x y ->
  let msb = testBit y 255
      asSigned = fromIntegral y :: Int256
  in if x > 256 then
       if msb then maxBound else 0
     else
       fromIntegral $ shiftR asSigned (fromIntegral x))

-- ** Bufs ** --------------------------------------------------------------------------------------


-- | Extracts the byte at a given index from a Buf.
--
-- We do our best to return a concrete value wherever possible, but fallback to
-- an abstract expresion if nescessary. Note that a Buf is an infinite
-- structure, so reads outside of the bounds of a ConcreteBuf return 0. This is
-- inline with the semantics of calldata and memory, but not of returndata.

-- fuly concrete reads
readByte :: Expr EWord -> Expr Buf -> Expr Byte
readByte (Lit x) (ConcreteBuf b)
  = if x <= unsafeInto (maxBound :: Int) && i < BS.length b
    then LitByte (BS.index b i)
    else LitByte 0x0
  where
    i :: Int
    i = case x of
          (W256 (Word256 _ (Word128 _ x'))) -> unsafeInto x'

readByte i@(Lit x) (WriteByte (Lit idx) val src)
  = if x == idx
    then val
    else readByte i src
readByte i@(Lit x) (WriteWord (Lit idx) val src)
  = if x - idx < 32
    then case val of
           (Lit _) -> indexWord (Lit $ x - idx) val
           _ -> IndexWord (Lit $ x - idx) val
    else readByte i src
readByte i@(Lit x) (CopySlice (Lit srcOffset) (Lit dstOffset) (Lit size) src dst)
  = if x - dstOffset < size
    then readByte (Lit $ x - (dstOffset - srcOffset)) src
    else readByte i dst
readByte i@(Lit x) buf@(CopySlice _ (Lit dstOffset) (Lit size) _ dst)
  -- the byte we are trying to read is compeletely outside of the sliced region
  = if x - dstOffset >= size
    then readByte i dst
    else ReadByte (Lit x) buf

-- fully abstract reads
readByte i buf = ReadByte i buf


-- | Reads n bytes starting from idx in buf and returns a left padded word
--
-- If n is >= 32 this is the same as readWord
readBytes :: Int -> Expr EWord -> Expr Buf -> Expr EWord
readBytes (Prelude.min 32 -> n) idx buf
  = joinBytes [readByte (add idx (Lit . unsafeInto $ i)) buf | i <- [0 .. n - 1]]

-- | Reads the word starting at idx from the given buf
readWord :: Expr EWord -> Expr Buf -> Expr EWord
readWord idx b@(WriteWord idx' val buf)
  -- the word we are trying to read exactly matches a WriteWord
  | idx == idx' = val
  | otherwise = case (idx, idx') of
    (Lit i, Lit i') ->
      if i' - i >= 32 && i' - i <= (maxBound :: W256) - 31
      -- the region we are trying to read is completely outside of the WriteWord
      then readWord idx buf
      -- the region we are trying to read partially overlaps the WriteWord
      else readWordFromBytes idx b
    -- we do not have enough information to statically determine whether or not
    -- the region we want to read overlaps the WriteWord
    _ -> readWordFromBytes idx b
readWord (Lit idx) b@(CopySlice (Lit srcOff) (Lit dstOff) (Lit size) src dst)
  -- the region we are trying to read is enclosed in the sliced region
  | (idx - dstOff) < size && 32 <= size - (idx - dstOff) = readWord (Lit $ srcOff + (idx - dstOff)) src
  -- the region we are trying to read is compeletely outside of the sliced region
  | (idx - dstOff) >= size && (idx - dstOff) <= (maxBound :: W256) - 31 = readWord (Lit idx) dst
  -- the region we are trying to read partially overlaps the sliced region
  | otherwise = readWordFromBytes (Lit idx) b
readWord i b = readWordFromBytes i b

-- Attempts to read a concrete word from a buffer by reading 32 individual bytes and joining them together
-- returns an abstract ReadWord expression if a concrete word cannot be constructed
readWordFromBytes :: Expr EWord -> Expr Buf -> Expr EWord
readWordFromBytes (Lit idx) (ConcreteBuf bs) =
  case toInt idx of
    Nothing -> Lit 0
    Just i -> Lit $ word $ padRight 32 $ BS.take 32 $ BS.drop i bs
readWordFromBytes i@(Lit idx) buf = let
    bytes = [readByte (Lit i') buf | i' <- [idx .. idx + 31]]
  in if Prelude.and . (fmap isLitByte) $ bytes
     then Lit (bytesToW256 . mapMaybe maybeLitByte $ bytes)
     else ReadWord i buf
readWordFromBytes idx buf = ReadWord idx buf

{- | Copies a slice of src into dst.

        0           srcOffset       srcOffset + size     length src
        ┌--------------┬------------------┬-----------------┐
   src: |              | ------ sl ------ |                 |
        └--------------┴------------------┴-----------------┘

        0     dstOffset       dstOffset + size     length dst
        ┌--------┬------------------┬-----------------┐
   dst: |   hd   |                  |       tl        |
        └--------┴------------------┴-----------------┘
-}

-- The maximum number of bytes we will expand as part of simplification
--     this limits the amount of memory we will use while simplifying to ~1 GB / rewrite
--     note that things can still stack up, e.g. N such rewrites could eventually eat
--     N*1GB.
maxBytes :: W256
maxBytes = into (maxBound :: Word32) `Prelude.div` 8

copySlice :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr Buf

-- Copies from empty buffers
copySlice _ _ (Lit 0) (ConcreteBuf "") dst = dst
copySlice a b c@(Lit size) d@(ConcreteBuf "") e@(ConcreteBuf "")
  | size < maxBytes = ConcreteBuf $ BS.replicate (unsafeInto size) 0
  | otherwise = CopySlice a b c d e
copySlice srcOffset dstOffset sz@(Lit size) src@(ConcreteBuf "") dst
  | size < maxBytes = copySlice srcOffset dstOffset (Lit size) (ConcreteBuf $ BS.replicate (unsafeInto size) 0) dst
  | otherwise = CopySlice srcOffset dstOffset sz src dst

-- Fully concrete copies
copySlice a@(Lit srcOffset) b@(Lit dstOffset) c@(Lit size) d@(ConcreteBuf src) e@(ConcreteBuf "")
  | srcOffset > unsafeInto (BS.length src), size < maxBytes = ConcreteBuf $ BS.replicate (unsafeInto size) 0
  | srcOffset <= unsafeInto (BS.length src), dstOffset < maxBytes, size < maxBytes = let
    hd = BS.replicate (unsafeInto dstOffset) 0
    sl = padRight (unsafeInto size) $ BS.take (unsafeInto size) (BS.drop (unsafeInto srcOffset) src)
    in ConcreteBuf $ hd <> sl
  | otherwise = CopySlice a b c d e

copySlice a@(Lit srcOffset) b@(Lit dstOffset) c@(Lit size) d@(ConcreteBuf src) e@(ConcreteBuf dst)
  | dstOffset < maxBytes
  , size < maxBytes =
      let hd = padRight (unsafeInto dstOffset) $ BS.take (unsafeInto dstOffset) dst
          sl = if srcOffset > unsafeInto (BS.length src)
            then BS.replicate (unsafeInto size) 0
            else padRight (unsafeInto size) $ BS.take (unsafeInto size) (BS.drop (unsafeInto srcOffset) src)
          tl = BS.drop (unsafeInto dstOffset + unsafeInto size) dst
      in ConcreteBuf $ hd <> sl <> tl
  | otherwise = CopySlice a b c d e

-- copying 32 bytes can be rewritten to a WriteWord on dst (e.g. CODECOPY of args during constructors)
copySlice srcOffset dstOffset (Lit 32) src dst = writeWord dstOffset (readWord srcOffset src) dst

-- concrete indicies & abstract src (may produce a concrete result if we are
-- copying from a concrete region of src)
copySlice s@(Lit srcOffset) d@(Lit dstOffset) sz@(Lit size) src ds@(ConcreteBuf dst)
  | dstOffset < maxBytes, size < maxBytes, srcOffset + (size-1) > srcOffset = let
    hd = padRight (unsafeInto dstOffset) $ BS.take (unsafeInto dstOffset) dst
    sl = [readByte (Lit i) src | i <- [srcOffset .. srcOffset + (size - 1)]]
    tl = BS.drop (unsafeInto dstOffset + unsafeInto size) dst
    in if Prelude.and . (fmap isLitByte) $ sl
       then ConcreteBuf $ hd <> (BS.pack . (mapMaybe maybeLitByte) $ sl) <> tl
       else CopySlice s d sz src ds
  | otherwise = CopySlice s d sz src ds

-- abstract indicies
copySlice srcOffset dstOffset size src dst = CopySlice srcOffset dstOffset size src dst


writeByte :: Expr EWord -> Expr Byte -> Expr Buf -> Expr Buf
writeByte (Lit offset) (LitByte val) (ConcreteBuf "")
  | offset < maxBytes
  = ConcreteBuf $ BS.replicate (unsafeInto offset) 0 <> BS.singleton val
writeByte o@(Lit offset) b@(LitByte byte) buf@(ConcreteBuf src)
  | offset < maxBytes
    = ConcreteBuf $ (padRight (unsafeInto offset) $ BS.take (unsafeInto offset) src)
                 <> BS.pack [byte]
                 <> BS.drop (unsafeInto offset + 1) src
  | otherwise = WriteByte o b buf
writeByte offset byte src = WriteByte offset byte src


writeWord :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
writeWord o@(Lit offset) (WAddr (LitAddr val)) b@(ConcreteBuf _)
  | offset + 32 < maxBytes
  = writeWord o (Lit $ into val) b
writeWord (Lit offset) (Lit val) (ConcreteBuf "")
  | offset + 32 < maxBytes
  = ConcreteBuf $ BS.replicate (unsafeInto offset) 0 <> word256Bytes val
writeWord o@(Lit offset) v@(Lit val) buf@(ConcreteBuf src)
  | offset + 32 < maxBytes
    = ConcreteBuf $ (padRight (unsafeInto offset) $ BS.take (unsafeInto offset) src)
                 <> word256Bytes val
                 <> BS.drop ((unsafeInto offset) + 32) src
  | otherwise = WriteWord o v buf
writeWord idx val b@(WriteWord idx' val' buf)
  -- if the indices match exactly then we just replace the value in the current write and return
  | idx == idx' = WriteWord idx val buf
  | otherwise
    = case (idx, idx') of
        (Lit i, Lit i') -> if i >= i' + 32
                           -- if we can statically determine that the write at
                           -- idx doesn't overlap the write at idx', then we
                           -- push the write down we only consider writes where
                           -- i > i' to avoid infinite loops in this routine.
                           -- This also has the nice side effect of imposing a
                           -- canonical ordering on write chains, making exact
                           -- syntactic equalities between abstract terms more
                           -- likely to occur
                           then WriteWord idx' val' (writeWord idx val buf)
                           -- if we cannot statically determine freedom from
                           -- overlap, then we just return an abstract term
                           else WriteWord idx val b
        -- if we cannot determine statically that the write at idx' is out of
        -- bounds for idx, then we return an abstract term
        _ -> WriteWord idx val b
writeWord offset val src = WriteWord offset val src


-- | Returns the length of a given buffer
--
-- If there are any writes to abstract locations, or CopySlices with an
-- abstract size or dstOffset, an abstract expresion will be returned.
bufLength :: Expr Buf -> Expr EWord
bufLength = bufLengthEnv mempty False

bufLengthEnv :: Map.Map Int (Expr Buf) -> Bool -> Expr Buf -> Expr EWord
bufLengthEnv env useEnv buf = go (Lit 0) buf
  where
    go :: Expr EWord -> Expr Buf -> Expr EWord
    go l (ConcreteBuf b) = EVM.Expr.max l (Lit (unsafeInto . BS.length $ b))
    go l (AbstractBuf b) = Max l (BufLength (AbstractBuf b))
    go l (WriteWord idx _ b) = go (EVM.Expr.max l (add idx (Lit 32))) b
    go l (WriteByte idx _ b) = go (EVM.Expr.max l (add idx (Lit 1))) b
    go l (CopySlice _ dstOffset size _ dst) = go (EVM.Expr.max l (add dstOffset size)) dst

    go l (GVar (BufVar a)) | useEnv =
      case Map.lookup a env of
        Just b -> go l b
        Nothing -> internalError "cannot compute length of open expression"
    go l (GVar (BufVar a)) = EVM.Expr.max l (BufLength (GVar (BufVar a)))

-- | If a buffer has a concrete prefix, we return it's length here
concPrefix :: Expr Buf -> Maybe W256
concPrefix (WriteWord (Lit srcOff) _ (ConcreteBuf ""))
  | srcOff == 0 = Nothing
  | otherwise = Just srcOff
concPrefix (CopySlice (Lit srcOff) (Lit _) (Lit _) src (ConcreteBuf "")) = do
  sz <- go 0 src
  pure . into $ (unsafeInto sz) - srcOff
  where
    go :: W256 -> Expr Buf -> Maybe Integer
    -- base cases
    go _ (AbstractBuf _) = Nothing
    go l (ConcreteBuf b) = Just . into $ Prelude.max (unsafeInto . BS.length $ b) l

    -- writes to a concrete index
    go l (WriteWord (Lit idx) (Lit _) b) = go (Prelude.max l (idx + 32)) b
    go l (WriteByte (Lit idx) (LitByte _) b) = go (Prelude.max l (idx + 1)) b
    go l (CopySlice _ (Lit dstOffset) (Lit size) _ dst) = go (Prelude.max (dstOffset + size) l) dst

    -- writes to an abstract index are ignored
    go l (WriteWord _ _ b) = go l b
    go l (WriteByte _ _ b) = go l b
    go _ (CopySlice _ _ _ _ _) = internalError "cannot compute a concrete prefix length for nested copySlice expressions"
    go _ (GVar _) = internalError "cannot calculate a concrete prefix of an open expression"
concPrefix (ConcreteBuf b) = Just (unsafeInto . BS.length $ b)
concPrefix e = internalError $ "cannot compute a concrete prefix length for: " <> show e


-- | Return the minimum possible length of a buffer. In the case of an
-- abstract buffer, it is the largest write that is made on a concrete
-- location. Parameterized by an environment for buffer variables.
minLength :: Map.Map Int (Expr Buf) -> Expr Buf -> Maybe Integer
minLength bufEnv = go 0
  where
    go :: W256 -> Expr Buf -> Maybe Integer
    -- base cases
    go l (AbstractBuf _) = if l == 0 then Nothing else Just $ into l
    go l (ConcreteBuf b) = Just . into $ Prelude.max (unsafeInto . BS.length $ b) l
    -- writes to a concrete index
    go l (WriteWord (Lit idx) _ b) = go (Prelude.max l (idx + 32)) b
    go l (WriteByte (Lit idx) _ b) = go (Prelude.max l (idx + 1)) b
    go l (CopySlice _ (Lit dstOffset) (Lit size) _ dst) = go (Prelude.max (dstOffset + size) l) dst
    -- writes to an abstract index are ignored
    go l (WriteWord _ _ b) = go l b
    go l (WriteByte _ _ b) = go l b
    go l (CopySlice _ _ _ _ b) = go l b
    go l (GVar (BufVar a)) = do
      b <- Map.lookup a bufEnv
      go l b

word256At :: Expr EWord -> Lens (Expr Buf) (Expr Buf) (Expr EWord) (Expr EWord)
word256At i = lens getter setter where
  getter = readWord i
  setter m x = writeWord i x m

-- | Returns the first n bytes of buf
take :: W256 -> Expr Buf -> Expr Buf
take n = slice (Lit 0) (Lit n)


-- | Returns everything but the first n bytes of buf
drop :: W256 -> Expr Buf -> Expr Buf
drop n buf = slice (Lit n) (sub (bufLength buf) (Lit n)) buf

slice :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
slice offset size src = copySlice offset (Lit 0) size src mempty


toList :: Expr Buf -> Maybe (V.Vector (Expr Byte))
toList (AbstractBuf _) = Nothing
toList (ConcreteBuf bs) = Just $ V.fromList $ LitByte <$> BS.unpack bs
toList buf = case bufLength buf of
  Lit l -> if l <= unsafeInto (maxBound :: Int)
              then Just $ V.generate (unsafeInto l) (\i -> readByte (Lit $ unsafeInto i) buf)
              else internalError "overflow when converting buffer to list"
  _ -> Nothing

fromList :: V.Vector (Expr Byte) -> Expr Buf
fromList bs = case Prelude.and (fmap isLitByte bs) of
  True -> ConcreteBuf . BS.pack . V.toList . V.mapMaybe maybeLitByte $ bs
  -- we want to minimize the size of the resulting expresion, so we do two passes:
  --   1. write all concrete bytes to some base buffer
  --   2. write all symbolic writes on top of this buffer
  -- this is safe because each write in the input vec is to a single byte at a distinct location
  -- runs in O(2n) time, and has pretty minimal allocation & copy overhead in
  -- the concrete part (a single preallocated vec, with no copies)
  False -> V.ifoldl' applySymWrites (ConcreteBuf concreteBytes) bs
    where
      concreteBytes :: ByteString
      concreteBytes = vectorToByteString $ VS.generate (V.length bs) (\idx ->
        case bs V.! idx of
          LitByte b -> b
          _ -> 0)

      applySymWrites :: Expr Buf -> Int -> Expr Byte -> Expr Buf
      applySymWrites buf _ (LitByte _) = buf
      applySymWrites buf idx by = WriteByte (Lit $ unsafeInto idx) by buf

instance Semigroup (Expr Buf) where
  (ConcreteBuf a) <> (ConcreteBuf b) = ConcreteBuf $ a <> b
  a <> b = copySlice (Lit 0) (bufLength a) (bufLength b) b a

instance Monoid (Expr Buf) where
  mempty = ConcreteBuf ""

-- | Removes any irrelevant writes when reading from a buffer
simplifyReads :: Expr a -> Expr a
simplifyReads = \case
  ReadWord (Lit idx) b -> readWord (Lit idx) (stripWrites idx 32 b)
  ReadByte (Lit idx) b -> readByte (Lit idx) (stripWrites idx 1 b)
  a -> a

-- | Strips writes from the buffer that can be statically determined to be out of range
-- TODO: are the bounds here correct? I think there might be some off by one mistakes...
stripWrites :: W256 -> W256 -> Expr Buf -> Expr Buf
stripWrites off size = \case
  AbstractBuf s -> AbstractBuf s
  ConcreteBuf b -> ConcreteBuf $ case off <= off + size of
                                    True -> case tryFrom @W256 (off + size) of
                                      Right n -> BS.take n b
                                      Left _ -> b
                                    False -> b
  WriteByte (Lit idx) v prev
    -> if idx - off >= size
       then stripWrites off size prev
       else WriteByte (Lit idx) v (stripWrites off size prev)
  -- TODO: handle partial overlaps
  WriteWord (Lit idx) v prev
    -> if idx - off >= size && idx - off <= (maxBound :: W256) - 31
       then stripWrites off size prev
       else WriteWord (Lit idx) v (stripWrites off size prev)
  CopySlice (Lit srcOff) (Lit dstOff) (Lit size') src dst
    -> if dstOff - off >= size && dstOff - off <= (maxBound :: W256) - size' - 1
       then stripWrites off size dst
       else CopySlice (Lit srcOff) (Lit dstOff) (Lit size')
                      (stripWrites srcOff size' src)
                      (stripWrites off size dst)
  WriteByte i v prev -> WriteByte i v (stripWrites off size prev)
  WriteWord i v prev -> WriteWord i v (stripWrites off size prev)
  CopySlice srcOff dstOff size' src dst -> CopySlice srcOff dstOff size' src dst
  GVar _ ->  internalError "unexpected GVar in stripWrites"


-- ** Storage ** -----------------------------------------------------------------------------------


-- | Reads the word at the given slot from the given storage expression.
--
-- Note that we return a Nothing instead of a 0x0 if we are reading from a
-- store that is backed by a ConcreteStore or an EmptyStore and there have been
-- no explicit writes to the requested slot. This makes implementing rpc
-- storage lookups much easier. If the store is backed by an AbstractStore we
-- always return a symbolic value.
readStorage :: Expr EWord -> Expr Storage -> Maybe (Expr EWord)
readStorage slot s@(AbstractStore _) = Just $ SLoad slot s
readStorage (Lit l) (ConcreteStore s) = Lit <$> Map.lookup l s
readStorage slot store@(ConcreteStore _) = Just $ SLoad slot store
readStorage slot s@(SStore prevSlot val prev) = case (prevSlot, slot) of
  -- if address and slot match then we return the val in this write
  _ | prevSlot == slot -> Just val
  -- if the slots don't match (see previous guard) and are lits, we can skip this write
  (Lit _, Lit _) -> readStorage slot prev
  -- special case of map + map (different slot) -> skip write
  (Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) (WriteWord (Lit 0) _ (ConcreteBuf a)) (ConcreteBuf "")), Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) (WriteWord (Lit 0) _ (ConcreteBuf b)) (ConcreteBuf ""))) | dontMatchSlot a b -> readStorage slot prev
  -- special case of array + map -> skip write
  (Add (Keccak (ConcreteBuf a)) _, Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) _ (ConcreteBuf ""))) | BS.length a /= 0x40 -> readStorage slot prev
  (Keccak (ConcreteBuf a), Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) _ (ConcreteBuf ""))) | BS.length a /= 0x40 -> readStorage slot prev
  -- special case of array + map -> skip write
  (Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) _ (ConcreteBuf "")), Add (Keccak (ConcreteBuf a)) _) | BS.length a /= 64 -> readStorage slot prev
  (Keccak (CopySlice (Lit 0) (Lit 0) (Lit 0x40) _ (ConcreteBuf "")), Keccak (ConcreteBuf a)) | BS.length a /= 64 -> readStorage slot prev
  -- Fixed SMALL value will never match Keccak (well, it might, but that's VERY low chance)
  (Lit a, Keccak _) | a < 255 -> readStorage slot prev
  (Keccak _, Lit a) | a < 255 -> readStorage slot prev
  -- case of array + array, but different position
  (Keccak (ConcreteBuf a), Keccak (ConcreteBuf b)) | a /= b -> readStorage slot prev
  _ -> Just $ SLoad slot s

readStorage _ (GVar _) = internalError "Can't read from a GVar"

readStorage' :: Expr EWord -> Expr Storage -> Expr EWord
readStorage' loc store = case readStorage loc store of
                           Just v -> v
                           Nothing -> Lit 0

dontMatchSlot :: ByteString -> ByteString -> Bool
dontMatchSlot a b = BS.length a >= 64 && BS.length b >= 64 && diff32to64Byte a b
  where
    diff32to64Byte :: ByteString -> ByteString -> Bool
    diff32to64Byte x y = x32 /= y32
      where
       x32 = BS.take 32 $ BS.drop 32 x
       y32 = BS.take 32 $ BS.drop 32 y

slotPos :: Word8 -> ByteString
slotPos pos = BS.pack ((replicate 31 (0::Word8))++[pos])

makeKeccak :: Expr a -> Expr a
makeKeccak e = mapExpr go e
  where
    go :: Expr a -> Expr a
    go orig@(Lit key) = case litToArrayPreimage key of
      Just (array, offset) -> Add (Keccak (ConcreteBuf (slotPos array))) (Lit offset)
      _ -> orig
    go a = a

-- Takes in value, checks if it's within 256 of a pre-computed array hash value
-- if it is, it returns (array_number, offset)
litToArrayPreimage :: W256 -> Maybe (Word8, W256)
litToArrayPreimage val = go preImages
  where
    go :: [(W256, Word8)] -> Maybe (Word8, W256)
    go ((image, preimage):ax) = if val >= image && val-image <= 255 then Just (preimage, val-image)
                                                                    else go ax
    go [] = Nothing

-- | Writes a value to a key in a storage expression.
--
-- Concrete writes on top of a concrete or empty store will produce a new
-- ConcreteStore, otherwise we add a new write to the storage expression.
writeStorage :: Expr EWord -> Expr EWord -> Expr Storage -> Expr Storage
writeStorage k@(Lit key) v@(Lit val) store = case store of
  ConcreteStore s -> ConcreteStore (Map.insert key val s)
  _ -> SStore k v store
writeStorage key val store@(SStore key' val' prev)
     = if key == key'
       -- if we're overwriting an existing location, then drop the write
       then SStore key val prev
       else case (key, key') of
              -- if we can know statically that the new write doesn't overlap with the existing write, then we continue down the write chain
              -- we impose an ordering relation on the writes that we push down to ensure termination when this routine is called from the simplifier
              (Lit k, Lit k') -> if k > k'
                                 then SStore key' val' (writeStorage key val prev)
                                 else SStore key val store
              -- otherwise stack a new write on top of the the existing write chain
              _ -> SStore key val store
writeStorage key val store = SStore key val store


getAddr :: Expr Storage -> Maybe (Expr EAddr)
getAddr (SStore _ _ p) = getAddr p
getAddr (AbstractStore a) = Just a
getAddr (ConcreteStore _) = Nothing
getAddr (GVar _) = error "cannot determine addr of a GVar"


-- ** Whole Expression Simplification ** -----------------------------------------------------------


-- | Simple recursive match based AST simplification
-- Note: may not terminate!
simplify :: Expr a -> Expr a
simplify e = if (mapExpr go e == e)
               then e
               else makeKeccak $ simplify (mapExpr go e)
  where
    go :: Expr a -> Expr a
    -- redundant CopySlice
    go (CopySlice (Lit 0x0) (Lit 0x0) (Lit 0x0) _ dst) = dst

    -- simplify storage
    go (SLoad slot store) = readStorage' slot store
    go (SStore slot val store) = writeStorage slot val store

    -- simplify buffers
    go o@(ReadWord (Lit _) _) = simplifyReads o
    go (ReadWord idx buf) = readWord idx buf
    go o@(ReadByte (Lit _) _) = simplifyReads o
    go (ReadByte idx buf) = readByte idx buf

    -- We can zero out any bytes in a base ConcreteBuf that we know will be overwritten by a later write
    -- TODO: make this fully general for entire write chains, not just a single write.
    go o@(WriteWord (Lit idx) val (ConcreteBuf b))
      | idx < maxBytes
        = (writeWord (Lit idx) val (
            ConcreteBuf $
              (BS.take (unsafeInto idx) (padRight (unsafeInto idx) b))
              <> (BS.replicate 32 0)
              <> (BS.drop (unsafeInto idx + 32) b)))
      | otherwise = o
    go (WriteWord a b c) = writeWord a b c

    go (WriteByte a b c) = writeByte a b c
    go (CopySlice srcOff@(Lit 0) dstOff size@(Lit sz) (WriteWord (Lit 0) value (ConcreteBuf buf)) dst) = (CopySlice srcOff dstOff size (WriteWord (Lit 0) value (ConcreteBuf simplifiedBuf)) dst)
        where simplifiedBuf = BS.take (unsafeInto sz) buf
    go (CopySlice a b c d f) = copySlice a b c d f

    go (IndexWord a b) = indexWord a b

    -- LT
    go (EVM.Types.LT (Lit a) (Lit b))
      | a < b = Lit 1
      | otherwise = Lit 0
    go (EVM.Types.LT _ (Lit 0)) = Lit 0

    -- normalize all comparisons in terms of LT
    go (EVM.Types.GT a b) = EVM.Types.LT b a
    go (EVM.Types.GEq a b) = EVM.Types.LEq b a
    go (EVM.Types.LEq a b) = EVM.Types.IsZero (EVM.Types.GT a b)

    go (IsZero a) = iszero a

    -- syntactic Eq reduction
    go (Eq (Lit a) (Lit b))
      | a == b = Lit 1
      | otherwise = Lit 0
    go (Eq (Lit 0) (Sub a b)) = Eq a b
    go o@(Eq a b)
      | a == b = Lit 1
      | otherwise = o

    -- redundant ITE
    go (ITE (Lit x) a b)
      | x == 0 = b
      | otherwise = a

    -- address masking
    go (And (Lit 0xffffffffffffffffffffffffffffffffffffffff) a@(WAddr _)) = a

    -- literal addresses
    go (WAddr (LitAddr a)) = Lit $ into a

    -- simple div/mod/add/sub
    go (Div o1@(Lit _)  o2@(Lit _)) = EVM.Expr.div  o1 o2
    go (SDiv o1@(Lit _) o2@(Lit _)) = EVM.Expr.sdiv o1 o2
    go (Mod o1@(Lit _)  o2@(Lit _)) = EVM.Expr.mod  o1 o2
    go (SMod o1@(Lit _) o2@(Lit _)) = EVM.Expr.smod o1 o2
    go (Add o1@(Lit _)  o2@(Lit _)) = EVM.Expr.add  o1 o2
    go (Sub o1@(Lit _)  o2@(Lit _)) = EVM.Expr.sub  o1 o2

    -- double add/sub.
    -- Notice that everything is done mod 2**256. So for example:
    -- (a-b)+c observes the same arithmetic equalities as we are used to
    --         in infinite integers. In fact, it can be re-written as:
    -- (a+(W256Max-b)+c), which is the same as:
    -- (a+c+(W256Max-b)), which is the same as:
    -- (a+(c-b))
    -- In other words, subtraction is just adding a much larger number.
    --    So 3-1 mod 6 = 3+(6-1) mod 6 = 3+5 mod 6 = 5+3 mod 6 = 2
    go (Sub (Sub orig (Lit x)) (Lit y)) = Sub orig (Lit (y+x))
    go (Sub (Add orig (Lit x)) (Lit y)) = Sub orig (Lit (y-x))
    go (Add (Add orig (Lit x)) (Lit y)) = Add orig (Lit (y+x))
    go (Add (Sub orig (Lit x)) (Lit y)) = Add orig (Lit (y-x))

    -- redundant add / sub
    go o@(Sub (Add a b) c)
      | a == c = b
      | b == c = a
      | otherwise = o

    -- add / sub identities
    go o@(Add a b)
      | b == (Lit 0) = a
      | a == (Lit 0) = b
      | otherwise = o
    go o@(Sub a b)
      | a == b = Lit 0
      | b == (Lit 0) = a
      | otherwise = o

    -- SHL / SHR by 0
    go o@(SHL a v)
      | a == (Lit 0) = v
      | otherwise = o
    go o@(SHR a v)
      | a == (Lit 0) = v
      | otherwise = o

    -- doubled And
    go o@(And a (And b c))
      | a == c = (And a b)
      | a == b = (And b c)
      | otherwise = o

    -- Bitwise AND & OR. These MUST preserve bitwise equivalence
    go o@(And (Lit x) _)
      | x == 0 = Lit 0
      | otherwise = o
    go o@(And v (Lit x))
      | x == 0 = Lit 0
      | x == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff = v
      | otherwise = o
    go o@(Or (Lit x) b)
      | x == 0 = b
      | otherwise = o
    go o@(Or a (Lit x))
      | x == 0 = a
      | otherwise = o

    -- If x is ever non zero the Or will always evaluate to some non zero value and the false branch will be unreachable
    -- NOTE: with AND this does not work, because and(0x8, 0x4) = 0
    go (ITE (Or (Lit x) a) t f)
      | x == 0 = ITE a t f
      | otherwise = t
    go (ITE (Or a b@(Lit _)) t f) = ITE (Or b a) t f

    -- we write at least 32, so if x <= 32, it's FALSE
    go o@(EVM.Types.LT (BufLength (WriteWord {})) (Lit x))
      | x <= 32 = Lit 0
      | otherwise = o
    -- we write at least 32, so if x < 32, it's TRUE
    go o@(EVM.Types.LT (Lit x) (BufLength (WriteWord {})))
      | x < 32 = Lit 1
      | otherwise = o

    -- Double NOT is a no-op, since it's a bitwise inversion
    go (EVM.Types.Not (EVM.Types.Not a)) = a

    -- Some trivial min / max eliminations
    go (Max (Lit 0) a) = a
    go (Min (Lit 0) _) = Lit 0

    -- If a >= b then the value of the `Max` expression can never be < b
    go o@(LT (Max (Lit a) _) (Lit b))
      | a >= b = Lit 0
      | otherwise = o
    go o@(SLT (Sub (Max (Lit a) _) (Lit b)) (Lit c))
      = let sa, sb, sc :: Int256
            sa = fromIntegral a
            sb = fromIntegral b
            sc = fromIntegral c
        in if sa >= sb && sa - sb >= sc
           then Lit 0
           else o

    go a = a


-- ** Conversions ** -------------------------------------------------------------------------------


litAddr :: Addr -> Expr EWord
litAddr = Lit . into

exprToAddr :: Expr EWord -> Maybe Addr
exprToAddr (Lit x) = Just (unsafeInto x)
exprToAddr _ = Nothing

-- TODO: make this smarter, probably we will need to use the solver here?
wordToAddr :: Expr EWord -> Maybe (Expr EAddr)
wordToAddr = go . simplify
  where
    go :: Expr EWord -> Maybe (Expr EAddr)
    go = \case
      WAddr a -> Just a
      Lit a -> Just $ LitAddr (truncateToAddr a)
      _ -> Nothing

litCode :: BS.ByteString -> [Expr Byte]
litCode bs = fmap LitByte (BS.unpack bs)

to512 :: W256 -> Word512
to512 = fromIntegral


-- ** Helpers ** -----------------------------------------------------------------------------------


-- Is the given expr a literal byte?
isLitByte :: Expr Byte -> Bool
isLitByte (LitByte _) = True
isLitByte _ = False

-- Is the given expr a literal word?
isLitWord :: Expr EWord -> Bool
isLitWord (Lit _) = True
isLitWord (WAddr (LitAddr _)) = True
isLitWord _ = False

isSuccess :: Expr End -> Bool
isSuccess = \case
  Success {} -> True
  _ -> False

isFailure :: Expr End -> Bool
isFailure = \case
  Failure {} -> True
  _ -> False

isPartial :: Expr End -> Bool
isPartial = \case
  Partial {} -> True
  _ -> False

-- | Returns the byte at idx from the given word.
indexWord :: Expr EWord -> Expr EWord -> Expr Byte
-- Simplify masked reads:
--
--
--                reads across the mask boundry
--                return an abstract expression
--                            │
--                            │
--   reads outside of         │             reads over the mask read
--   the mask return 0        │             from the underlying word
--          │                 │                       │
--          │           ┌─────┘                       │
--          ▼           ▼                             ▼
--        ┌───┐       ┌─┬─┬─────────────────────────┬───┬──────────────┐
--        │   │       │ │ │                         │   │              │    mask
--        │   │       │ └─┼─────────────────────────┼───┼──────────────┘
--        │   │       │   │                         │   │
--    ┌───┼───┼───────┼───┼─────────────────────────┼───┼──────────────┐
--    │   │┼┼┼│       │┼┼┼│                         │┼┼┼│              │    w
--    └───┴───┴───────┴───┴─────────────────────────┴───┴──────────────┘
--   MSB                                                              LSB
--    ────────────────────────────────────────────────────────────────►
--    0                                                               31
--
--                    indexWord 0 reads from the MSB
--                    indexWord 31 reads from the LSB
--
indexWord i@(Lit idx) e@(And (Lit mask) w)
  -- if the mask is all 1s then read from the undelrying word
  -- we need this case to avoid overflow
  | mask == fullWordMask = indexWord (Lit idx) w
  -- if the index is a read from the masked region then read from the underlying word
  | idx <= 31
  , isPower2 (mask + 1)
  , isByteAligned mask
  , idx >= unmaskedBytes
    = indexWord (Lit idx) w
  -- if the read is outside of the masked region return 0
  | idx <= 31
  , isPower2 (mask + 1)
  , isByteAligned mask
  , idx < unmaskedBytes
    = LitByte 0
  -- if the mask is not a power of 2, or it does not align with a byte boundry return an abstract expression
  | idx <= 31 = IndexWord i e
  -- reads outside the range of the source word return 0
  | otherwise = LitByte 0
  where
    isPower2 n = n .&. (n-1) == 0
    fullWordMask = (2 ^ (256 :: W256)) - 1
    unmaskedBytes = fromIntegral $ (countLeadingZeros mask) `Prelude.div` 8
    isByteAligned m = (countLeadingZeros m) `Prelude.mod` 8 == 0
indexWord (Lit idx) (Lit w)
  | idx <= 31 = LitByte . fromIntegral $ shiftR w (248 - unsafeInto idx * 8)
  | otherwise = LitByte 0
indexWord (Lit idx) (JoinBytes zero        one        two       three
                               four        five       six       seven
                               eight       nine       ten       eleven
                               twelve      thirteen   fourteen  fifteen
                               sixteen     seventeen  eighteen  nineteen
                               twenty      twentyone  twentytwo twentythree
                               twentyfour  twentyfive twentysix twentyseven
                               twentyeight twentynine thirty    thirtyone)
  | idx == 0 = zero
  | idx == 1 = one
  | idx == 2 = two
  | idx == 3 = three
  | idx == 4 = four
  | idx == 5 = five
  | idx == 6 = six
  | idx == 7 = seven
  | idx == 8 = eight
  | idx == 9 = nine
  | idx == 10 = ten
  | idx == 11 = eleven
  | idx == 12 = twelve
  | idx == 13 = thirteen
  | idx == 14 = fourteen
  | idx == 15 = fifteen
  | idx == 16 = sixteen
  | idx == 17 = seventeen
  | idx == 18 = eighteen
  | idx == 19 = nineteen
  | idx == 20 = twenty
  | idx == 21 = twentyone
  | idx == 22 = twentytwo
  | idx == 23 = twentythree
  | idx == 24 = twentyfour
  | idx == 25 = twentyfive
  | idx == 26 = twentysix
  | idx == 27 = twentyseven
  | idx == 28 = twentyeight
  | idx == 29 = twentynine
  | idx == 30 = thirty
  | idx == 31 = thirtyone
  | otherwise = LitByte 0
indexWord idx w = IndexWord idx w


padByte :: Expr Byte -> Expr EWord
padByte (LitByte b) = Lit . bytesToW256 $ [b]
padByte b = joinBytes [b]

-- | Converts a list of bytes into a W256.
-- TODO: semantics if the input is too large?
bytesToW256 :: [Word8] -> W256
bytesToW256 = word . BS.pack

padBytesLeft :: Int -> [Expr Byte] -> [Expr Byte]
padBytesLeft n bs
  | length bs > n = Prelude.take n bs
  | length bs == n = bs
  | otherwise = padBytesLeft n (LitByte 0 : bs)

joinBytes :: [Expr Byte] -> Expr EWord
joinBytes bs
  | Prelude.and . (fmap isLitByte) $ bs = Lit . bytesToW256 . (mapMaybe maybeLitByte) $ bs
  | otherwise = let
      bytes = padBytesLeft 32 bs
    in JoinBytes
      (bytes !! 0)  (bytes !! 1)  (bytes !! 2)  (bytes !! 3)
      (bytes !! 4)  (bytes !! 5)  (bytes !! 6)  (bytes !! 7)
      (bytes !! 8)  (bytes !! 9)  (bytes !! 10) (bytes !! 11)
      (bytes !! 12) (bytes !! 13) (bytes !! 14) (bytes !! 15)
      (bytes !! 16) (bytes !! 17) (bytes !! 18) (bytes !! 19)
      (bytes !! 20) (bytes !! 21) (bytes !! 22) (bytes !! 23)
      (bytes !! 24) (bytes !! 25) (bytes !! 26) (bytes !! 27)
      (bytes !! 28) (bytes !! 29) (bytes !! 30) (bytes !! 31)

eqByte :: Expr Byte -> Expr Byte -> Expr EWord
eqByte (LitByte x) (LitByte y) = Lit $ if x == y then 1 else 0
eqByte x y = EqByte x y

min :: Expr EWord -> Expr EWord -> Expr EWord
min x y = normArgs Min Prelude.min x y

max :: Expr EWord -> Expr EWord -> Expr EWord
max x y = normArgs Max Prelude.max x y

numBranches :: Expr End -> Int
numBranches (ITE _ t f) = numBranches t + numBranches f
numBranches _ = 1

allLit :: [Expr Byte] -> Bool
allLit = Data.List.and . fmap (isLitByte)

-- | True if the given expression contains any node that satisfies the
-- input predicate
containsNode :: (forall a. Expr a -> Bool) -> Expr b -> Bool
containsNode p = getAny . foldExpr go (Any False)
  where
    go :: Expr a -> Any
    go node | p node  = Any True
    go _ = Any False

inRange :: Int -> Expr EWord -> Prop
inRange sz e = PAnd (PGEq e (Lit 0)) (PLEq e (Lit $ 2 ^ sz - 1))

-- | Evaluate the provided proposition down to its most concrete result
evalProp :: Prop -> Prop
evalProp prop =
  let new = mapProp' go prop
  in if (new == prop) then prop else evalProp new
  where
    go :: Prop -> Prop
    go (PLT (Lit l) (Lit r)) = PBool (l < r)
    go (PGT (Lit l) (Lit r)) = PBool (l > r)
    go (PGEq (Lit l) (Lit r)) = PBool (l >= r)
    go (PLEq (Lit l) (Lit r)) = PBool (l <= r)
    go (PNeg (PBool b)) = PBool (Prelude.not b)

    go (PAnd (PBool l) (PBool r)) = PBool (l && r)
    go (PAnd (PBool False) _) = PBool False
    go (PAnd _ (PBool False)) = PBool False

    go (POr (PBool l) (PBool r)) = PBool (l || r)
    go (POr (PBool True) _) = PBool True
    go (POr _ (PBool True)) = PBool True

    go (PImpl (PBool l) (PBool r)) = PBool ((Prelude.not l) || r)
    go (PImpl (PBool False) _) = PBool True

    go (PEq (Eq a b) (Lit 0)) = PNeg (PEq a b)
    go (PEq (Eq a b) (Lit 1)) = PEq a b

    go (PEq (Sub a b) (Lit 0)) = PEq a b

    go (PNeg (PNeg a)) = a

    go (PEq (Lit l) (Lit r)) = PBool (l == r)
    go o@(PEq l r)
      | l == r = PBool True
      | otherwise = o
    go p = p


-- Magic Constants

preImages :: [(W256, Word8)]
preImages = [ (0x290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563, 0)
            , (0xB10E2D527612073B26EECDFD717E6A320CF44B4AFAC2B0732D9FCBE2B7FA0CF6, 1)
            , (0x405787FA12A823E0F2B7631CC41B3BA8828B3321CA811111FA75CD3AA3BB5ACE, 2)
            , (0xC2575A0E9E593C00F959F8C92F12DB2869C3395A3B0502D05E2516446F71F85B, 3)
            , (0x8A35ACFBC15FF81A39AE7D344FD709F28E8600B4AA8C65C6B64BFE7FE36BD19B, 4)
            , (0x036B6384B5ECA791C62761152D0C79BB0604C104A5FB6F4EB0703F3154BB3DB0, 5)
            , (0xF652222313E28459528D920B65115C16C04F3EFC82AAEDC97BE59F3F377C0D3F, 6)
            , (0xA66CC928B5EDB82AF9BD49922954155AB7B0942694BEA4CE44661D9A8736C688, 7)
            , (0xF3F7A9FE364FAAB93B216DA50A3214154F22A0A2B415B23A84C8169E8B636EE3, 8)
            , (0x6E1540171B6C0C960B71A7020D9F60077F6AF931A8BBF590DA0223DACF75C7AF, 9)
            , (0xC65A7BB8D6351C1CF70C95A316CC6A92839C986682D98BC35F958F4883F9D2A8, 10)
            , (0x0175B7A638427703F0DBE7BB9BBF987A2551717B34E79F33B5B1008D1FA01DB9, 11)
            , (0xDF6966C971051C3D54EC59162606531493A51404A002842F56009D7E5CF4A8C7, 12)
            , (0xD7B6990105719101DABEB77144F2A3385C8033ACD3AF97E9423A695E81AD1EB5, 13)
            , (0xBB7B4A454DC3493923482F07822329ED19E8244EFF582CC204F8554C3620C3FD, 14)
            , (0x8D1108E10BCB7C27DDDFC02ED9D693A074039D026CF4EA4240B40F7D581AC802, 15)
            , (0x1B6847DC741A1B0CD08D278845F9D819D87B734759AFB55FE2DE5CB82A9AE672, 16)
            , (0x31ECC21A745E3968A04E9570E4425BC18FA8019C68028196B546D1669C200C68, 17)
            , (0xBB8A6A4669BA250D26CD7A459ECA9D215F8307E33AEBE50379BC5A3617EC3444, 18)
            , (0x66DE8FFDA797E3DE9C05E8FC57B3BF0EC28A930D40B0D285D93C06501CF6A090, 19)
            , (0xCE6D7B5282BD9A3661AE061FEED1DBDA4E52AB073B1F9285BE6E155D9C38D4EC, 20)
            , (0x55F448FDEA98C4D29EB340757EF0A66CD03DBB9538908A6A81D96026B71EC475, 21)
            , (0xD833147D7DC355BA459FC788F669E58CFAF9DC25DDCD0702E87D69C7B5124289, 22)
            , (0xC624B66CC0138B8FABC209247F72D758E1CF3343756D543BADBF24212BED8C15, 23)
            , (0xB13D2D76D1F4B7BE834882E410B3E3A8AFAF69F83600AE24DB354391D2378D2E, 24)
            , (0x944998273E477B495144FB8794C914197F3CCB46BE2900F4698FD0EF743C9695, 25)
            , (0x057C384A7D1C54F3A1B2E5E67B2617B8224FDFD1EA7234EEA573A6FF665FF63E, 26)
            , (0x3AD8AA4F87544323A9D1E5DD902F40C356527A7955687113DB5F9A85AD579DC1, 27)
            , (0x0E4562A10381DEC21B205ED72637E6B1B523BDD0E4D4D50AF5CD23DD4500A211, 28)
            , (0x6D4407E7BE21F808E6509AA9FA9143369579DD7D760FE20A2C09680FC146134F, 29)
            , (0x50BB669A95C7B50B7E8A6F09454034B2B14CF2B85C730DCA9A539CA82CB6E350, 30)
            , (0xA03837A25210EE280C2113FF4B77CA23440B19D4866CCA721C801278FD08D807, 31)
            , (0xC97BFAF2F8EE708C303A06D134F5ECD8389AE0432AF62DC132A24118292866BB, 32)
            , (0x3A6357012C1A3AE0A17D304C9920310382D968EBCC4B1771F41C6B304205B570, 33)
            , (0x61035B26E3E9EEE00E0D72FD1EE8DDCA6894550DCA6916EA2AC6BAA90D11E510, 34)
            , (0xD57B2B5166478FD4318D2ACC6CC2C704584312BDD8781B32D5D06ABDA57F4230, 35)
            , (0x7CD332D19B93BCABE3CCE7CA0C18A052F57E5FD03B4758A09F30F5DDC4B22EC4, 36)
            , (0x401968FF42A154441DA5F6C4C935AC46B8671F0E062BAAA62A7545BA53BB6E4C, 37)
            , (0x744A2CF8FD7008E3D53B67916E73460DF9FA5214E3EF23DD4259CA09493A3594, 38)
            , (0x98A476F1687BC3D60A2DA2ADBCBA2C46958E61FA2FB4042CD7BC5816A710195B, 39)
            , (0xE16DA923A2D88192E5070F37B4571D58682C0D66212EC634D495F33DE3F77AB5, 40)
            , (0xCB7C14CE178F56E2E8D86AB33EBC0AE081BA8556A00CD122038841867181CAAC, 41)
            , (0xBECED09521047D05B8960B7E7BCC1D1292CF3E4B2A6B63F48335CBDE5F7545D2, 42)
            , (0x11C44E4875B74D31FF9FD779BF2566AF7BD15B87FC985D01F5094B89E3669E4F, 43)
            , (0x7416C943B4A09859521022FD2E90EAC0DD9026DAD28FA317782A135F28A86091, 44)
            , (0x4A2CC91EE622DA3BC833A54C37FFCB6F3EC23B7793EFC5EAF5E71B7B406C5C06, 45)
            , (0x37FA166CBDBFBB1561CCD9EA985EC0218B5E68502E230525F544285B2BDF3D7E, 46)
            , (0xA813484AEF6FB598F9F753DAF162068FF39CCEA4075CB95E1A30F86995B5B7EE, 47)
            , (0x6FF97A59C90D62CC7236BA3A37CD85351BF564556780CF8C1157A220F31F0CBB, 48)
            , (0xC54045FA7C6EC765E825DF7F9E9BF9DEC12C5CEF146F93A5EEE56772EE647FBC, 49)
            , (0x11DF491316F14931039EDFD4F8964C9A443B862F02D4C7611D18C2BC4E6FF697, 50)
            , (0x82A75BDEEAE8604D839476AE9EFD8B0E15AA447E21BFD7F41283BB54E22C9A82, 51)
            , (0x46BDDB1178E94D7F2892FF5F366840EB658911794F2C3A44C450AA2C505186C1, 52)
            , (0xCFA4BEC1D3298408BB5AFCFCD9C430549C5B31F8AA5C5848151C0A55F473C34D, 53)
            , (0x4A11F94E20A93C79F6EC743A1954EC4FC2C08429AE2122118BF234B2185C81B8, 54)
            , (0x42A7B7DD785CD69714A189DFFB3FD7D7174EDC9ECE837694CE50F7078F7C31AE, 55)
            , (0x38395C5DCEADE9603479B177B68959049485DF8AA97B39F3533039AF5F456199, 56)
            , (0xDC16FEF70F8D5DDBC01EE3D903D1E69C18A3C7BE080EB86A81E0578814EE58D3, 57)
            , (0xA2999D817B6757290B50E8ECF3FA939673403DD35C97DE392FDB343B4015CE9E, 58)
            , (0xBBE3212124853F8B0084A66A2D057C2966E251E132AF3691DB153AB65F0D1A4D, 59)
            , (0xC6BB06CB7F92603DE181BF256CD16846B93B752A170FF24824098B31AA008A7E, 60)
            , (0xECE66CFDBD22E3F37D348A3D8E19074452862CD65FD4B9A11F0336D1AC6D1DC3, 61)
            , (0x8D800D6614D35EED73733EE453164A3B48076EB3138F466ADEEB9DEC7BB31F70, 62)
            , (0xC03004E3CE0784BF68186394306849F9B7B1200073105CD9AEB554A1802B58FD, 63)
            , (0x352FEEE0EEA125F11F791C1B77524172E9BC20F1B719B6CEF0FC24F64DB8E15E, 64)
            , (0x7C9785E8241615BC80415D89775984A1337D15DC1BF4CE50F41988B2A2B336A7, 65)
            , (0x38DFE4635B27BABECA8BE38D3B448CB5161A639B899A14825BA9C8D7892EB8C3, 66)
            , (0x9690AD99D6CE244EFA8A0F6C2D04036D3B33A9474DB32A71B71135C695102793, 67)
            , (0x9B22D3D61959B4D3528B1D8BA932C96FBE302B36A1AAD1D95CAB54F9E0A135EA, 68)
            , (0xA80A8FCC11760162F08BB091D2C9389D07F2B73D0E996161DFAC6F1043B5FC0B, 69)
            , (0x128667F541FED74A8429F9D592C26C2C6A4BEB9AE5EAD9912C98B2595C842310, 70)
            , (0xC43C1E24E1884C4E28A16BBD9506F60B5CA9F18FC90635E729D3CFE13ABCF001, 71)
            , (0x15040156076F78057C0A886F6DBAC29221FA3C2646ADBC8EFFEDAB98152FF32B, 72)
            , (0x37E472F504E93744DF80D87316862F9A8FD41A7BC266C723BF77DF7866D75F55, 73)
            , (0xFCC5BA1A98FC477B8948A04D08C6F4A76181FE75021370AB5E6ABD22B1792A2A, 74)
            , (0x17B0AF156A929EDF60C351F3DF2D53ED643FDD750AEF9EDA90DC7C8759A104A8, 75)
            , (0x42859D4F253F4D4A28EE9A59F9C9683A9404DA2C5D329C733AB84F150DB798A8, 76)
            , (0x1B524E1C8B5382BB913D0A2AAE8AD83BB92A45FCB47761FA4A12F5B6316C2B20, 77)
            , (0x9B65E484CE3D961A557081A44C6C68A0A27ECA0B88FCE820BDD99C3DC223DCC7, 78)
            , (0xA2E8F972DC9F7D0B76177BB8BE102E6BEC069EE42C61080745E8825470E80C6C, 79)
            , (0x5529612556959EF813DBE8D0ED29336AB75E80A9B7855030760B2917B01E568A, 80)
            , (0x994A4B4EDDB300691EE19901712848B1114BAD8A1A4AE195E5ABE0EC38021B94, 81)
            , (0xA9144A5E7EFD259B8B0D55467F4696ED47EC83317D61501B76366DBCCA65CE73, 82)
            , (0x4C83EFB3982AFBD500AB7C66D02B996DF5FDC3D20660E61600390AAD6D5F7F1E, 83)
            , (0xF0D642DBC7517672E217238A2F008F4F8CDAD0586D8CE5113E9E09DCC6860619, 84)
            , (0x71BEDA120AAFDD3BB922B360A066D10B7CE81D7AC2AD9874DAAC46E2282F6B45, 85)
            , (0xEA7419F5AE821E7204864E6A0871433BA612011908963BB42A64F42D65AD2F72, 86)
            , (0xE8E5595D268AAA85B36C3557E9D96C14A4FFFAEE9F45BCAE0C407968A7109630, 87)
            , (0x657000D47E971DCFB21375BCFA3496F47A2A2F0F12C8AEB78A008ACE6AE55CA5, 88)
            , (0xD73956B9E00D8F8BC5E44F7184DF1387CDD652E7726B8CCDA3DB4859E02F31BF, 89)
            , (0xE8C3ABD4193A84EC8A3FFF3EEB3ECBCBD0979E0C977AC1DEE06C6E01A60ACA1B, 90)
            , (0xFCEBC02DD307DC58CD01B156D63C6948B8F3422055FAC1D836349B01722E9C52, 91)
            , (0xEC0B854938343F85EB39A6648B9E449C2E4AEE4DC9B4E96AB592F9F497D05138, 92)
            , (0x2619EC68B255542E3DA68C054BFE0D7D0F27B7FDBEFC8BBCCDD23188FC71FE7F, 93)
            , (0x34D3C319F536DEB74ED8F1F3205D9AEFEF7487C819E77D3351630820DBFF1118, 94)
            , (0xCC7EE599E5D59FEE88C83157BD897847C5911DC7D317B3175E0B085198349973, 95)
            , (0x41C7AE758795765C6664A5D39BF63841C71FF191E9189522BAD8EBFF5D4ECA98, 96)
            , (0xF0ECB75DD1820844C57B6762233D4E26853B3A7B8157BBD9F41F280A0F1CEE9B, 97)
            , (0xB912C5EB6319A4A6A83580B9611610BEDB31614179330261BFD87A41347CAE1C, 98)
            , (0xD86D8A3F7C82C89ED8E04140017AA108A0A1469249F92C8F022B9DBAFA87B883, 99)
            , (0x26700E13983FEFBD9CF16DA2ED70FA5C6798AC55062A4803121A869731E308D2, 100)
            , (0x8FF97419363FFD7000167F130EF7168FBEA05FAF9251824CA5043F113CC6A7C7, 101)
            , (0x46501879B8CA8525E8C2FD519E2FBFCFA2EBEA26501294AA02CBFCFB12E94354, 102)
            , (0x9787EEB91FE3101235E4A76063C7023ECB40F923F97916639C598592FA30D6AE, 103)
            , (0xA2153420D844928B4421650203C77BABC8B33D7F2E7B450E2966DB0C22097753, 104)
            , (0x7FB4302E8E91F9110A6554C2C0A24601252C2A42C2220CA988EFCFE399914308, 105)
            , (0x116FEA137DB6E131133E7F2BAB296045D8F41CC5607279DB17B218CAB0929A51, 106)
            , (0xBD43CB8ECE8CD1863BCD6082D65C5B0D25665B1CE17980F0DA43C0ED545F98B4, 107)
            , (0x2B4A51AB505FC96A0952EFDA2BA61BCD3078D4C02C39A186EC16F21883FBE016, 108)
            , (0x5006B838207C6A9AE9B84D68F467DD4BB5C305FBFB6B04EAB8FAAABEEC1E18D8, 109)
            , (0x9930D9FF0DEE0EF5CA2F7710EA66B8F84DD0F5F5351ECFFE72B952CD9DB7142A, 110)
            , (0x39F2BABE526038520877FC7C33D81ACCF578AF4A06C5FA6B0D038CAE36E12711, 111)
            , (0x8F6B23FFA15F0465E3176E15CA644CF24F86DC1312FE715484E3C4AEAD5EB78B, 112)
            , (0xA1FCD19BFE8C32A61095B6BFBB2664842857E148FCBB5188386C8CD40348D5B6, 113)
            , (0xDFFBD64CC7C1A7EB27984335D9416D51137A03D3FABEC7141025C62663253FE1, 114)
            , (0xF79BDE9DDD17963EBCE6F7D021D60DE7C2BD0DB944D23C900C0C0E775F530052, 115)
            , (0x19A0B39AA25AC793B5F6E9A0534364CC0B3FD1EA9B651E79C7F50A59D48EF813, 116)
            , (0x9A8D93986A7B9E6294572EA6736696119C195C1A9F5EAE642D3C5FCD44E49DEA, 117)
            , (0xB5732705F5241370A28908C2FE1303CB223F03B90D857FD0573F003F79FEFED4, 118)
            , (0x7901CB5ADDCAE2D210A531C604A76A660D77039093BAC314DE0816A16392AFF1, 119)
            , (0x8DC6FB69531D98D70DC0420E638D2DFD04E09E1EC783EDE9AAC77DA9C5A0DAC4, 120)
            , (0x957BBDC7FAD0DEC56E7C96AF4A3AB63AA9DAF934A52FFCE891945B7FB622D791, 121)
            , (0xF0440771A29E57E18C66727944770B82CC77924AEF333C927CE6BDD2CDB3AE03, 122)
            , (0x5569044719A1EC3B04D0AFA9E7A5310C7C0473331D13DC9FAFE143B2C4E8148A, 123)
            , (0x9222CBF5D0DDC505A6F2F04716E22C226CEE16A955FEF88C618922096DAE2FD0, 124)
            , (0xA913C8AC5320DAE1C4A00FF23343947ED0FDF88D251E9BD2A5519D3D6162D222, 125)
            , (0x0F2ADA1F2DBAE48AE468FE0CDB7BCDA7D0CFFEE8545442E682273BA01A6203A7, 126)
            , (0x66925E85F1A4743FD8D60BA595ED74887B7CAF321DD83B21E04D77C115383408, 127)
            , (0x59F3FB058C6BBA7A4E76396639FC4DD21BD59163DB798899CF56CEF48B3C9EC9, 128)
            , (0x76FCE494794D92AC286B20D6126FC49ECB9CCA2FA94B5C726F6EC1109B891414, 129)
            , (0xB2244E644CFE16F72B654FBC48FF0FECEC8FC59649CA8625094BEBD9BD2E4035, 130)
            , (0x1397B88F412A83A7F1C0D834C533E486FF1F24F42A31819E91B624931060A863, 131)
            , (0x50250E93F8C73D2C1BE015EC28E8CD2FEB871EFA71E955AD24477AAFB09484FA, 132)
            , (0xDBDAEC72D84124D8C7C57AE448F5A4E3EEDB34DBA437FDCBE6D26496B68AFE87, 133)
            , (0x46B7EA84944250856A716737059479854246A026D947C13D5A0929BC8C1BC81D, 134)
            , (0x171AB08901BE24769DBEBEDBDF7E0245486FBC64AB975CD431A39533032D5415, 135)
            , (0x7EF464CF5A521D70C933977510816A0355B91A50ECA2778837FB82DA8448ECF6, 136)
            , (0x5BFA74C743914028161AE645D300D90BBDC659F169CA1469EC86B4960F7266CB, 137)
            , (0x834355D35CBFBD33B2397E201AF04B52BDD40B9B51275F279EA47E93547B631E, 138)
            , (0x7B6BB1E9D1B017FF82945596CF3CFB1A6CEE971C1EBB16F2C6BD23C2D642728E, 139)
            , (0x5F2F2DCA1D951C7429B52007F396328C64C25E226C1867318158F7F2CBDD40A9, 140)
            , (0x37A1BE2A88DADCD0E6062F54DDCC01A03360BA61CA7784A744E757488BF8CEB2, 141)
            , (0x8EDD81FF20324EA0CFE70C700FF4E9DB7580D269B423D9F61470B370819CBD17, 142)
            , (0x337F7913DB22D91EF425F82102BC8075EF67E23A2BE359965EA316E78E1EFF3F, 143)
            , (0x60B1E32550F9D5F25F9DD040E7A106B15D8EB282DD6B3E1914C73D8066896412, 144)
            , (0xCDAE184EDD6BF71C1FB62D6E6682FDB2032455C0E50143742135FBBE809BD793, 145)
            , (0x6E452848784197F00927D379E3DB9E69A5131D2269F862BFCD05A0B38F6ABF7F, 146)
            , (0x28DA5CA8143BFA5E9F642E58E5E87BEF0A2EB0C00BCD4EFDD01050293F5FAC91, 147)
            , (0x7047A3CC0A76EDCEE45792CA71527C753F6167484F14B94C4A3BD2997516725C, 148)
            , (0x947035E97D0F7E1937F791BC189F60C984CEAAA7A8494FC67F9F8F4DE8CCF2C6, 149)
            , (0x6AA7EC8AC2A999A90CE6C78668DFFE4E487E2576A97CA366EC81ECB335AF90D0, 150)
            , (0x354A83ED9988F79F6038D4C7A7DADBAD8AF32F4AD6DF893E0E5807A1B1944FF9, 151)
            , (0x2237A976FA961F5921FD19F2B03C925C725D77B20CE8F790C19709C03DE4D814, 152)
            , (0x72A152DDFB8E864297C917AF52EA6C1C68AEAD0FEE1A62673FCC7E0C94979D00, 153)
            , (0x44DA158BA27F9252712A74FF6A55C5D531F69609F1F6E7F17C4443A8E2089BE4, 154)
            , (0xBBA9DB4CDBEA0A37C207BBB83E20F828CD4441C49891101DC94FD20DC8EFC349, 155)
            , (0xAF85B9071DFAFEAC1409D3F1D19BAFC9BC7C37974CDE8DF0EE6168F0086E539C, 156)
            , (0xD26E832454299E9FABB89E0E5FFFDC046D4E14431BC1BF607FFB2E8A1DDECF7B, 157)
            , (0xCFE2A20FF701A1F3E14F63BD70D6C6BC6FBA8172EC6D5A505CDAB3927C0A9DE6, 158)
            , (0x0BC14066C33013FE88F66E314E4CF150B0B2D4D6451A1A51DBBD1C27CD11DE28, 159)
            , (0x78FDC8D422C49CED035A9EDF18D00D3C6A8D81DF210F3E5E448E045E77B41E88, 160)
            , (0xAADC37B8BA5645E62F4546802DB221593A94729CCBFC5A97D01365A88F649878, 161)
            , (0xAAF4F58DE99300CFADC4585755F376D5FA747D5BC561D5BD9D710DE1F91BF42D, 162)
            , (0x60859188CFFE297F44DDE29F2D2865634621F26215049CAEB304CCBA566A8B17, 163)
            , (0xE434DC35DA084CF8D7E8186688EA2DACB53DB7003D427AF3ABF351BD9D0A4E8D, 164)
            , (0xB29A2B3B6F2FF1B765777A231725941DA5072CC4FCC30AC4A2CE09706E8DDEFF, 165)
            , (0x2DA56674729343ACC9933752C8C469A244252915242EB6D4C02D11DDD69164A1, 166)
            , (0xB68792697ED876AF8B4858B316F5B54D81F6861191AD2950C1FDE6C3DC7B3DEA, 167)
            , (0xBEE89403B5BF0E626C2F71ADB366311C697013DF53107181A963ADC459EF4D99, 168)
            , (0xDC471888E6136F84C49E531E9C9240DC4E3FBA66DA9D3A49E2AF6202133683E0, 169)
            , (0x550D3DE95BE0BD28A79C3EB4EA7F05692C60B0602E48B49461E703379B08A71A, 170)
            , (0xFC377260A69A39DD786235C89F4BCD5D9639157731CAC38071A0508750EB115A, 171)
            , (0x0A0A1BCADD9F6A5539376FA82276E043AE3CB4499DAAAF8136572ECB1F9F0D60, 172)
            , (0x0440FD76B4E685D17019B0EEF836CEA9994650028B99DDDFB48BE06FA4240AA6, 173)
            , (0xDF5D400F265039450228FA547DF2BEE79E6A350DAA43FBA4BD328BC654824C64, 174)
            , (0xDEF993A65205231625280C5E3C23E44B263D0AA948FBC330055626B8AB25A5A1, 175)
            , (0x238BA8D02078544847438DB7773730A25D584074EAC94489BD8EB86CA267C937, 176)
            , (0x04CB44C80B6FBF8CEB1D80AF688C9F7C0B2AB5BF4A964CABE37041F23B23F7A8, 177)
            , (0xBBF265BEA1B905C854054A8DBE97FEDCC06FA54306551423711231A4AD0610C9, 178)
            , (0x236F2840BFC5DC34B28742DD0B4C9DEFE8A4A5FA9592E49CEFFB9AB51B7EB974, 179)
            , (0x1C5F5AC147EC2DEE04D8CE29BDBEBBC58F578E0E1392DA66F352A62E5C09C503, 180)
            , (0x22B88D74A6B23BE687AA96340C881253C2E9873C526EEC7366DC5F733ADA306A, 181)
            , (0x3AE797CEEF265E3A4F9C1978C47C759EB34A32909251DEE7276DB339B17B3DE3, 182)
            , (0x6A79CC294E25EB1A13381E9F3361EE96C47EE7ED00BF73ABADB8F9664BFFD0A7, 183)
            , (0xD91D691C894F8266E3F2D5E558AD2349D6783327A752A4949BC554F514E34988, 184)
            , (0xE35848A7C6477CFE9366AE64571069FD3A5AD752A460D28C5F73D438B5E432BF, 185)
            , (0xF3B9EB9E163AF2088B11DE0A369FB583F58F9440E0E5C70FCE0C59909ECECE8A, 186)
            , (0x28AFDD85196B637A3C64FF1F53AF1AD8DE145CF652297EDE1B38F2CBD6A4B4BF, 187)
            , (0x6F1F0041084F67CED174808484BD05851DE94443D775585E9D86D4C2589DBA59, 188)
            , (0xD344F074C815FDED543CD5A29A47659DE529CD0ADB1C1FAE6EDA2D685D422BD8, 189)
            , (0x4082D8AA0BE13AB143F55D600665A8AE7EF90BA09D57C38FA538A2604D7E9827, 190)
            , (0xB52CF138A3505DC3D3CD84A77912F4BE1A33DF2C3065D3E4CB37FB1D5D1B5072, 191)
            , (0x5E29E30C8EA9A89560281B90DBE96FE6F067A8ACC0F164A71449BF0DA7D58D7E, 192)
            , (0xA4C9B5D989FA12D608052E66DC5A37A431D679E93D0ED25572F97F67460BB157, 193)
            , (0xB93EDCD1E74716AC76D71E26CE3491BE20745375DCD4848D8F3B91A3F785DBB1, 194)
            , (0x6D918F650E2B4A9F360977C4447E6376EB632EC1F687BA963AA9983E90086594, 195)
            , (0x2BDE9B0C0857AEE2CFFDEA6B8723EAF59894499EC278C18F020EDD3C2295E424, 196)
            , (0xBACDDA17ED986C07F827229709E1DED99D4DA917A5E7E7EC15816EAF2CACF54C, 197)
            , (0xCFC479828D8133D824A47FE26326D458B6B94134276B945404197F42411564C3, 198)
            , (0xC1D0558604082AF4380F8AF6E6DF686F24C7438CA4F2A67C86A71EE7852601F9, 199)
            , (0xE71FAC6FB785942CC6C6404A423F94F32A28AE66D69FF41494C38BFD4788B2F8, 200)
            , (0x66BE4F155C5EF2EBD3772B228F2F00681E4ED5826CDB3B1943CC11AD15AD1D28, 201)
            , (0x42D72674974F694B5F5159593243114D38A5C39C89D6B62FEE061FF523240EE1, 202)
            , (0xA7CE836D032B2BF62B7E2097A8E0A6D8AEB35405AD15271E96D3B0188A1D06FB, 203)
            , (0x47197230E1E4B29FC0BD84D7D78966C0925452AFF72A2A121538B102457E9EBE, 204)
            , (0x83978B4C69C48DD978AB43FE30F077615294F938FB7F936D9EB340E51EA7DB2E, 205)
            , (0xD36CD1C74EF8D7326D8021B776C18FB5A5724B7F7BC93C2F42E43E10EF27D12A, 206)
            , (0xACB8D954E2CFEF495862221E91BD7523613CF8808827CB33EDFE4904CC51BF29, 207)
            , (0xE89D44C8FD6A9BAC8AF33CE47F56337617D449BF7FF3956B618C646DE829CBCB, 208)
            , (0x695FB3134AD82C3B8022BC5464EDD0BCC9424EF672B52245DCB6AB2374327CE3, 209)
            , (0xF2192E1030363415D7B4FB0406540A0060E8E2FC8982F3F32289379E11FA6546, 210)
            , (0x915C3EB987B20E1AF620C1403197BF687FB7F18513B3A73FDE6E78C7072C41A6, 211)
            , (0x9780E26D96B1F2A9A18EF8FC72D589DBF03EF788137B64F43897E83A91E7FEEC, 212)
            , (0x51858DE9989BF7441865EBDADBF7382C8838EDBF830F5D86A9A51AC773676DD6, 213)
            , (0xE767803F8ECF1DEE6BB0345811F7312CDA556058B19DB6389AD9AE3568643DDD, 214)
            , (0x8A012A6DE2943A5AA4D77ACF5E695D4456760A3F1F30A5D6DC2079599187A071, 215)
            , (0x5320AD99A619A90804CD2EFE3A5CF0AC1AC5C41AD9FF2C61CF699EFDAD771096, 216)
            , (0xCC6782FD46DD71C5F512301AB049782450B4EAF79FDAC5443D93D274D3916786, 217)
            , (0xB3D6E86317C38844915B053A0C35FF2FC103B684E96CEF2918AB06844EB51AAF, 218)
            , (0x4C0D3471EAD8EE99FBD8249E33F683E07C6CD6071FE102DD09617B2C353DE430, 219)
            , (0x3162B0988D4210BFF484413ED451D170A03887272177EFC0B7D000F10ABE9EDF, 220)
            , (0xAC507B9F8BF86AD8BB770F71CD2B1992902AE0314D93FC0F2BB011D70E796226, 221)
            , (0xFAE8130C0619F84B4B44F01B84806F04E82E536D70E05F2356977FA318AECC1A, 222)
            , (0x65E3D48FA860A761B461CE1274F0D562F3DB9A6A57CF04D8C90D68F5670B6AEA, 223)
            , (0x8B43726243EEAF8325404568ABECE3264B546CF9D88671F09C24C87045FCCB4F, 224)
            , (0x3EFDD7A884FF9E18C9E5711C185AA6C5E413B68F23197997DA5B1665CA978F99, 225)
            , (0x26A62D79192C78C3891F38189368673110B88734C09ED7453515DEF7525E07D8, 226)
            , (0x37F6A7F96B945F2F9A9127CCB4A8552FCB6938E53FE8F046DB8DA238398093E9, 227)
            , (0x04E4A0BB093261EE16386DADCEF9E2A83913F4E1899464891421D20C1BBFF74D, 228)
            , (0x5625F7C930B8B40DE87DC8E69145D83FD1D81C61B6C31FB7CFE69FAC65B28642, 229)
            , (0xD31DDB47B5E8664717D3718ACBD132396FF496FE337159C99410BE8658408A27, 230)
            , (0x6CB0DB1D7354DFB4A1464318006DF0643CAFE2002A86A29FF8560F900FEF28A1, 231)
            , (0x53C8DA29BFA275271DF3F270296D5A7D61B57F8848C89B3F65F49E21340B7592, 232)
            , (0xEA6426B4B8D70CAA8ECE9A88FB0A9D4A6B817BB4A43AC6FBEF64CB0E589129EE, 233)
            , (0x61C831BEAB28D67D1BB40B5AE1A11E2757FA842F031A2D0BC94A7867BC5D26C2, 234)
            , (0x0446C598F3355ED7D8A3B7E0B99F9299D15E956A97FAAE081A0B49D17024ABD2, 235)
            , (0xE7DFAC380F4A6ED3A03E62F813161EFF828766FA014393558E075E9CEB77D549, 236)
            , (0x0504E0A132D2EF5CA5F2FE74FC64437205BC10F32D5F13D533BF552916A94D3F, 237)
            , (0xDB444DA68C84F0A9CE08609100B69B8F3D5672687E0CA13FA3C0AC9EB2BDE5D2, 238)
            , (0xDD0DC620E7584674CB3DBA490D2EBA9E68ECA0BEF228EE569A4A64F6559056E9, 239)
            , (0x681483E2251CD5E2885507BB09F76BED3B99D3C377DD48396177647BFB4AAFDA, 240)
            , (0xC29B39917E4E60F0FEE5B6871B30A38E50531D76D1B0837811BD6351B34854EC, 241)
            , (0x83D76AFC3887C0B7EDD14A1AFFA7554BED3345BA68DDCD2A3326C7EAE97B80D8, 242)
            , (0x2F5553803273E8BB29D913CC31BAB953051C59F3BA57A71CF5591563CA721405, 243)
            , (0xFC6A672327474E1387FCBCE1814A1DE376D8561FC138561441AC6E396089E062, 244)
            , (0x81630654DFB0FD282A37117995646CDDE2CF8EEFE9F3F96FDB12CFDA88DF6668, 245)
            , (0xDDF78CFA378B5E068A248EDAF3ABEF23EA9E62C66F86F18CC5E695CD36C9809B, 246)
            , (0xE9944EBEF6E5A24035A31A727E8FF6DA7C372D99949C1224483B857F6401E346, 247)
            , (0x6120B123382F98F7EFE66ABE6A3A3445788A87E48D4E6991F37BAADCAC0BEF95, 248)
            , (0x168C8166292B85070409830617E84BDD7E3518B38E5AC430DC35ED7D16B07A86, 249)
            , (0xD84F57F3FFA76CC18982DA4353CC5991158EC5AE4F6A9109D1D7A0AE2CBA77ED, 250)
            , (0x3E7257B7272BB46D49CD6019B04DDEE20DA7C0CB13F7C1EC3391291B2CCEBABC, 251)
            , (0x371F36870D18F32A11FEA0F144B021C8B407BB50F8E0267C711123F454B963C0, 252)
            , (0x9346AC6DD7DE6B96975FEC380D4D994C4C12E6A8897544F22915316CC6CCA280, 253)
            , (0x54075DF80EC1AE6AC9100E1FD0EBF3246C17F5C933137AF392011F4C5F61513A, 254)
            , (0xE08EC2AF2CFC251225E1968FD6CA21E4044F129BFFA95BAC3503BE8BDB30A367, 255)
            ]
