{-# Language DataKinds #-}
{-# Language PatternGuards #-}

{-|
   Helper functions for working with Expr instances.
   All functions here will return a concrete result if given a concrete input.
-}
module EVM.Expr where

import Prelude hiding (LT, GT)
import Data.Bits
import Data.DoubleWord (Int256, Word256(Word256), Word128(Word128))
import Data.Word
import Data.Maybe
import Data.List

import Control.Lens (lens)

import EVM.Types
import EVM.Traversals
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V
import qualified Data.Vector.Storable as VS
import Data.Vector.Storable.ByteString


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
normArgs symop concop l r = case (l, r) of
  (Lit _, _) -> doOp l r
  (_, Lit _) -> doOp r l
  _ -> doOp l r
  where
    doOp = op2 symop concop

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
  else let n = num bytes * 8 + 7 in
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
sgt = op2 SLT (\x y ->
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
  let asSigned = (fromIntegral y) :: Int256
  in fromIntegral $ shiftR asSigned (fromIntegral x))

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
  = if x <= num (maxBound :: Int) && i < BS.length b
    then LitByte (BS.index b i)
    else LitByte 0x0
  where
    i :: Int
    i = case x of
          (W256 (Word256 _ (Word128 _ x'))) -> num x'

readByte i@(Lit x) (WriteByte (Lit idx) val src)
  = if x == idx
    then val
    else readByte i src
readByte i@(Lit x) (WriteWord (Lit idx) val src)
  = if idx <= x && x <= idx + 31
    then case val of
           (Lit _) -> indexWord (Lit $ x - idx) val
           _ -> IndexWord (Lit $ x - idx) val
    else readByte i src
readByte i@(Lit x) (CopySlice (Lit srcOffset) (Lit dstOffset) (Lit size) src dst)
  = if dstOffset <= num x && num x < (dstOffset + size)
    then readByte (Lit $ num x - (dstOffset - srcOffset)) src
    else readByte i dst

-- reads from partially symbolic copySlice exprs
readByte i@(Lit x) buf@(CopySlice _ (Lit dstOffset) (Lit size) _ dst)
  = if num x < dstOffset || dstOffset + size < num x
    then readByte i dst
    else ReadByte (Lit x) buf
readByte i@(Lit x) buf@(CopySlice _ (Lit dstOffset) _ _ dst)
  = if num x < dstOffset
    then readByte i dst
    else ReadByte (Lit x) buf

-- fully abstract reads
readByte i buf = ReadByte i buf


-- | Reads n bytes starting from idx in buf and returns a left padded word
--
-- If n is >= 32 this is the same as readWord
readBytes :: Int -> Expr EWord -> Expr Buf -> Expr EWord
readBytes (Prelude.min 32 -> n) idx buf
  = joinBytes [readByte (add idx (Lit . num $ i)) buf | i <- [0 .. n - 1]]

-- | Reads the word starting at idx from the given buf
readWord :: Expr EWord -> Expr Buf -> Expr EWord
readWord idx b@(WriteWord idx' val buf)
  -- the word we are trying to read exactly matches a WriteWord
  | idx == idx' = val
  | otherwise = case (idx, idx') of
    (Lit i, Lit i') ->
      if i >= i' + 32 || i + 32 <= i'
      -- the region we are trying to read is completely outside of the WriteWord
      then readWord idx buf
      -- the region we are trying to read partially overlaps the WriteWord
      else readWordFromBytes idx b
    -- we do not have enough information to statically determine whether or not
    -- the region we want to read overlaps the WriteWord
    _ -> readWordFromBytes idx b
readWord (Lit idx) b@(CopySlice (Lit srcOff) (Lit dstOff) (Lit size) src dst)
  -- the region we are trying to read is enclosed in the sliced region
  | idx >= dstOff && idx + 32 <= dstOff + size = readWord (Lit $ srcOff + (idx - dstOff)) src
  -- the region we are trying to read is compeletely outside of the sliced reegion
  | idx >= dstOff + size || idx + 32 <= dstOff = readWord (Lit idx) dst
  -- the region we are trying to read partially overlaps the sliced region
  | otherwise = readWordFromBytes (Lit idx) b
readWord i b = readWordFromBytes i b

-- Attempts to read a concrete word from a buffer by reading 32 individual bytes and joining them together
-- returns an abstract ReadWord expression if a concrete word cannot be constructed
readWordFromBytes :: Expr EWord -> Expr Buf -> Expr EWord
readWordFromBytes i@(Lit idx) buf = let
    bytes = [readByte (Lit i') buf | i' <- [idx .. idx + 31]]
  in if Prelude.and . (fmap isLitByte) $ bytes
     then Lit (bytesToW256 . mapMaybe unlitByte $ bytes)
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
copySlice :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr Buf

-- copies from empty bufs
copySlice _ _ (Lit 0) (ConcreteBuf "") dst = dst
copySlice _ _ (Lit size) (ConcreteBuf "") (ConcreteBuf "") =
  ConcreteBuf $ BS.replicate (num size) 0
copySlice srcOffset dstOffset (Lit size) (ConcreteBuf "") dst =
  copySlice srcOffset dstOffset (Lit size) (ConcreteBuf $ BS.replicate (num size) 0) dst -- TODO: ugly!

-- fully concrete copies
copySlice (Lit srcOffset) (Lit dstOffset) (Lit size) (ConcreteBuf src) (ConcreteBuf "")
  | srcOffset > num (BS.length src) = ConcreteBuf $ BS.replicate (num size) 0
  | otherwise = let
    hd = BS.replicate (num dstOffset) 0
    sl = padRight (num size) $ BS.take (num size) (BS.drop (num srcOffset) src)
  in ConcreteBuf $ hd <> sl
copySlice (Lit srcOffset) (Lit dstOffset) (Lit size) (ConcreteBuf src) (ConcreteBuf dst)
  = let hd = padRight (num dstOffset) $ BS.take (num dstOffset) dst
        sl = if srcOffset > num (BS.length src)
          then BS.replicate (num size) 0
          else padRight (num size) $ BS.take (num size) (BS.drop (num srcOffset) src)
        tl = BS.drop (num dstOffset + num size) dst
    in ConcreteBuf $ hd <> sl <> tl

-- copying 32 bytes can be rewritten to a WriteWord on dst (e.g. CODECOPY of args during constructors)
copySlice srcOffset dstOffset (Lit 32) src dst = writeWord dstOffset (readWord srcOffset src) dst

-- concrete indicies & abstract src (may produce a concrete result if we are
-- copying from a concrete region of src)
copySlice s@(Lit srcOffset) d@(Lit dstOffset) sz@(Lit size) src ds@(ConcreteBuf dst) = let
    hd = padRight (num dstOffset) $ BS.take (num dstOffset) dst
    sl = [readByte (Lit i) src | i <- [srcOffset .. srcOffset + (size - 1)]]
    tl = BS.drop (num dstOffset + num size) dst
  in if Prelude.and . (fmap isLitByte) $ sl
     then ConcreteBuf $ hd <> (BS.pack . (mapMaybe unlitByte) $ sl) <> tl
     else CopySlice s d sz src ds

-- abstract indicies
copySlice srcOffset dstOffset size src dst = CopySlice srcOffset dstOffset size src dst


writeByte :: Expr EWord -> Expr Byte -> Expr Buf -> Expr Buf
writeByte (Lit offset) (LitByte val) (ConcreteBuf "")
  = ConcreteBuf $ BS.replicate (num offset) 0 <> BS.singleton val
writeByte o@(Lit offset) b@(LitByte byte) buf@(ConcreteBuf src)
  | offset < num (maxBound :: Int)
    = ConcreteBuf $ (padRight (num offset) $ BS.take (num offset) src)
                 <> BS.pack [byte]
                 <> BS.drop (num offset + 1) src
  | otherwise = WriteByte o b buf
writeByte offset byte src = WriteByte offset byte src


writeWord :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
writeWord (Lit offset) (Lit val) (ConcreteBuf "")
  = ConcreteBuf $ BS.replicate (num offset) 0 <> word256Bytes val
writeWord o@(Lit offset) v@(Lit val) buf@(ConcreteBuf src)
  | offset + 32 < num (maxBound :: Int)
    = ConcreteBuf $ (padRight (num offset) $ BS.take (num offset) src)
                 <> word256Bytes val
                 <> BS.drop ((num offset) + 32) src
  | otherwise = WriteWord o v buf
writeWord offset val src = WriteWord offset val src


-- | Returns the length of a given buffer
--
-- If there are any writes to abstract locations, or CopySlices with an
-- abstract size or dstOffset, an abstract expresion will be returned.
bufLength :: Expr Buf -> Expr EWord
bufLength buf = case go 0 buf of
                  Just len -> len
                  Nothing -> BufLength buf
  where
    go :: W256 -> Expr Buf -> Maybe (Expr EWord)
    go l (ConcreteBuf b) = Just . Lit $ max (num . BS.length $ b) l
    go l (WriteWord (Lit idx) _ b) = go (max l (idx + 32)) b
    go l (WriteByte (Lit idx) _ b) = go (max l (idx + 1)) b
    go l (CopySlice _ (Lit dstOffset) (Lit size) _ dst) = go (max (dstOffset + size) l) dst
    go _ _ = Nothing

-- | If a buffer has a concrete prefix, we return it's length here
concPrefix :: Expr Buf -> Maybe Integer
concPrefix (CopySlice (Lit srcOff) (Lit _) (Lit _) src (ConcreteBuf "")) = do
  sz <- go 0 src
  pure . num $ (num sz) - srcOff
  where
    go :: W256 -> Expr Buf -> Maybe Integer
    -- base cases
    go _ (AbstractBuf _) = Nothing
    go l (ConcreteBuf b) = Just . num $ max (num . BS.length $ b) l

    -- writes to a concrete index
    go l (WriteWord (Lit idx) (Lit _) b) = go (max l (idx + 32)) b
    go l (WriteByte (Lit idx) (LitByte _) b) = go (max l (idx + 1)) b
    go l (CopySlice _ (Lit dstOffset) (Lit size) _ dst) = go (max (dstOffset + size) l) dst

    -- writes to an abstract index are ignored
    go l (WriteWord _ _ b) = go l b
    go l (WriteByte _ _ b) = go l b
    go l (CopySlice _ _ _ _ dst) = error "Internal Error: cannot compute a concrete prefix length for nested copySlice expressions"
    go _ (GVar _) = error "Internal error: cannot calculate minLength of an open expression"
concPrefix (ConcreteBuf b) = Just (num . BS.length $ b)
concPrefix e = error $ "Internal error: cannot compute a concrete prefix length for: " <> show e


word256At
  :: Functor f
  => Expr EWord -> (Expr EWord -> f (Expr EWord))
  -> Expr Buf -> f (Expr Buf)
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
  Lit l -> if l <= num (maxBound :: Int)
              then Just $ V.generate (num l) (\i -> readByte (Lit $ num i) buf)
              else error "Internal Error: overflow when converting buffer to list"
  _ -> Nothing

fromList :: V.Vector (Expr Byte) -> Expr Buf
fromList bs = case Prelude.and (fmap isLitByte bs) of
  True -> ConcreteBuf . BS.pack . V.toList . V.mapMaybe unlitByte $ bs
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
      applySymWrites buf idx by = WriteByte (Lit $ num idx) by buf

instance Semigroup (Expr Buf) where
  (ConcreteBuf a) <> (ConcreteBuf b) = ConcreteBuf $ a <> b
  a <> b = copySlice (Lit 0) (bufLength a) (bufLength b) b a

instance Monoid (Expr Buf) where
  mempty = ConcreteBuf ""

-- | Removes any irrelevant writes when reading from a buffer
simplifyReads :: Expr a -> Expr a
simplifyReads = \case
  ReadWord (Lit idx) b -> readWord (Lit idx) (stripWrites idx (idx + 31) b)
  ReadByte (Lit idx) b -> readByte (Lit idx) (stripWrites idx idx b)
  a -> a

-- | Strips writes from the buffer that can be statically determined to be out of range
-- TODO: are the bounds here correct? I think there might be some off by one mistakes...
stripWrites :: W256 -> W256 -> Expr Buf -> Expr Buf
stripWrites bottom top = \case
  AbstractBuf s -> AbstractBuf s
  ConcreteBuf b -> ConcreteBuf $ BS.take (num top+1) b
  WriteByte (Lit idx) v prev
    -> if idx < bottom || idx > top
       then stripWrites bottom top prev
       else WriteByte (Lit idx) v (stripWrites bottom top prev)
  -- TODO: handle partial overlaps
  WriteWord (Lit idx) v prev
    -> if idx + 31 < bottom || idx > top
       then stripWrites bottom top prev
       else WriteWord (Lit idx) v (stripWrites bottom top prev)
  CopySlice (Lit srcOff) (Lit dstOff) (Lit size) src dst
    -> if dstOff + size < bottom || dstOff > top
       then stripWrites bottom top dst
       else CopySlice (Lit srcOff) (Lit dstOff) (Lit size)
                      (stripWrites srcOff (srcOff + size) src)
                      (stripWrites bottom top dst)
  WriteByte i v prev -> WriteByte i v (stripWrites bottom top prev)
  WriteWord i v prev -> WriteWord i v (stripWrites bottom top prev)
  CopySlice srcOff dstOff size src dst -> CopySlice srcOff dstOff size src dst
  GVar _ ->  error "unexpected GVar in stripWrites"


-- ** Storage ** -----------------------------------------------------------------------------------


-- | Reads the word at the given slot from the given storage expression.
--
-- Note that we return a Nothing instead of a 0x0 if we are reading from a
-- store that is backed by a ConcreteStore or an EmptyStore and there have been
-- no explicit writes to the requested slot. This makes implementing rpc
-- storage lookups much easier. If the store is backed by an AbstractStore we
-- always return a symbolic value.
readStorage :: Expr EWord -> Expr EWord -> Expr Storage -> Maybe (Expr EWord)
readStorage _ _ EmptyStore = Nothing
readStorage addr slot store@(ConcreteStore s) = case (addr, slot) of
  (Lit a, Lit l) -> do
    ctrct <- Map.lookup a s
    val <- Map.lookup l ctrct
    pure $ Lit val
  _ -> Just $ SLoad addr slot store
readStorage addr' slot' s@AbstractStore = Just $ SLoad addr' slot' s
readStorage addr' slot' s@(SStore addr slot val prev) =
  if addr == addr'
  then if slot == slot'
       -- if address and slot match then we return the val in this write
       then Just val
       else case (slot, slot') of
              -- if the slots don't match and are lits, we can skip this write
              (Lit _, Lit _) -> readStorage addr' slot' prev
              -- if the slots don't match syntactically and are abstract then we can't skip this write
              _ -> Just $ SLoad addr' slot' s
  else case (addr, addr') of
    -- if the the addresses don't match and are lits, we can skip this write
    (Lit _, Lit _) -> readStorage addr' slot' prev
    -- if the the addresses don't match syntactically and are abstract then we can't skip this write
    _ -> Just $ SLoad addr' slot' s
readStorage _ _ (GVar _) = error "Can't read from a GVar"

readStorage' :: Expr EWord -> Expr EWord -> Expr Storage -> Expr EWord
readStorage' addr loc store = case readStorage addr loc store of
                                Just v -> v
                                Nothing -> Lit 0


-- | Writes a value to a key in a storage expression.
--
-- Concrete writes on top of a concrete or empty store will produce a new
-- ConcreteStore, otherwise we add a new write to the storage expression.
writeStorage :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Storage -> Expr Storage
writeStorage a@(Lit addr) k@(Lit key) v@(Lit val) store = case store of
  EmptyStore -> ConcreteStore (Map.singleton addr (Map.singleton key val))
  ConcreteStore s -> let
      ctrct = Map.findWithDefault Map.empty addr s
    in ConcreteStore (Map.insert addr (Map.insert key val ctrct) s)
  _ -> SStore a k v store
writeStorage addr key val store = SStore addr key val store


-- ** Whole Expression Simplification ** -----------------------------------------------------------


-- | Simple recursive match based AST simplification
-- Note: may not terminate!
simplify :: Expr a -> Expr a
simplify e = if (mapExpr go e == e)
               then e
               else simplify (mapExpr go e)
  where
    go :: Expr a -> Expr a
    -- redundant CopySlice
    go (CopySlice (Lit 0x0) (Lit 0x0) (Lit 0x0) _ dst) = dst

    -- simplify buffers
    go o@(ReadWord (Lit _) _) = simplifyReads o
    go (ReadWord idx buf) = readWord idx buf
    go o@(ReadByte (Lit _) _) = simplifyReads o
    go (ReadByte idx buf) = readByte idx buf
    go (WriteWord a b c) = writeWord a b c
    go (WriteByte a b c) = writeByte a b c
    go (CopySlice a b c d f) = copySlice a b c d f

    go (IndexWord a b) = indexWord a b

    -- concrete LT / GT
    go (EVM.Types.LT (Lit a) (Lit b))
      | a < b = Lit 1
      | otherwise = Lit 0
    go (EVM.Types.GT a b) = EVM.Types.LT b a
    go (EVM.Types.GEq a b) = EVM.Types.LEq b a
    go (EVM.Types.LEq a b) = EVM.Types.IsZero (EVM.Types.GT a b)

    -- syntactic Eq reduction
    go (Eq (Lit a) (Lit b))
      | a == b = Lit 1
      | otherwise = Lit 0
    go o@(Eq a b)
      | a == b = Lit 1
      | otherwise = o

    -- redundant ITE
    go (ITE (Lit x) a b)
      | x == 0 = b
      | otherwise = a

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
    go o@(And _ (Lit x))
      | x == 0 = Lit 0
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

    go a = a


-- ** Conversions ** -------------------------------------------------------------------------------


litAddr :: Addr -> Expr EWord
litAddr = Lit . num

litCode :: BS.ByteString -> [Expr Byte]
litCode bs = fmap LitByte (BS.unpack bs)

to512 :: W256 -> Word512
to512 = fromIntegral


-- ** Helpers ** -----------------------------------------------------------------------------------


-- Is the given expr a literal word?
isLitByte :: Expr Byte -> Bool
isLitByte (LitByte _) = True
isLitByte _ = False

isPower2 :: W256 -> Bool
isPower2 n = n .&. (n-1) == 0

-- | Returns the byte at idx from the given word.
indexWord :: Expr EWord -> Expr EWord -> Expr Byte
indexWord (Lit idx) (And (Lit mask) w)
  | mask == (2 ^ (256 :: W256)) - 1 = indexWord (Lit idx) w -- we need this case here to avoid overflow below
  | isPower2 (mask + 1), 2 ^ (idx + 1) <= mask = indexWord (Lit idx) w
  | isPower2 (mask + 1), 2 ^ (idx + 1) > mask = LitByte 0
  | otherwise = IndexWord (Lit idx) (And (Lit mask) w)
indexWord (Lit idx) (Lit w)
  | idx <= 31 = LitByte . fromIntegral $ shiftR w (248 - num idx * 8)
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
  | Prelude.and . (fmap isLitByte) $ bs = Lit . bytesToW256 . (mapMaybe unlitByte) $ bs
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
min (Lit x) (Lit y) = if x < y then Lit x else Lit y
min x y = Min x y

numBranches :: Expr End -> Int
numBranches (ITE _ t f) = numBranches t + numBranches f
numBranches _ = 1

allLit :: [Expr Byte] -> Bool
allLit = Data.List.and . fmap (isLitByte)
