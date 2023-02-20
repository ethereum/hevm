{-# Language CPP #-}
{-# Language TemplateHaskell #-}
{-# Language TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DefaultSignatures #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module EVM.Types where

import Prelude hiding  (Word, LT, GT)

import Data.Aeson
import Crypto.Hash hiding (SHA256)
import Data.Map (Map)
import Data.Bifunctor (first)
import Data.Char
import Data.List (isPrefixOf, foldl')
import Data.ByteString (ByteString)
import Data.ByteString.Base16 as BS16
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Lazy (toStrict)
import qualified Data.ByteString.Char8  as Char8
import Data.Word (Word8, Word32, Word64)
import Data.Bits (Bits, FiniteBits, shiftR, shift, shiftL, (.&.), (.|.))
import Data.DoubleWord
import Data.DoubleWord.TH
import Data.Maybe (fromMaybe)
import Numeric (readHex, showHex)
import Options.Generic
import EVM.Hexdump (paddedShowHex)
import Control.Arrow ((>>>))
import Control.Monad

import qualified Data.ByteArray       as BA
import qualified Data.Aeson           as JSON
import qualified Data.Aeson.Types     as JSON
import qualified Data.ByteString      as BS
import qualified Data.Serialize.Get   as Cereal
import qualified Data.Text            as Text
import qualified Data.Text.Encoding   as Text
import qualified Data.Sequence        as Seq
import qualified Text.Regex.TDFA      as Regex
import qualified Text.Read

-- Some stuff for "generic programming", needed to create Word512
import Data.Data
import qualified Data.Vector as V

-- We need a 512-bit word for doing ADDMOD and MULMOD with full precision.
mkUnpackedDoubleWord "Word512" ''Word256 "Int512" ''Int256 ''Word256
  [''Typeable, ''Data, ''Generic]


newtype W256 = W256 Word256
  deriving
    ( Num, Integral, Real, Ord, Generic
    , Bits , FiniteBits, Enum, Eq , Bounded
    )

{- |
  Expr implements an abstract respresentation of an EVM program

  This type can give insight into the provenance of a term which is useful,
  both for the aesthetic purpose of printing terms in a richer way, but also to
  allow optimizations on the AST instead of letting the SMT solver do all the
  heavy lifting.

  Memory, calldata, and returndata are all represented as a Buf. Semantically
  speaking a Buf is a byte array with of size 2^256.

  Bufs have two base constructors:
    - AbstractBuf:    all elements are fully abstract values
    - ConcreteBuf bs: all elements past (length bs) are zero

  Bufs can be read from with:
    - ReadByte idx buf: read the byte at idx from buf
    - ReadWord idx buf: read the byte at idx from buf

  Bufs can be written to with:
    - WriteByte idx val buf: write val to idx in buf
    - WriteWord idx val buf: write val to idx in buf
    - CopySlice srcOffset dstOffset size src dst:
        overwrite dstOffset -> dstOffset + size in dst with srcOffset -> srcOffset + size from src

  Note that the shared usage of `Buf` does allow for the construction of some
  badly typed Expr instances (e.g. an MSTORE on top of the contents of calldata
  instead of some previous instance of memory), we accept this for the
  sake of simplifying pattern matches against a Buf expression.

  Storage expressions are similar, but instead of writing regions of bytes, we
  write a word to a particular key in a given addresses storage. Note that as
  with a Buf, writes can be sequenced on top of concrete, empty and fully
  abstract starting states.

  One important principle is that of local context: e.g. each term representing
  a write to a Buf / Storage / Logs will always contain a copy of the state
  that is being added to, this ensures that all context relevant to a given
  operation is contained within the term that represents that operation.

  When dealing with Expr instances we assume that concrete expressions have
  been reduced to their smallest possible representation (i.e. a `Lit`,
  `ConcreteBuf`, or `ConcreteStore`). Failure to adhere to this invariant will
  result in your concrete term being treated as symbolic, and may produce
  unexpected errors. In the future we may wish to consider encoding the
  concreteness of a given term directly in the type of that term, since such
  type level shenanigans tends to complicate implementation, we skip this for
  now.
-}

-- phantom type tags for AST construction
data EType
  = Buf
  | Storage
  | Log
  | EWord
  | Byte
  | End
  deriving (Typeable)

-- Failure states of the Expr AST
data ExprError
  = UnrecognizedOpcode
  | IllegalOverflow
  | StackLimitExceeded
  | InvalidMemoryAccess
  | BadJumpDestination
  | StackUnderrun
  | SelfDestruct
  | WrappedEVMError String
  deriving (Show, Eq, Ord)

-- Variables refering to a global environment
data GVar (a :: EType) where
  BufVar :: Int -> GVar Buf
  StoreVar :: Int -> GVar Storage

deriving instance Show (GVar a)
deriving instance Eq (GVar a)
deriving instance Ord (GVar a)


-- add type level list of constraints
data Expr (a :: EType) where

  -- identifiers

  Lit            :: W256 -> Expr EWord
  Var            :: Text -> Expr EWord
  GVar           :: GVar a -> Expr a

  -- bytes

  LitByte        :: Word8      -> Expr Byte
  IndexWord      :: Expr EWord -> Expr EWord -> Expr Byte
  EqByte         :: Expr Byte  -> Expr Byte  -> Expr EWord

  -- TODO: rm readWord in favour of this?
  JoinBytes      :: Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr Byte -> Expr Byte -> Expr Byte -> Expr Byte
                 -> Expr EWord
  -- control flow

  Revert              :: [Prop] -> Expr Buf -> Expr End
  Failure             :: [Prop] -> ExprError -> Expr End
  Return              :: [Prop] -> Expr Buf -> Expr Storage -> Expr End
  ITE                 :: Expr EWord -> Expr End -> Expr End -> Expr End

  -- integers

  Add            :: Expr EWord -> Expr EWord -> Expr EWord
  Sub            :: Expr EWord -> Expr EWord -> Expr EWord
  Mul            :: Expr EWord -> Expr EWord -> Expr EWord
  Div            :: Expr EWord -> Expr EWord -> Expr EWord
  SDiv           :: Expr EWord -> Expr EWord -> Expr EWord
  Mod            :: Expr EWord -> Expr EWord -> Expr EWord
  SMod           :: Expr EWord -> Expr EWord -> Expr EWord
  AddMod         :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
  MulMod         :: Expr EWord -> Expr EWord -> Expr EWord -> Expr EWord
  Exp            :: Expr EWord -> Expr EWord -> Expr EWord
  SEx            :: Expr EWord -> Expr EWord -> Expr EWord
  Min            :: Expr EWord -> Expr EWord -> Expr EWord

  -- booleans

  LT             :: Expr EWord -> Expr EWord -> Expr EWord
  GT             :: Expr EWord -> Expr EWord -> Expr EWord
  LEq            :: Expr EWord -> Expr EWord -> Expr EWord
  GEq            :: Expr EWord -> Expr EWord -> Expr EWord
  SLT            :: Expr EWord -> Expr EWord -> Expr EWord
  SGT            :: Expr EWord -> Expr EWord -> Expr EWord
  Eq             :: Expr EWord -> Expr EWord -> Expr EWord
  IsZero         :: Expr EWord -> Expr EWord

  -- bits

  And            :: Expr EWord -> Expr EWord -> Expr EWord
  Or             :: Expr EWord -> Expr EWord -> Expr EWord
  Xor            :: Expr EWord -> Expr EWord -> Expr EWord
  Not            :: Expr EWord -> Expr EWord
  SHL            :: Expr EWord -> Expr EWord -> Expr EWord
  SHR            :: Expr EWord -> Expr EWord -> Expr EWord
  SAR            :: Expr EWord -> Expr EWord -> Expr EWord

  -- Hashes

  Keccak         :: Expr Buf -> Expr EWord
  SHA256         :: Expr Buf -> Expr EWord

  -- block context

  Origin         :: Expr EWord
  BlockHash      :: Expr EWord -> Expr EWord
  Coinbase       :: Expr EWord
  Timestamp      :: Expr EWord
  BlockNumber    :: Expr EWord
  PrevRandao     :: Expr EWord
  GasLimit       :: Expr EWord
  ChainId        :: Expr EWord
  BaseFee        :: Expr EWord

  -- frame context

  CallValue      :: Int                -- frame idx
                 -> Expr EWord

  Caller         :: Int                -- frame idx
                 -> Expr EWord

  Address        :: Int                -- frame idx
                 -> Expr EWord

  Balance        :: Int                -- frame idx
                 -> Int                -- PC (in case we're checking the current contract)
                 -> Expr EWord         -- address
                 -> Expr EWord

  SelfBalance    :: Int                -- frame idx
                 -> Int                -- PC
                 -> Expr EWord

  Gas            :: Int                -- frame idx
                 -> Int                -- PC
                 -> Expr EWord

  -- code

  CodeSize       :: Expr EWord         -- address
                 -> Expr EWord         -- size

  ExtCodeHash    :: Expr EWord         -- address
                 -> Expr EWord         -- size

  -- logs

  LogEntry       :: Expr EWord         -- address
                 -> Expr Buf           -- data
                 -> [Expr EWord]       -- topics
                 -> Expr Log

  -- Contract Creation

  Create         :: Expr EWord         -- value
                 -> Expr EWord         -- offset
                 -> Expr EWord         -- size
                 -> Expr Buf           -- memory
                 -> [Expr Log]          -- logs
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- address

  Create2        :: Expr EWord         -- value
                 -> Expr EWord         -- offset
                 -> Expr EWord         -- size
                 -> Expr EWord         -- salt
                 -> Expr Buf           -- memory
                 -> [Expr Log]          -- logs
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- address

  -- Calls

  Call           :: Expr EWord         -- gas
                 -> Maybe (Expr EWord) -- target
                 -> Expr EWord         -- value
                 -> Expr EWord         -- args offset
                 -> Expr EWord         -- args size
                 -> Expr EWord         -- ret offset
                 -> Expr EWord         -- ret size
                 -> [Expr Log]          -- logs
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- success

  CallCode       :: Expr EWord         -- gas
                 -> Expr EWord         -- address
                 -> Expr EWord         -- value
                 -> Expr EWord         -- args offset
                 -> Expr EWord         -- args size
                 -> Expr EWord         -- ret offset
                 -> Expr EWord         -- ret size
                 -> [Expr Log]         -- logs
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- success

  DelegeateCall  :: Expr EWord         -- gas
                 -> Expr EWord         -- address
                 -> Expr EWord         -- value
                 -> Expr EWord         -- args offset
                 -> Expr EWord         -- args size
                 -> Expr EWord         -- ret offset
                 -> Expr EWord         -- ret size
                 -> [Expr Log]         -- logs
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- success

  -- storage

  EmptyStore     :: Expr Storage
  ConcreteStore  :: Map W256 (Map W256 W256) -> Expr Storage
  AbstractStore  :: Expr Storage

  SLoad          :: Expr EWord         -- address
                 -> Expr EWord         -- index
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- result

  SStore         :: Expr EWord         -- address
                 -> Expr EWord         -- index
                 -> Expr EWord         -- value
                 -> Expr Storage       -- old storage
                 -> Expr Storage       -- new storae

  -- buffers

  ConcreteBuf    :: ByteString -> Expr Buf
  AbstractBuf    :: Text -> Expr Buf

  ReadWord       :: Expr EWord         -- index
                 -> Expr Buf           -- src
                 -> Expr EWord

  ReadByte       :: Expr EWord         -- index
                 -> Expr Buf           -- src
                 -> Expr Byte

  WriteWord      :: Expr EWord         -- dst offset
                 -> Expr EWord         -- value
                 -> Expr Buf           -- prev
                 -> Expr Buf

  WriteByte      :: Expr EWord         -- dst offset
                 -> Expr Byte          -- value
                 -> Expr Buf           -- prev
                 -> Expr Buf

  CopySlice      :: Expr EWord         -- src offset
                 -> Expr EWord         -- dst offset
                 -> Expr EWord         -- size
                 -> Expr Buf           -- src
                 -> Expr Buf           -- dst
                 -> Expr Buf

  BufLength      :: Expr Buf -> Expr EWord

deriving instance Show (Expr a)
deriving instance Eq (Expr a)
deriving instance Ord (Expr a)

-- The language of assertable expressions.
-- This is useful when generating SMT queries based on Expr instances, since
-- the translation of Eq and other boolean operators from Expr to SMT is an
-- (ite (eq a b) 1 0). We can use the boolean operators here to remove some
-- unescessary `ite` statements from our SMT encoding.
data Prop where
  PEq :: forall a . Typeable a => Expr a -> Expr a -> Prop
  PLT :: Expr EWord -> Expr EWord -> Prop
  PGT :: Expr EWord -> Expr EWord -> Prop
  PGEq :: Expr EWord -> Expr EWord -> Prop
  PLEq :: Expr EWord -> Expr EWord -> Prop
  PNeg :: Prop -> Prop
  PAnd :: Prop -> Prop -> Prop
  POr :: Prop -> Prop -> Prop
  PBool :: Bool -> Prop
deriving instance (Show Prop)

infixr 3 .&&
(.&&) :: Prop -> Prop -> Prop
x .&& y = PAnd x y

infixr 2 .||
(.||) :: Prop -> Prop -> Prop
x .|| y = POr x y

infix 4 .<, .<=, .>, .>=
(.<) :: Expr EWord -> Expr EWord -> Prop
x .< y = PLT x y
(.<=) :: Expr EWord -> Expr EWord -> Prop
x .<= y = PLEq x y
(.>) :: Expr EWord -> Expr EWord -> Prop
x .> y = PGT x y
(.>=) :: Expr EWord -> Expr EWord -> Prop
x .>= y = PGEq x y

infix 4 .==, ./=
(.==) :: (Typeable a) => Expr a -> Expr a -> Prop
x .== y = PEq x y
(./=) :: (Typeable a) => Expr a -> Expr a -> Prop
x ./= y = PNeg (PEq x y)

pand :: [Prop] -> Prop
pand = foldl' PAnd (PBool True)

por :: [Prop] -> Prop
por = foldl' POr (PBool False)

instance Eq Prop where
  PBool a == PBool b = a == b
  PEq (a :: Expr x) (b :: Expr x) == PEq (c :: Expr y) (d :: Expr y)
    = case eqT @x @y of
       Just Refl -> a == c && b == d
       Nothing -> False
  PLT a b == PLT c d = a == c && b == d
  PGT a b == PGT c d = a == c && b == d
  PGEq a b == PGEq c d = a == c && b == d
  PLEq a b == PLEq c d = a == c && b == d
  PNeg a == PNeg b = a == b
  PAnd a b == PAnd c d = a == c && b == d
  POr a b == POr c d = a == c && b == d
  _ == _ = False

instance Ord Prop where
  PBool a <= PBool b = a <= b
  PEq (a :: Expr x) (b :: Expr x) <= PEq (c :: Expr y) (d :: Expr y)
    = case eqT @x @y of
       Just Refl -> a <= c && b <= d
       Nothing -> False
  PLT a b <= PLT c d = a <= c && b <= d
  PGT a b <= PGT c d = a <= c && b <= d
  PGEq a b <= PGEq c d = a <= c && b <= d
  PLEq a b <= PLEq c d = a <= c && b <= d
  PNeg a <= PNeg b = a <= b
  PAnd a b <= PAnd c d = a <= c && b <= d
  POr a b <= POr c d = a <= c && b <= d
  _ <= _ = False


unlit :: Expr EWord -> Maybe W256
unlit (Lit x) = Just x
unlit _ = Nothing

unlitByte :: Expr Byte -> Maybe Word8
unlitByte (LitByte x) = Just x
unlitByte _ = Nothing

newtype ByteStringS = ByteStringS ByteString deriving (Eq)

instance Show ByteStringS where
  show (ByteStringS x) = ("0x" ++) . Text.unpack . fromBinary $ x
    where
      fromBinary =
        Text.decodeUtf8 . toStrict . toLazyByteString . byteStringHex

instance JSON.FromJSON ByteString where
  parseJSON (JSON.String x) = case BS16.decodeBase16' x of
                                Left _ -> mzero
                                Right bs -> pure bs
  parseJSON _ = mzero

instance JSON.ToJSON ByteString where
  toJSON x = JSON.String (Text.pack $ "0x" ++ (concatMap (paddedShowHex 2) . BS.unpack $ x))

newtype Addr = Addr { addressWord160 :: Word160 }
  deriving
    ( Num, Integral, Real, Ord, Enum
    , Eq, Generic, Bits, FiniteBits
    )
instance JSON.ToJSON Addr where
  toJSON = JSON.String . Text.pack . show

maybeLitWord :: Expr EWord -> Maybe W256
maybeLitWord (Lit w) = Just w
maybeLitWord _ = Nothing

instance Read W256 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W256 <$> readsPrec n s

instance Show W256 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W256 where
  toJSON x = JSON.String  $ Text.pack ("0x" ++ pad ++ cutshow)
    where
      cutshow = drop 2 $ show x
      pad = replicate (64 - length (cutshow)) '0'

newtype W64 = W64 Data.Word.Word64
  deriving
    ( Num, Integral, Real, Ord, Generic
    , Bits , FiniteBits, Enum, Eq , Bounded
    )
instance JSON.FromJSON W64

instance Read W64 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W64 <$> readsPrec n s

instance Show W64 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W64 where
  toJSON x = JSON.String  $ Text.pack ("0x" ++ cutshow)
    where
      cutshow = drop 2 $ show x

instance Read Addr where
  readsPrec _ ('0':'x':s) = readHex s
  readsPrec _ s = readHex s

instance Show Addr where
  showsPrec _ addr next =
    let hex = showHex addr next
        str = replicate (40 - length hex) '0' ++ hex
    in "0x" ++ toChecksumAddress str ++ drop 40 str

instance JSON.ToJSONKey Addr where
  toJSONKey = JSON.toJSONKeyText (addrKey)
    where
      addrKey :: Addr -> Text
      addrKey addr = Text.pack $ replicate (40 - length hex) '0' ++ hex
        where
          hex = show addr

-- https://eips.ethereum.org/EIPS/eip-55
toChecksumAddress :: String -> String
toChecksumAddress addr = zipWith transform nibbles addr
  where
    nibbles = unpackNibbles . BS.take 20 $ keccakBytes (Char8.pack addr)
    transform nibble = if nibble >= 8 then toUpper else id

strip0x :: ByteString -> ByteString
strip0x bs = if "0x" `Char8.isPrefixOf` bs then Char8.drop 2 bs else bs

strip0x' :: String -> String
strip0x' s = if "0x" `isPrefixOf` s then drop 2 s else s

instance FromJSON W256 where
  parseJSON v = do
    s <- Text.unpack <$> parseJSON v
    case reads s of
      [(x, "")]  -> return x
      _          -> fail $ "invalid hex word (" ++ s ++ ")"

instance FromJSON Addr where
  parseJSON v = do
    s <- Text.unpack <$> parseJSON v
    case reads s of
      [(x, "")] -> return x
      _         -> fail $ "invalid address (" ++ s ++ ")"

#if MIN_VERSION_aeson(1, 0, 0)

instance FromJSONKey W256 where
  fromJSONKey = FromJSONKeyTextParser $ \s ->
    case reads (Text.unpack s) of
      [(x, "")]  -> return x
      _          -> fail $ "invalid word (" ++ Text.unpack s ++ ")"

instance FromJSONKey Addr where
  fromJSONKey = FromJSONKeyTextParser $ \s ->
    case reads (Text.unpack s) of
      [(x, "")] -> return x
      _         -> fail $ "invalid word (" ++ Text.unpack s ++ ")"

#endif

instance ParseField W256
instance ParseFields W256
instance ParseRecord W256 where
  parseRecord = fmap getOnly parseRecord

instance ParseField Addr
instance ParseFields Addr
instance ParseRecord Addr where
  parseRecord = fmap getOnly parseRecord

hexByteString :: String -> ByteString -> ByteString
hexByteString msg bs =
  case BS16.decodeBase16 bs of
    Right x -> x
    _ -> error ("invalid hex bytestring for " ++ msg)

hexText :: Text -> ByteString
hexText t =
  case BS16.decodeBase16 (Text.encodeUtf8 (Text.drop 2 t)) of
    Right x -> x
    _ -> error ("invalid hex bytestring " ++ show t)

readN :: Integral a => String -> a
readN s = fromIntegral (read s :: Integer)

readNull :: Read a => a -> String -> a
readNull x = fromMaybe x . Text.Read.readMaybe

wordField :: JSON.Object -> Key -> JSON.Parser W256
wordField x f = ((readNull 0) . Text.unpack)
                  <$> (x .: f)

word64Field :: JSON.Object -> Key -> JSON.Parser Word64
word64Field x f = ((readNull 0) . Text.unpack)
                  <$> (x .: f)

addrField :: JSON.Object -> Key -> JSON.Parser Addr
addrField x f = (read . Text.unpack) <$> (x .: f)

addrFieldMaybe :: JSON.Object -> Key -> JSON.Parser (Maybe Addr)
addrFieldMaybe x f = (Text.Read.readMaybe . Text.unpack) <$> (x .: f)

dataField :: JSON.Object -> Key -> JSON.Parser ByteString
dataField x f = hexText <$> (x .: f)

toWord512 :: W256 -> Word512
toWord512 (W256 x) = fromHiAndLo 0 x

fromWord512 :: Word512 -> W256
fromWord512 x = W256 (loWord x)

num :: (Integral a, Num b) => a -> b
num = fromIntegral

padLeft :: Int -> ByteString -> ByteString
padLeft n xs = BS.replicate (n - BS.length xs) 0 <> xs

padLeftStr :: Int -> String -> String
padLeftStr n xs = replicate (n - length xs) '0' <> xs

padRight :: Int -> ByteString -> ByteString
padRight n xs = xs <> BS.replicate (n - BS.length xs) 0

padRight' :: Int -> String -> String
padRight' n xs = xs <> replicate (n - length xs) '0'

-- | Right padding  / truncating
--truncpad :: Int -> [SWord 8] -> [SWord 8]
--truncpad n xs = if m > n then take n xs
                --else mappend xs (replicate (n - m) 0)
  --where m = length xs

padLeft' :: Int -> V.Vector (Expr Byte) -> V.Vector (Expr Byte)
padLeft' n xs = V.replicate (n - length xs) (LitByte 0) <> xs

word256 :: ByteString -> Word256
word256 xs = case Cereal.runGet m (padLeft 32 xs) of
               Left _ -> error "internal error"
               Right x -> x
  where
    m = do a <- Cereal.getWord64be
           b <- Cereal.getWord64be
           c <- Cereal.getWord64be
           d <- Cereal.getWord64be
           return $ fromHiAndLo (fromHiAndLo a b) (fromHiAndLo c d)

word :: ByteString -> W256
word = W256 . word256

byteAt :: (Bits a, Bits b, Integral a, Num b) => a -> Int -> b
byteAt x j = num (x `shiftR` (j * 8)) .&. 0xff

fromBE :: (Integral a) => ByteString -> a
fromBE xs = if xs == mempty then 0
  else 256 * fromBE (BS.init xs)
       + (num $ BS.last xs)

asBE :: (Integral a) => a -> ByteString
asBE 0 = mempty
asBE x = asBE (x `div` 256)
  <> BS.pack [num $ x `mod` 256]

word256Bytes :: W256 -> ByteString
word256Bytes x = BS.pack [byteAt x (31 - i) | i <- [0..31]]

word160Bytes :: Addr -> ByteString
word160Bytes x = BS.pack [byteAt x.addressWord160 (19 - i) | i <- [0..19]]

newtype Nibble = Nibble Word8
  deriving ( Num, Integral, Real, Ord, Enum, Eq, Bounded, Generic)

instance Show Nibble where
  show = (:[]) . intToDigit . num

-- Get first and second Nibble from byte
hi, lo :: Word8 -> Nibble
hi b = Nibble $ b `shiftR` 4
lo b = Nibble $ b .&. 0x0f

toByte :: Nibble -> Nibble -> Word8
toByte  (Nibble high) (Nibble low) = high `shift` 4 .|. low

unpackNibbles :: ByteString -> [Nibble]
unpackNibbles bs = BS.unpack bs >>= unpackByte
  where unpackByte b = [hi b, lo b]

-- Well-defined for even length lists only (plz dependent types)
packNibbles :: [Nibble] -> ByteString
packNibbles [] = mempty
packNibbles (n1:n2:ns) = BS.singleton (toByte n1 n2) <> packNibbles ns
packNibbles _ = error "can't pack odd number of nibbles"

toWord64 :: W256 -> Maybe Word64
toWord64 n =
  if n <= num (maxBound :: Word64)
    then let (W256 (Word256 _ (Word128 _ n'))) = n in Just n'
    else Nothing

toInt :: W256 -> Maybe Int
toInt n =
  if n <= num (maxBound :: Int)
    then let (W256 (Word256 _ (Word128 _ n'))) = n in Just (fromIntegral n')
    else Nothing

-- Keccak hashing

keccakBytes :: ByteString -> ByteString
keccakBytes =
  (hash :: ByteString -> Digest Keccak_256)
    >>> BA.convert

word32 :: [Word8] -> Word32
word32 xs = sum [ fromIntegral x `shiftL` (8*n)
                | (n, x) <- zip [0..] (reverse xs) ]

keccak :: Expr Buf -> Expr EWord
keccak (ConcreteBuf bs) = Lit $ keccak' bs
keccak buf = Keccak buf

keccak' :: ByteString -> W256
keccak' = keccakBytes >>> BS.take 32 >>> word

abiKeccak :: ByteString -> Word32
abiKeccak =
  keccakBytes
    >>> BS.take 4
    >>> BS.unpack
    >>> word32

-- Utils

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = fmap concat (mapM f xs)

regexMatches :: Text -> Text -> Bool
regexMatches regexSource =
  let
    compOpts =
      Regex.defaultCompOpt { Regex.lastStarGreedy = True }
    execOpts =
      Regex.defaultExecOpt { Regex.captureGroups = False }
    regex = Regex.makeRegexOpts compOpts execOpts (Text.unpack regexSource)
  in
    Regex.matchTest regex . Seq.fromList . Text.unpack

data VMTrace =
  VMTrace
  { tracePc      :: Int
  , traceOp      :: Int
  , traceStack   :: [W256]
  , traceMemSize :: Data.Word.Word64
  , traceDepth   :: Int
  , traceGas     :: Data.Word.Word64
  } deriving (Generic, Show)
instance JSON.ToJSON VMTrace where
  toEncoding = JSON.genericToEncoding JSON.defaultOptions
instance JSON.FromJSON VMTrace
