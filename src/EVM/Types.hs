{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module EVM.Types where

import GHC.Stack (HasCallStack, prettyCallStack, callStack)
import Control.Arrow ((>>>))
import Control.Monad.State.Strict (State, mzero)
import Crypto.Hash (hash, Keccak_256, Digest)
import Data.Aeson
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.Bifunctor (first)
import Data.Bits (Bits, FiniteBits, shiftR, shift, shiftL, (.&.), (.|.), toIntegralSized)
import Data.ByteArray qualified as BA
import Data.Char
import Data.List (foldl')
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Lazy (toStrict)
import Data.Data
import Data.Int (Int64)
import Data.Word (Word8, Word32, Word64)
import Data.DoubleWord
import Data.DoubleWord.TH
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Sequence qualified as Seq
import Data.Serialize qualified as Cereal
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Tree (Forest)
import Data.Tree.Zipper qualified as Zipper
import Data.Vector qualified as V
import Data.Vector.Storable qualified as SV
import Numeric (readHex, showHex)
import Options.Generic
import Optics.TH
import EVM.Hexdump (paddedShowHex)
import EVM.FeeSchedule (FeeSchedule (..))

import Text.Regex.TDFA qualified as Regex
import Text.Read qualified
import Witch


-- Template Haskell --------------------------------------------------------------------------


-- We need a 512-bit word for doing ADDMOD and MULMOD with full precision.
mkUnpackedDoubleWord "Word512" ''Word256 "Int512" ''Int256 ''Word256
  [''Typeable, ''Data, ''Generic]

instance From Addr Integer where from = fromIntegral
instance From Addr W256 where from = fromIntegral
instance From Int256 Integer where from = fromIntegral
instance From Nibble Int where from = fromIntegral
instance From W256 Integer where from = fromIntegral
instance From Word8 W256 where from = fromIntegral
instance From Word8 Word256 where from = fromIntegral
instance From Word32 W256 where from = fromIntegral
instance From Word32 Word256 where from = fromIntegral
instance From Word64 W256 where from = fromIntegral
instance From Word256 Integer where from = fromIntegral
instance From Word256 W256 where from = fromIntegral

instance TryFrom Int W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int Word256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int256 W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Integer W256 where tryFrom = maybeTryFrom toIntegralSized
-- TODO: hevm relies on this behavior
instance TryFrom W256 Addr where tryFrom = Right . fromIntegral
instance TryFrom W256 FunctionSelector where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int64 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Int256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom W256 Word32 where tryFrom = maybeTryFrom toIntegralSized
-- TODO: hevm relies on this behavior
instance TryFrom W256 Word64 where tryFrom = Right . fromIntegral
instance TryFrom Word160 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word32 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word512 W256 where tryFrom = maybeTryFrom toIntegralSized

-- Symbolic IR -------------------------------------------------------------------------------------

-- phantom type tags for AST construction
data EType
  = Buf
  | Storage
  | Log
  | EWord
  | Byte
  | End
  deriving (Typeable)


-- Variables refering to a global environment
data GVar (a :: EType) where
  BufVar :: Int -> GVar Buf
  StoreVar :: Int -> GVar Storage

deriving instance Show (GVar a)
deriving instance Eq (GVar a)
deriving instance Ord (GVar a)

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
data Expr (a :: EType) where

  -- identifiers

  Lit            :: {-# UNPACK #-} !W256 -> Expr EWord
  Var            :: Text -> Expr EWord
  GVar           :: GVar a -> Expr a

  -- bytes

  LitByte        :: {-# UNPACK #-} !Word8 -> Expr Byte
  IndexWord      :: Expr EWord -> Expr EWord -> Expr Byte
  EqByte         :: Expr Byte  -> Expr Byte  -> Expr EWord

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

  Partial        :: [Prop] -> Traces -> PartialExec -> Expr End
  Failure        :: [Prop] -> Traces -> EvmError -> Expr End
  Success        :: [Prop] -> Traces -> Expr Buf -> Expr Storage -> Expr End
  ITE            :: Expr EWord -> Expr End -> Expr End -> Expr End

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
  Max            :: Expr EWord -> Expr EWord -> Expr EWord

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


-- Existential Wrapper -----------------------------------------------------------------------------


data SomeExpr = forall a . Typeable a => SomeExpr (Expr a)

deriving instance Show SomeExpr

instance Eq SomeExpr where
  SomeExpr (a :: Expr b) == SomeExpr (c :: Expr d) =
    case eqT @b @d of
      Just Refl -> a == c
      Nothing -> False

instance Ord SomeExpr where
  compare (SomeExpr (a :: Expr b)) (SomeExpr (c :: Expr d)) =
    case eqT @b @d of
      Just Refl -> compare a c
      Nothing -> compare (toNum a) (toNum c)

toNum :: (Typeable a) => Expr a -> Int
toNum (_ :: Expr a) =
  case eqT @a @Buf of
    Just Refl -> 1
    Nothing -> case eqT @a @Storage of
      Just Refl -> 2
      Nothing -> case eqT @a @Log of
        Just Refl -> 3
        Nothing -> case eqT @a @EWord of
          Just Refl -> 4
          Nothing -> case eqT @a @Byte of
            Just Refl -> 5
            Nothing -> 6


-- Propostions -------------------------------------------------------------------------------------


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
  PImpl :: Prop -> Prop -> Prop
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
  PImpl a b == PImpl c d = a == c && b == d
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
  PImpl a b <= PImpl c d = a <= c && b <= d
  _ <= _ = False


-- Errors ------------------------------------------------------------------------------------------


-- | Core EVM Error Types
data EvmError
  = BalanceTooLow W256 W256
  | UnrecognizedOpcode Word8
  | SelfDestruction
  | StackUnderrun
  | BadJumpDestination
  | Revert (Expr Buf)
  | OutOfGas Word64 Word64
  | StackLimitExceeded
  | IllegalOverflow
  | StateChangeWhileStatic
  | InvalidMemoryAccess
  | CallDepthLimitReached
  | MaxCodeSizeExceeded W256 W256
  | MaxInitCodeSizeExceeded W256 W256
  | InvalidFormat
  | PrecompileFailure
  | ReturnDataOutOfBounds
  | NonceOverflow
  | BadCheatCode FunctionSelector
  deriving (Show, Eq, Ord)

-- | Sometimes we can only partially execute a given program
data PartialExec
  = UnexpectedSymbolicArg  { pc :: Int, msg  :: String, args  :: [SomeExpr] }
  | MaxIterationsReached  { pc :: Int, addr :: Addr }
  deriving (Show, Eq, Ord)

-- | Effect types used by the vm implementation for side effects & control flow
data Effect
  = Query Query
  | Choose Choose
deriving instance Show Effect

-- | Queries halt execution until resolved through RPC calls or SMT queries
data Query where
  PleaseFetchContract :: Addr -> (Contract -> EVM ()) -> Query
  PleaseFetchSlot     :: Addr -> W256 -> (W256 -> EVM ()) -> Query
  PleaseAskSMT        :: Expr EWord -> [Prop] -> (BranchCondition -> EVM ()) -> Query
  PleaseDoFFI         :: [String] -> (ByteString -> EVM ()) -> Query

-- | Execution could proceed down one of two branches
data Choose where
  PleaseChoosePath    :: Expr EWord -> (Bool -> EVM ()) -> Choose

-- | The possible return values of a SMT query
data BranchCondition = Case Bool | Unknown
  deriving Show

instance Show Query where
  showsPrec _ = \case
    PleaseFetchContract addr _ ->
      (("<EVM.Query: fetch contract " ++ show addr ++ ">") ++)
    PleaseFetchSlot addr slot _ ->
      (("<EVM.Query: fetch slot "
        ++ show slot ++ " for "
        ++ show addr ++ ">") ++)
    PleaseAskSMT condition constraints _ ->
      (("<EVM.Query: ask SMT about "
        ++ show condition ++ " in context "
        ++ show constraints ++ ">") ++)
    PleaseDoFFI cmd _ ->
      (("<EVM.Query: do ffi: " ++ (show cmd)) ++)

instance Show Choose where
  showsPrec _ = \case
    PleaseChoosePath _ _ ->
      (("<EVM.Choice: waiting for user to select path (0,1)") ++)

-- | The possible result states of a VM
data VMResult
  = VMFailure EvmError     -- ^ An operation failed
  | VMSuccess (Expr Buf)   -- ^ Reached STOP, RETURN, or end-of-code
  | HandleEffect Effect    -- ^ An effect must be handled for execution to continue
  | Unfinished PartialExec -- ^ Execution could not continue further

deriving instance Show VMResult


-- VM State ----------------------------------------------------------------------------------------


-- | The state of a stepwise EVM execution
data VM = VM
  { result         :: Maybe VMResult
  , state          :: FrameState
  , frames         :: [Frame]
  , env            :: Env
  , block          :: Block
  , tx             :: TxState
  , logs           :: [Expr Log]
  , traces         :: Zipper.TreePos Zipper.Empty Trace
  , cache          :: Cache
  , burned         :: {-# UNPACK #-} !Word64
  , iterations     :: Map CodeLocation (Int, [Expr EWord]) -- ^ how many times we've visited a loc, and what the contents of the stack were when we were there last
  , constraints    :: [Prop]
  , keccakEqs      :: [Prop]
  , allowFFI       :: Bool
  , overrideCaller :: Maybe Addr
  }
  deriving (Show, Generic)

-- | Alias for the type of e.g. @exec1@.
type EVM a = State VM a

-- | An entry in the VM's "call/create stack"
data Frame = Frame
  { context :: FrameContext
  , state   :: FrameState
  }
  deriving (Show)

-- | Call/create info
data FrameContext
  = CreationContext
    { address         :: Addr
    , codehash        :: Expr EWord
    , createreversion :: Map Addr Contract
    , substate        :: SubState
    }
  | CallContext
    { target        :: Addr
    , context       :: Addr
    , offset        :: W256
    , size          :: W256
    , codehash      :: Expr EWord
    , abi           :: Maybe W256
    , calldata      :: Expr Buf
    , callreversion :: (Map Addr Contract, Expr Storage)
    , subState      :: SubState
    }
  deriving (Eq, Ord, Show, Generic)

-- | The "accrued substate" across a transaction
data SubState = SubState
  { selfdestructs       :: [Addr]
  , touchedAccounts     :: [Addr]
  , accessedAddresses   :: Set Addr
  , accessedStorageKeys :: Set (Addr, W256)
  , refunds             :: [(Addr, Word64)]
  -- in principle we should include logs here, but do not for now
  }
  deriving (Eq, Ord, Show)

-- | The "registers" of the VM along with memory and data stack
data FrameState = FrameState
  { contract     :: Addr
  , codeContract :: Addr
  , code         :: ContractCode
  , pc           :: {-# UNPACK #-} !Int
  , stack        :: [Expr EWord]
  , memory       :: Expr Buf
  , memorySize   :: Word64
  , calldata     :: Expr Buf
  , callvalue    :: Expr EWord
  , caller       :: Expr EWord
  , gas          :: {-# UNPACK #-} !Word64
  , returndata   :: Expr Buf
  , static       :: Bool
  }
  deriving (Show, Generic)

-- | The state that spans a whole transaction
data TxState = TxState
  { gasprice    :: W256
  , gaslimit    :: Word64
  , priorityFee :: W256
  , origin      :: Addr
  , toAddr      :: Addr
  , value       :: Expr EWord
  , substate    :: SubState
  , isCreate    :: Bool
  , txReversion :: Map Addr Contract
  }
  deriving (Show)

-- | When doing symbolic execution, we have three different
-- ways to model the storage of contracts. This determines
-- not only the initial contract storage model but also how
-- RPC or state fetched contracts will be modeled.
data StorageModel
  = ConcreteS    -- ^ Uses `Concrete` Storage. Reading / Writing from abstract
                 -- locations causes a runtime failure. Can be nicely combined with RPC.

  | SymbolicS    -- ^ Uses `Symbolic` Storage. Reading / Writing never reaches RPC,
                 -- but always done using an SMT array with no default value.

  | InitialS     -- ^ Uses `Symbolic` Storage. Reading / Writing never reaches RPC,
                 -- but always done using an SMT array with 0 as the default value.

  deriving (Read, Show)

instance ParseField StorageModel

-- | Various environmental data
data Env = Env
  { contracts    :: Map Addr Contract
  , chainId      :: W256
  , storage      :: Expr Storage
  , origStorage  :: Map W256 (Map W256 W256)
  }
  deriving (Show, Generic)

-- | Data about the block
data Block = Block
  { coinbase    :: Addr
  , timestamp   :: Expr EWord
  , number      :: W256
  , prevRandao  :: W256
  , gaslimit    :: Word64
  , baseFee     :: W256
  , maxCodeSize :: W256
  , schedule    :: FeeSchedule Word64
  } deriving (Show, Generic)

-- | The state of a contract
data Contract = Contract
  { contractcode :: ContractCode
  , balance      :: W256
  , nonce        :: W256
  , codehash     :: Expr EWord
  , opIxMap      :: SV.Vector Int
  , codeOps      :: V.Vector (Int, Op)
  , external     :: Bool
  }
  deriving (Eq, Ord, Show)


-- Bytecode Representations ------------------------------------------------------------------------


-- | A unique id for a given pc
type CodeLocation = (Addr, Int)

-- | The cache is data that can be persisted for efficiency:
-- any expensive query that is constant at least within a block.
data Cache = Cache
  { fetchedContracts :: Map Addr Contract
  , fetchedStorage :: Map W256 (Map W256 W256)
  , path :: Map (CodeLocation, Int) Bool
  } deriving (Show, Generic)

instance Semigroup Cache where
  a <> b = Cache
    { fetchedContracts = Map.unionWith unifyCachedContract a.fetchedContracts b.fetchedContracts
    , fetchedStorage = Map.unionWith unifyCachedStorage a.fetchedStorage b.fetchedStorage
    , path = mappend a.path b.path
    }

instance Monoid Cache where
  mempty = Cache { fetchedContracts = mempty
                 , fetchedStorage = mempty
                 , path = mempty
                 }

unifyCachedStorage :: Map W256 W256 -> Map W256 W256 -> Map W256 W256
unifyCachedStorage _ _ = undefined

-- only intended for use in Cache merges, where we expect
-- everything to be Concrete
unifyCachedContract :: Contract -> Contract -> Contract
unifyCachedContract _ _ = undefined
  {-
unifyCachedContract a b = a & set storage merged
  where merged = case (view storage a, view storage b) of
                   (ConcreteStore sa, ConcreteStore sb) ->
                     ConcreteStore (mappend sa sb)
                   _ ->
                     view storage a
   -}


-- Bytecode Representations ------------------------------------------------------------------------


{- |
  A contract is either in creation (running its "constructor") or
  post-creation, and code in these two modes is treated differently
  by instructions like @EXTCODEHASH@, so we distinguish these two
  code types.

  The definition follows the structure of code output by solc. We need to use
  some heuristics here to deal with symbolic data regions that may be present
  in the bytecode since the fully abstract case is impractical:

  - initcode has concrete code, followed by an abstract data "section"
  - runtimecode has a fixed length, but may contain fixed size symbolic regions (due to immutable)

  hopefully we do not have to deal with dynamic immutable before we get a real data section...
-}
data ContractCode
  = InitCode ByteString (Expr Buf) -- ^ "Constructor" code, during contract creation
  | RuntimeCode RuntimeCode -- ^ "Instance" code, after contract creation
  deriving (Show, Ord)

-- | We have two variants here to optimize the fully concrete case.
-- ConcreteRuntimeCode just wraps a ByteString
-- SymbolicRuntimeCode is a fixed length vector of potentially symbolic bytes, which lets us handle symbolic pushdata (e.g. from immutable variables in solidity).
data RuntimeCode
  = ConcreteRuntimeCode ByteString
  | SymbolicRuntimeCode (V.Vector (Expr Byte))
  deriving (Show, Eq, Ord)

-- runtime err when used for symbolic code
instance Eq ContractCode where
  InitCode a b  == InitCode c d  = a == c && b == d
  RuntimeCode x == RuntimeCode y = x == y
  _ == _ = False


-- Execution Traces --------------------------------------------------------------------------------


data Trace = Trace
  { opIx      :: Int
  , contract  :: Contract
  , tracedata :: TraceData
  }
  deriving (Eq, Ord, Show, Generic)

data TraceData
  = EventTrace (Expr EWord) (Expr Buf) [Expr EWord]
  | FrameTrace FrameContext
  | ErrorTrace EvmError
  | EntryTrace Text
  | ReturnTrace (Expr Buf) FrameContext
  deriving (Eq, Ord, Show, Generic)

-- | Wrapper type containing vm traces and the context needed to pretty print them properly
data Traces = Traces
  { traces :: Forest Trace
  , contracts :: Map Addr Contract
  }
  deriving (Eq, Ord, Show, Generic)

instance Semigroup Traces where
  (Traces a b) <> (Traces c d) = Traces (a <> c) (b <> d)
instance Monoid Traces where
  mempty = Traces mempty mempty


-- VM Initialization -------------------------------------------------------------------------------


-- | A specification for an initial VM state
data VMOpts = VMOpts
  { contract :: Contract
  , calldata :: (Expr Buf, [Prop])
  , initialStorage :: Expr Storage
  , value :: Expr EWord
  , priorityFee :: W256
  , address :: Addr
  , caller :: Expr EWord
  , origin :: Addr
  , gas :: Word64
  , gaslimit :: Word64
  , number :: W256
  , timestamp :: Expr EWord
  , coinbase :: Addr
  , prevRandao :: W256
  , maxCodeSize :: W256
  , blockGaslimit :: Word64
  , gasprice :: W256
  , baseFee :: W256
  , schedule :: FeeSchedule Word64
  , chainId :: W256
  , create :: Bool
  , txAccessList :: Map Addr [W256]
  , allowFFI :: Bool
  } deriving Show


-- Opcodes -----------------------------------------------------------------------------------------


type Op = GenericOp (Expr EWord)

data GenericOp a
  = OpStop
  | OpAdd
  | OpMul
  | OpSub
  | OpDiv
  | OpSdiv
  | OpMod
  | OpSmod
  | OpAddmod
  | OpMulmod
  | OpExp
  | OpSignextend
  | OpLt
  | OpGt
  | OpSlt
  | OpSgt
  | OpEq
  | OpIszero
  | OpAnd
  | OpOr
  | OpXor
  | OpNot
  | OpByte
  | OpShl
  | OpShr
  | OpSar
  | OpSha3
  | OpAddress
  | OpBalance
  | OpOrigin
  | OpCaller
  | OpCallvalue
  | OpCalldataload
  | OpCalldatasize
  | OpCalldatacopy
  | OpCodesize
  | OpCodecopy
  | OpGasprice
  | OpExtcodesize
  | OpExtcodecopy
  | OpReturndatasize
  | OpReturndatacopy
  | OpExtcodehash
  | OpBlockhash
  | OpCoinbase
  | OpTimestamp
  | OpNumber
  | OpPrevRandao
  | OpGaslimit
  | OpChainid
  | OpSelfbalance
  | OpBaseFee
  | OpPop
  | OpMload
  | OpMstore
  | OpMstore8
  | OpSload
  | OpSstore
  | OpJump
  | OpJumpi
  | OpPc
  | OpMsize
  | OpGas
  | OpJumpdest
  | OpCreate
  | OpCall
  | OpStaticcall
  | OpCallcode
  | OpReturn
  | OpDelegatecall
  | OpCreate2
  | OpRevert
  | OpSelfdestruct
  | OpDup !Word8
  | OpSwap !Word8
  | OpLog !Word8
  | OpPush0
  | OpPush a
  | OpUnknown Word8
  deriving (Show, Eq, Ord, Functor)


-- Function Selectors ------------------------------------------------------------------------------


-- | https://docs.soliditylang.org/en/v0.8.19/abi-spec.html#function-selector
newtype FunctionSelector = FunctionSelector { unFunctionSelector :: Word32 }
  deriving (Bits, Num, Eq, Ord, Real, Enum, Integral)
instance Show FunctionSelector where show s = "0x" <> showHex s ""


-- ByteString wrapper ------------------------------------------------------------------------------


-- Newtype wrapper for ByteString to allow custom instances
newtype ByteStringS = ByteStringS ByteString deriving (Eq, Generic)

instance Show ByteStringS where
  show (ByteStringS x) = ("0x" ++) . T.unpack . fromBinary $ x
    where
      fromBinary =
        T.decodeUtf8 . toStrict . toLazyByteString . byteStringHex

instance JSON.FromJSON ByteStringS where
  parseJSON (JSON.String x) = case BS16.decodeBase16' x of
                                Left _ -> mzero
                                Right bs -> pure (ByteStringS bs)
  parseJSON _ = mzero

instance JSON.ToJSON ByteStringS where
  toJSON (ByteStringS x) = JSON.String (T.pack $ "0x" ++ (concatMap (paddedShowHex 2) . BS.unpack $ x))


-- Word256 wrapper ---------------------------------------------------------------------------------


-- Newtype wrapper around Word256 to allow custom instances
newtype W256 = W256 Word256
  deriving
    ( Num, Integral, Real, Ord, Bits
    , Generic, FiniteBits, Enum, Eq , Bounded
    )

instance Read W256 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W256 <$> readsPrec n s

instance Show W256 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W256 where
  toJSON x = JSON.String  $ T.pack ("0x" ++ pad ++ cutshow)
    where
      cutshow = drop 2 $ show x
      pad = replicate (64 - length (cutshow)) '0'

instance FromJSON W256 where
  parseJSON v = do
    s <- T.unpack <$> parseJSON v
    case reads s of
      [(x, "")]  -> pure x
      _          -> fail $ "invalid hex word (" ++ s ++ ")"

instance FromJSONKey W256 where
  fromJSONKey = FromJSONKeyTextParser $ \s ->
    case reads (T.unpack s) of
      [(x, "")]  -> pure x
      _          -> fail $ "invalid word (" ++ T.unpack s ++ ")"

wordField :: JSON.Object -> Key -> JSON.Parser W256
wordField x f = ((readNull 0) . T.unpack)
                  <$> (x .: f)

instance ParseField W256
instance ParseFields W256
instance ParseRecord W256 where
  parseRecord = fmap getOnly parseRecord


-- Word64 wrapper ----------------------------------------------------------------------------------


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
  toJSON x = JSON.String  $ T.pack $ show x

word64Field :: JSON.Object -> Key -> JSON.Parser Word64
word64Field x f = ((readNull 0) . T.unpack)
                  <$> (x .: f)


-- Addresses ---------------------------------------------------------------------------------------


newtype Addr = Addr { addressWord160 :: Word160 }
  deriving
    ( Num, Integral, Real, Ord, Enum
    , Eq, Generic, Bits, FiniteBits
    )

instance Read Addr where
  readsPrec _ ('0':'x':s) = readHex s
  readsPrec _ s = readHex s

instance Show Addr where
  showsPrec _ addr next =
    let hex = showHex addr next
        str = replicate (40 - length hex) '0' ++ hex
    in "0x" ++ toChecksumAddress str ++ drop 40 str

-- https://eips.ethereum.org/EIPS/eip-55
toChecksumAddress :: String -> String
toChecksumAddress addr = zipWith transform nibbles addr
  where
    nibbles = unpackNibbles . BS.take 20 $ keccakBytes (Char8.pack addr)
    transform nibble = if nibble >= 8 then toUpper else id

instance JSON.ToJSON Addr where
  toJSON = JSON.String . T.pack . show

instance FromJSON Addr where
  parseJSON v = do
    s <- T.unpack <$> parseJSON v
    case reads s of
      [(x, "")] -> pure x
      _         -> fail $ "invalid address (" ++ s ++ ")"

instance JSON.ToJSONKey Addr where
  toJSONKey = JSON.toJSONKeyText (addrKey)
    where
      addrKey :: Addr -> Text
      addrKey addr = T.pack $ replicate (40 - length hex) '0' ++ hex
        where
          hex = show addr

instance FromJSONKey Addr where
  fromJSONKey = FromJSONKeyTextParser $ \s ->
    case reads (T.unpack s) of
      [(x, "")] -> pure x
      _         -> fail $ "invalid word (" ++ T.unpack s ++ ")"

addrField :: JSON.Object -> Key -> JSON.Parser Addr
addrField x f = (read . T.unpack) <$> (x .: f)

addrFieldMaybe :: JSON.Object -> Key -> JSON.Parser (Maybe Addr)
addrFieldMaybe x f = (Text.Read.readMaybe . T.unpack) <$> (x .: f)

instance ParseField Addr
instance ParseFields Addr
instance ParseRecord Addr where
  parseRecord = fmap getOnly parseRecord


-- Nibbles -----------------------------------------------------------------------------------------


-- | A four bit value
newtype Nibble = Nibble Word8
  deriving (Num, Integral, Real, Ord, Enum, Eq, Bounded, Generic)

instance Show Nibble where
  show = (:[]) . intToDigit . fromIntegral


-- Conversions -------------------------------------------------------------------------------------


toWord512 :: W256 -> Word512
toWord512 (W256 x) = fromHiAndLo 0 x

fromWord512 :: Word512 -> W256
fromWord512 x = W256 (loWord x)

maybeLitByte :: Expr Byte -> Maybe Word8
maybeLitByte (LitByte x) = Just x
maybeLitByte _ = Nothing

maybeLitWord :: Expr EWord -> Maybe W256
maybeLitWord (Lit w) = Just w
maybeLitWord _ = Nothing

word256 :: ByteString -> Word256
word256 xs | BS.length xs == 1 =
  -- optimize one byte pushes
  Word256 (Word128 0 0) (Word128 0 (fromIntegral $ BS.head xs))
word256 xs = case Cereal.runGet m (padLeft 32 xs) of
               Left _ -> internalError "should not happen"
               Right x -> x
  where
    m = do a <- Cereal.getWord64be
           b <- Cereal.getWord64be
           c <- Cereal.getWord64be
           d <- Cereal.getWord64be
           pure $ Word256 (Word128 a b) (Word128 c d)

word :: ByteString -> W256
word = W256 . word256

fromBE :: (Integral a) => ByteString -> a
fromBE xs = if xs == mempty then 0
  else 256 * fromBE (BS.init xs)
       + (fromIntegral $ BS.last xs)

asBE :: (Integral a) => a -> ByteString
asBE 0 = mempty
asBE x = asBE (x `div` 256)
  <> BS.pack [fromIntegral $ x `mod` 256]

word256Bytes :: W256 -> ByteString
word256Bytes (W256 (Word256 (Word128 a b) (Word128 c d))) =
  Cereal.encode a <> Cereal.encode b <> Cereal.encode c <> Cereal.encode d

word160Bytes :: Addr -> ByteString
word160Bytes (Addr (Word160 a (Word128 b c))) =
  Cereal.encode a <> Cereal.encode b <> Cereal.encode c

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
packNibbles _ = internalError "can't pack odd number of nibbles"

toWord64 :: W256 -> Maybe Word64
toWord64 n =
  if n <= into (maxBound :: Word64)
    then let (W256 (Word256 _ (Word128 _ n'))) = n in Just n'
    else Nothing

toInt :: W256 -> Maybe Int
toInt n =
  if n <= unsafeInto (maxBound :: Int)
    then let (W256 (Word256 _ (Word128 _ n'))) = n in Just (fromIntegral n')
    else Nothing

bssToBs :: ByteStringS -> ByteString
bssToBs (ByteStringS bs) = bs


-- Keccak hashing ----------------------------------------------------------------------------------


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

abiKeccak :: ByteString -> FunctionSelector
abiKeccak =
  keccakBytes
    >>> BS.take 4
    >>> BS.unpack
    >>> word32
    >>> FunctionSelector


-- Utils -------------------------------------------------------------------------------------------

internalError:: HasCallStack => [Char] -> a
internalError m = error $ "Internal error: " ++ m ++ " -- " ++ (prettyCallStack callStack)

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = fmap concat (mapM f xs)

regexMatches :: Text -> Text -> Bool
regexMatches regexSource =
  let
    compOpts =
      Regex.defaultCompOpt { Regex.lastStarGreedy = True }
    execOpts =
      Regex.defaultExecOpt { Regex.captureGroups = False }
    regex = Regex.makeRegexOpts compOpts execOpts (T.unpack regexSource)
  in
    Regex.matchTest regex . Seq.fromList . T.unpack

readNull :: Read a => a -> String -> a
readNull x = fromMaybe x . Text.Read.readMaybe

padLeft :: Int -> ByteString -> ByteString
padLeft n xs = BS.replicate (n - BS.length xs) 0 <> xs

padLeft' :: Int -> V.Vector (Expr Byte) -> V.Vector (Expr Byte)
padLeft' n xs = V.replicate (n - length xs) (LitByte 0) <> xs

padRight :: Int -> ByteString -> ByteString
padRight n xs = xs <> BS.replicate (n - BS.length xs) 0

padRight' :: Int -> String -> String
padRight' n xs = xs <> replicate (n - length xs) '0'

-- We need this here instead of Format for cyclic import reasons...
formatString :: ByteString -> String
formatString bs =
  case T.decodeUtf8' (fst (BS.spanEnd (== 0) bs)) of
    Right s -> "\"" <> T.unpack s <> "\""
    Left _ -> "❮utf8 decode failed❯: " <> (show $ ByteStringS bs)

-- To display ByteStrings as HEX values
byteStringToHex :: ByteString -> String
byteStringToHex bs = foldMap (++"") $ "0x" : map toHex (BS.unpack bs)

toHex :: Word8 -> String
toHex w = case showHex w "" of
           [w1,w2] -> [w1, w2]
           [w2]    -> ['0', w2]
           _       -> "showHex returned []"

-- Optics ------------------------------------------------------------------------------------------


makeFieldLabelsNoPrefix ''VM
makeFieldLabelsNoPrefix ''FrameState
makeFieldLabelsNoPrefix ''TxState
makeFieldLabelsNoPrefix ''SubState
makeFieldLabelsNoPrefix ''Cache
makeFieldLabelsNoPrefix ''Trace
makeFieldLabelsNoPrefix ''VMOpts
makeFieldLabelsNoPrefix ''Frame
makeFieldLabelsNoPrefix ''FrameContext
makeFieldLabelsNoPrefix ''Contract
makeFieldLabelsNoPrefix ''Env
makeFieldLabelsNoPrefix ''Block
