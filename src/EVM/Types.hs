{-# LANGUAGE CPP #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

{-# OPTIONS_GHC -Wno-inline-rule-shadowing #-}

module EVM.Types where

import GHC.Stack (HasCallStack, prettyCallStack, callStack)
import Control.Arrow ((>>>))
import Control.Monad (mzero)
import Control.Monad.ST (ST)
import Control.Monad.State.Strict (StateT)
import Crypto.Hash (hash, Keccak_256, Digest)
import Data.Aeson
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.Bifunctor (first)
import Data.Bits (Bits, FiniteBits, shiftR, shift, shiftL, (.&.), (.|.), toIntegralSized)
import Data.Binary qualified as Binary
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
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Serialize qualified as Cereal
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Tree (Forest)
import Data.Tree.Zipper qualified as Zipper
import Data.Vector qualified as V
import Data.Vector.Storable qualified as SV
import Data.Vector.Unboxed.Mutable (STVector)
import Numeric (readHex, showHex)
import Options.Generic
import Optics.TH
import EVM.FeeSchedule (FeeSchedule (..))

import Text.Regex.TDFA qualified as Regex
import Text.Read qualified
import Witch


-- Template Haskell --------------------------------------------------------------------------


-- We need a 512-bit word for doing ADDMOD and MULMOD with full precision.
mkUnpackedDoubleWord "Word512" ''Word256 "Int512" ''Int256 ''Word256
  [''Typeable, ''Data, ''Generic]



-- Conversions -------------------------------------------------------------------------------------


-- We ignore hlint to suppress the warnings about `fromIntegral` and friends here
#ifndef __HLINT__

instance From Addr Integer where from = fromIntegral
instance From Addr W256 where from = fromIntegral
instance From Int256 Integer where from = fromIntegral
instance From Nibble Int where from = fromIntegral
instance From W256 Integer where from = fromIntegral
instance From Word8 W256 where from = fromIntegral
instance From Word8 Word256 where from = fromIntegral
instance From Word32 W256 where from = fromIntegral
instance From Word32 Word256 where from = fromIntegral
instance From Word32 ByteString where from = toStrict . Binary.encode
instance From Word64 W256 where from = fromIntegral
instance From W64 W256 where from = fromIntegral
instance From Word256 Integer where from = fromIntegral
instance From Word256 W256 where from = fromIntegral

instance TryFrom Int W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int Word256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Int256 W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Integer W256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Integer Addr where tryFrom = maybeTryFrom toIntegralSized
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
instance TryFrom W256 W64 where tryFrom = Right . fromIntegral
instance TryFrom Word160 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Int256 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word8 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word256 Word32 where tryFrom = maybeTryFrom toIntegralSized
instance TryFrom Word512 W256 where tryFrom = maybeTryFrom toIntegralSized

truncateToAddr :: W256 -> Addr
truncateToAddr = fromIntegral

#endif


-- Symbolic IR -------------------------------------------------------------------------------------


-- phantom type tags for AST construction
data EType
  = Buf
  | Storage
  | Log
  | EWord
  | EAddr
  | EContract
  | Byte
  | End
  deriving (Typeable)

-- Variables referring to a global environment
data GVar (a :: EType) where
  BufVar :: Int -> GVar Buf
  StoreVar :: Int -> GVar Storage

deriving instance Show (GVar a)
deriving instance Eq (GVar a)
deriving instance Ord (GVar a)

{- |
  Expr implements an abstract representation of an EVM program

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

  -- | Literal words
  Lit            :: {-# UNPACK #-} !W256 -> Expr EWord
  -- | Variables
  Var            :: Text -> Expr EWord
  -- | variables introduced during the CSE pass
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

  Partial        :: [Prop] -> TraceContext -> PartialExec -> Expr End
  Failure        :: [Prop] -> TraceContext -> EvmError -> Expr End
  Success        :: [Prop] -> TraceContext -> Expr Buf -> Map (Expr EAddr) (Expr EContract) -> Expr End
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

  -- tx context

  TxValue        :: Expr EWord

  -- frame context

  Balance        :: Expr EAddr -> Expr EWord

  Gas            :: Int                -- frame idx
                 -> Expr EWord

  -- code

  CodeSize       :: Expr EAddr         -- address
                 -> Expr EWord         -- size

  CodeHash       :: Expr EAddr         -- address
                 -> Expr EWord         -- size

  -- logs

  LogEntry       :: Expr EWord         -- address
                 -> Expr Buf           -- data
                 -> [Expr EWord]       -- topics
                 -> Expr Log


  -- Contract

  -- A restricted view of a contract that does not include extraneous metadata
  -- from the full constructor defined in the VM state
  C ::
    { code     :: ContractCode
    , storage  :: Expr Storage
    , tStorage :: Expr Storage
    , balance  :: Expr EWord
    , nonce    :: Maybe W64
    } -> Expr EContract

  -- addresses

  -- Symbolic addresses are identified with an int. It is important that
  -- semantic equality is the same as syntactic equality here. Additionally all
  -- SAddr's in a given expression should be constrained to differ from any LitAddr's
  SymAddr        :: Text -> Expr EAddr
  LitAddr        :: Addr -> Expr EAddr
  WAddr          :: Expr EAddr -> Expr EWord

  -- storage

  ConcreteStore  :: (Map W256 W256) -> Expr Storage
  AbstractStore  :: Expr EAddr -- which contract is this store for?
                 -> Maybe W256 -- which logical store does this refer to? (e.g. solidity mappings / arrays)
                 -> Expr Storage

  SLoad          :: Expr EWord         -- key
                 -> Expr Storage       -- storage
                 -> Expr EWord         -- result

  SStore         :: Expr EWord         -- key
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
       Just Refl -> a <= c || b <= d
       Nothing -> toNum a <= toNum c
  PLT a b <= PLT c d = a <= c || b <= d
  PGT a b <= PGT c d = a <= c || b <= d
  PGEq a b <= PGEq c d = a <= c || b <= d
  PLEq a b <= PLEq c d = a <= c || b <= d
  PNeg a <= PNeg b = a <= b
  PAnd a b <= PAnd c d = a <= c || b <= d
  POr a b <= POr c d = a <= c || b <= d
  PImpl a b <= PImpl c d = a <= c || b <= d
  a <= b = asNum a <= asNum b
    where
      asNum :: Prop -> Int
      asNum (PBool {}) = 0
      asNum (PEq   {}) = 1
      asNum (PLT   {}) = 2
      asNum (PGT   {}) = 3
      asNum (PGEq  {}) = 4
      asNum (PLEq  {}) = 5
      asNum (PNeg  {}) = 6
      asNum (PAnd  {}) = 7
      asNum (POr   {}) = 8
      asNum (PImpl {}) = 9



isPBool :: Prop -> Bool
isPBool (PBool _) = True
isPBool _ = False


-- Errors ------------------------------------------------------------------------------------------


-- | Core EVM Error Types
data EvmError
  = BalanceTooLow (Expr EWord) (Expr EWord)
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
  | MaxInitCodeSizeExceeded W256 (Expr EWord)
  | InvalidFormat
  | PrecompileFailure
  | ReturnDataOutOfBounds
  | NonceOverflow
  | BadCheatCode FunctionSelector
  | NonexistentFork Int
  deriving (Show, Eq, Ord)

-- | Sometimes we can only partially execute a given program
data PartialExec
  = UnexpectedSymbolicArg { pc :: Int, msg  :: String, args  :: [SomeExpr] }
  | MaxIterationsReached  { pc :: Int, addr :: Expr EAddr }
  | JumpIntoSymbolicCode  { pc :: Int, jumpDst :: Int }
  deriving (Show, Eq, Ord)

-- | Effect types used by the vm implementation for side effects & control flow
data Effect t s where
  Query :: Query t s -> Effect t s
  Choose :: Choose s -> Effect Symbolic s
deriving instance Show (Effect t s)

-- | Queries halt execution until resolved through RPC calls or SMT queries
data Query t s where
  PleaseFetchContract :: Addr -> BaseState -> (Contract -> EVM t s ()) -> Query t s
  PleaseFetchSlot     :: Addr -> W256 -> (W256 -> EVM t s ()) -> Query t s
  PleaseAskSMT        :: Expr EWord -> [Prop] -> (BranchCondition -> EVM Symbolic s ()) -> Query Symbolic s
  PleaseDoFFI         :: [String] -> (ByteString -> EVM t s ()) -> Query t s

-- | Execution could proceed down one of two branches
data Choose s where
  PleaseChoosePath    :: Expr EWord -> (Bool -> EVM Symbolic s ()) -> Choose s

-- | The possible return values of a SMT query
data BranchCondition = Case Bool | Unknown
  deriving Show

instance Show (Query t s) where
  showsPrec _ = \case
    PleaseFetchContract addr base _ ->
      (("<EVM.Query: fetch contract " ++ show addr ++ show base ++ ">") ++)
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

instance Show (Choose s) where
  showsPrec _ = \case
    PleaseChoosePath _ _ ->
      (("<EVM.Choice: waiting for user to select path (0,1)") ++)

-- | The possible result states of a VM
data VMResult (t :: VMType) s where
  Unfinished :: PartialExec -> VMResult Symbolic s -- ^ Execution could not continue further
  VMFailure :: EvmError -> VMResult t s            -- ^ An operation failed
  VMSuccess :: (Expr Buf) -> VMResult t s          -- ^ Reached STOP, RETURN, or end-of-code
  HandleEffect :: (Effect t s) -> VMResult t s     -- ^ An effect must be handled for execution to continue

deriving instance Show (VMResult t s)


-- VM State ----------------------------------------------------------------------------------------

data VMType = Symbolic | Concrete

type family Gas (t :: VMType) = r | r -> t where
  Gas Symbolic = ()
  Gas Concrete = Word64

-- | The state of a stepwise EVM execution
data VM (t :: VMType) s = VM
  { result         :: Maybe (VMResult t s)
  , state          :: FrameState t s
  , frames         :: [Frame t s]
  , env            :: Env
  , block          :: Block
  , tx             :: TxState
  , logs           :: [Expr Log]
  , traces         :: Zipper.TreePos Zipper.Empty Trace
  , cache          :: Cache
  , burned         :: !(Gas t)
  , iterations     :: Map CodeLocation (Int, [Expr EWord])
  -- ^ how many times we've visited a loc, and what the contents of the stack were when we were there last
  , constraints    :: [Prop]
  , config         :: RuntimeConfig
  , forks          :: Seq ForkState
  , currentFork    :: Int
  , labels         :: Map Addr Text
  }
  deriving (Generic)

data ForkState = ForkState
  { env :: Env
  , block :: Block
  , cache :: Cache
  , urlOrAlias :: String
  }
  deriving (Show, Generic)

deriving instance Show (VM Symbolic s)
deriving instance Show (VM Concrete s)

-- | Alias for the type of e.g. @exec1@.
type EVM (t :: VMType) s a = StateT (VM t s) (ST s) a

-- | The VM base state (i.e. should new contracts be created with abstract balance / storage?)
data BaseState
  = EmptyBase
  | AbstractBase
  deriving (Show)

-- | Configuration options that need to be consulted at runtime
data RuntimeConfig = RuntimeConfig
  { allowFFI :: Bool
  , overrideCaller :: Maybe (Expr EAddr)
  , resetCaller :: Bool
  , baseState :: BaseState
  }
  deriving (Show)

-- | An entry in the VM's "call/create stack"
data Frame (t :: VMType) s = Frame
  { context :: FrameContext
  , state   :: FrameState t s
  }

deriving instance Show (Frame Symbolic s)
deriving instance Show (Frame Concrete s)

-- | Call/create info
data FrameContext
  = CreationContext
    { address         :: Expr EAddr
    , codehash        :: Expr EWord
    , createreversion :: Map (Expr EAddr) Contract
    , substate        :: SubState
    }
  | CallContext
    { target        :: Expr EAddr
    , context       :: Expr EAddr
    , offset        :: Expr EWord
    , size          :: Expr EWord
    , codehash      :: Expr EWord
    , abi           :: Maybe W256
    , calldata      :: Expr Buf
    , callreversion :: Map (Expr EAddr) Contract
    , subState      :: SubState
    }
  deriving (Eq, Ord, Show, Generic)

-- | The "accrued substate" across a transaction
data SubState = SubState
  { selfdestructs       :: [Expr EAddr]
  , touchedAccounts     :: [Expr EAddr]
  , accessedAddresses   :: Set (Expr EAddr)
  , accessedStorageKeys :: Set (Expr EAddr, W256)
  , refunds             :: [(Expr EAddr, Word64)]
  -- in principle we should include logs here, but do not for now
  }
  deriving (Eq, Ord, Show)

-- | The "registers" of the VM along with memory and data stack
data FrameState (t :: VMType) s = FrameState
  { contract     :: Expr EAddr
  , codeContract :: Expr EAddr
  , code         :: ContractCode
  , pc           :: {-# UNPACK #-} !Int
  , stack        :: [Expr EWord]
  , memory       :: Memory s
  , memorySize   :: Word64
  , calldata     :: Expr Buf
  , callvalue    :: Expr EWord
  , caller       :: Expr EAddr
  , gas          :: !(Gas t)
  , returndata   :: Expr Buf
  , static       :: Bool
  }
  deriving (Generic)

deriving instance Show (FrameState Symbolic s)
deriving instance Show (FrameState Concrete s)

data Memory s
  = ConcreteMemory (MutableMemory s)
  | SymbolicMemory !(Expr Buf)

instance Show (Memory s) where
  show (ConcreteMemory _) = "<can't show mutable memory>"
  show (SymbolicMemory m) = show m

type MutableMemory s = STVector s Word8

-- | The state that spans a whole transaction
data TxState = TxState
  { gasprice    :: W256
  , gaslimit    :: Word64
  , priorityFee :: W256
  , origin      :: Expr EAddr
  , toAddr      :: Expr EAddr
  , value       :: Expr EWord
  , substate    :: SubState
  , isCreate    :: Bool
  , txReversion :: Map (Expr EAddr) Contract
  }
  deriving (Show)

-- | Various environmental data
data Env = Env
  { contracts      :: Map (Expr EAddr) Contract
  , chainId        :: W256
  , freshAddresses :: Int
  , freshGasVals :: Int
  }
  deriving (Show, Generic)

-- | Data about the block
data Block = Block
  { coinbase    :: Expr EAddr
  , timestamp   :: Expr EWord
  , number      :: W256
  , prevRandao  :: W256
  , gaslimit    :: Word64
  , baseFee     :: W256
  , maxCodeSize :: W256
  , schedule    :: FeeSchedule Word64
  } deriving (Show, Generic)

-- | Full contract state
data Contract = Contract
  { code        :: ContractCode
  , storage     :: Expr Storage
  , tStorage    :: Expr Storage
  , origStorage :: Expr Storage
  , balance     :: Expr EWord
  , nonce       :: Maybe W64
  , codehash    :: Expr EWord
  , opIxMap     :: SV.Vector Int
  , codeOps     :: V.Vector (Int, Op)
  , external    :: Bool
  }
  deriving (Show, Eq, Ord)

class VMOps (t :: VMType) where
  burn' :: Gas t -> EVM t s () -> EVM t s ()
  -- TODO: change to EvmWord t
  burnExp :: Expr EWord -> EVM t s () -> EVM t s ()
  burnSha3 :: Expr EWord -> EVM t s () -> EVM t s ()
  burnCalldatacopy :: Expr EWord -> EVM t s () -> EVM t s ()
  burnCodecopy :: Expr EWord -> EVM t s () -> EVM t s ()
  burnExtcodecopy :: Expr EAddr -> Expr EWord -> EVM t s () -> EVM t s ()
  burnReturndatacopy :: Expr EWord -> EVM t s () -> EVM t s ()
  burnLog :: Expr EWord -> Word8 -> EVM t s () -> EVM t s ()

  initialGas :: Gas t
  ensureGas :: Word64 -> EVM t s () -> EVM t s ()
  -- TODO: change to EvmWord t
  gasTryFrom :: Expr EWord -> Either () (Gas t)

  -- Gas cost of create, including hash cost if needed
  costOfCreate :: FeeSchedule Word64 -> Gas t -> Expr EWord -> Bool -> (Gas t, Gas t)

  costOfCall
    :: FeeSchedule Word64 -> Bool -> Expr EWord -> Gas t -> Gas t -> Expr EAddr
    -> (Word64 -> Word64 -> EVM t s ()) -> EVM t s ()

  reclaimRemainingGasAllowance :: VM t s -> EVM t s ()
  payRefunds :: EVM t s ()
  pushGas :: EVM t s ()
  enoughGas :: Word64 -> Gas t -> Bool
  subGas :: Gas t -> Word64 -> Gas t
  toGas :: Word64 -> Gas t

  whenSymbolicElse :: EVM t s a -> EVM t s a -> EVM t s a

  partial :: PartialExec -> EVM t s ()
  branch :: Expr EWord -> (Bool -> EVM t s ()) -> EVM t s ()

-- Bytecode Representations ------------------------------------------------------------------------


-- | A unique id for a given pc
type CodeLocation = (Expr EAddr, Int)

-- | The cache is data that can be persisted for efficiency:
-- any expensive query that is constant at least within a block.
data Cache = Cache
  { fetched :: Map Addr Contract
  , path    :: Map (CodeLocation, Int) Bool
  } deriving (Show, Generic)

instance Semigroup Cache where
  a <> b = Cache
    { fetched = Map.unionWith unifyCachedContract a.fetched b.fetched
    , path = mappend a.path b.path
    }

instance Monoid Cache where
  mempty = Cache { fetched = mempty
                 , path = mempty
                 }

-- only intended for use in Cache merges, where we expect
-- everything to be Concrete
unifyCachedContract :: Contract -> Contract -> Contract
unifyCachedContract a b = a { storage = merged }
  where merged = case (a.storage, b.storage) of
                   (ConcreteStore sa, ConcreteStore sb) ->
                     ConcreteStore (mappend sa sb)
                   _ -> a.storage


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
  = UnknownCode (Expr EAddr)       -- ^ Fully abstract code, keyed on an address to give consistent results for e.g. extcodehash
  | InitCode ByteString (Expr Buf) -- ^ "Constructor" code, during contract creation
  | RuntimeCode RuntimeCode        -- ^ "Instance" code, after contract creation
  deriving (Show, Eq, Ord)

-- | We have two variants here to optimize the fully concrete case.
-- ConcreteRuntimeCode just wraps a ByteString
-- SymbolicRuntimeCode is a fixed length vector of potentially symbolic bytes, which lets us handle symbolic pushdata (e.g. from immutable variables in solidity).
data RuntimeCode
  = ConcreteRuntimeCode ByteString
  | SymbolicRuntimeCode (V.Vector (Expr Byte))
  deriving (Show, Eq, Ord)

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
data TraceContext = TraceContext
  { traces :: Forest Trace
  , contracts :: Map (Expr EAddr) Contract
  , labels :: Map Addr Text
  }
  deriving (Eq, Ord, Show, Generic)

instance Semigroup TraceContext where
  (TraceContext a b c) <> (TraceContext d e f) = TraceContext (a <> d) (b <> e) (c <> f)
instance Monoid TraceContext where
  mempty = TraceContext mempty mempty mempty


-- VM Initialization -------------------------------------------------------------------------------


-- | A specification for an initial VM state
data VMOpts (t :: VMType) = VMOpts
  { contract :: Contract
  , otherContracts :: [(Expr EAddr, Contract)]
  , calldata :: (Expr Buf, [Prop])
  , baseState :: BaseState
  , value :: Expr EWord
  , priorityFee :: W256
  , address :: Expr EAddr
  , caller :: Expr EAddr
  , origin :: Expr EAddr
  , gas :: Gas t
  , gaslimit :: Word64
  , number :: W256
  , timestamp :: Expr EWord
  , coinbase :: Expr EAddr
  , prevRandao :: W256
  , maxCodeSize :: W256
  , blockGaslimit :: Word64
  , gasprice :: W256
  , baseFee :: W256
  , schedule :: FeeSchedule Word64
  , chainId :: W256
  , create :: Bool
  , txAccessList :: Map (Expr EAddr) [W256]
  , allowFFI :: Bool
  }

deriving instance Show (VMOpts Symbolic)
deriving instance Show (VMOpts Concrete)


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
  | OpTLoad
  | OpTStore
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
  parseJSON (JSON.String x) = case BS16.decodeBase16Untyped (T.encodeUtf8 x) of
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

instance Read W64 where
  readsPrec _ "0x" = [(0, "")]
  readsPrec n s = first W64 <$> readsPrec n s

instance Show W64 where
  showsPrec _ s = ("0x" ++) . showHex s

instance JSON.ToJSON W64 where
  toJSON x = JSON.String  $ T.pack $ show x

instance FromJSON W64 where
  parseJSON v = do
    s <- T.unpack <$> parseJSON v
    case reads s of
      [(x, "")]  -> return x
      _          -> fail $ "invalid hex word (" ++ s ++ ")"


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
maybeLitWord (WAddr (LitAddr w)) = Just (into w)
maybeLitWord _ = Nothing

maybeLitAddr :: Expr EAddr -> Maybe Addr
maybeLitAddr (LitAddr a) = Just a
maybeLitAddr _ = Nothing

maybeConcreteStore :: Expr Storage -> Maybe (Map W256 W256)
maybeConcreteStore (ConcreteStore s) = Just s
maybeConcreteStore _ = Nothing


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
  Cereal.encode (a, b, c, d)

word160Bytes :: Addr -> ByteString
word160Bytes (Addr (Word160 a (Word128 b c))) =
  Cereal.encode (a, b, c)

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

{- HLINT ignore internalError -}
internalError:: HasCallStack => [Char] -> a
internalError m = error $ "Internal Error: " ++ m ++ " -- " ++ (prettyCallStack callStack)

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

-- |'paddedShowHex' displays a number in hexadecimal and pads the number
-- with 0 so that it has a minimum length of @w@.
paddedShowHex :: (Show a, Integral a) => Int -> a -> String
paddedShowHex w n = pad ++ str
    where
     str = showHex n ""
     pad = replicate (w - length str) '0'

untilFixpoint :: Eq a => (a -> a) -> a -> a
untilFixpoint f a = if f a == a
                    then a
                    else untilFixpoint f (f a)

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
makeFieldLabelsNoPrefix ''RuntimeConfig
