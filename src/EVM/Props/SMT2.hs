{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module EVM.Props.SMT2 where

import Data.Kind
import Data.Typeable
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Hashable
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Map (Map)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Word (Word8, Word64)
import EVM.Types (Expr(..), EType(..), W256(..))
import EVM.Traversals
import Witch

type Err = Either Text

-- constraint to allow injection of a singleton from a known type context
class Repr (f :: k -> Type) (ctx :: k) where
  repr :: f ctx

-- s-expressions
data SMT = A Text | L [SMT]
  deriving (Show, Eq)

-- | The result of a call to (check-sat)
data CheckSatResult
  = Sat (HashSet Assignment)
  | Unsat
  | Unknown
  | Error Text
  deriving (Eq)


-- Public Interface --------------------------------------------------------------------------------


class Monad m => Solvers m where
  satisfiable :: Propositional a => HashSet a -> m CheckSatResult

-- | encode a term of arbitrary type to smt
class ToSMT a where
  toSMT :: a -> SMT

-- | things that can be given to (assert) as an argument
class ToSMT a => Propositional a where
  mkassert :: a -> SMT
  mkassert e = L [A "assert", toSMT e]

-- | things that can have their models auto generated
class (Eq (LitVal t), ToSMT (f t)) => Encoding (f :: k -> Type) (s :: k -> Type) (t :: k) | t -> f, t -> s where
  -- | indexed wrapper for literal values
  type LitVal :: k -> Type
  -- | encode the type represented by the given singleton into smt
  mkty :: Repr s t => s t -> SMT
  -- | parse an smt value into a literal matching the given singleton type
  parse :: Repr s t => s t -> SMT -> Err (LitVal t)
  -- | walk the expression and return the set of free variables
  frees :: f t -> HashSet FreeVar

-- | type erasing wrapper for free variables
data FreeVar where
  FreeVar :: (Hashable (s t), Repr s t, Typeable (s t))
          => s t -> Text -> FreeVar

-- | type erasing wrapper for assignments in sat models
data Assignment where
  Assign :: forall s t . (Eq (LitVal t), Show (s t), Show (LitVal t), Hashable (s t), Hashable (LitVal t), Repr s t, Typeable (s t))
         => s t -> Text -> LitVal t -> Assignment


-- Implementation for Expr -------------------------------------------------------------------------


pattern WordT :: SMT
pattern WordT = BitVecT 256

pattern ByteT :: SMT
pattern ByteT = BitVecT 8

pattern BufT :: SMT
pattern BufT = ArrayT WordT ByteT

pattern StoreT :: SMT
pattern StoreT = ArrayT WordT WordT


instance Encoding Expr STy (t :: EType) where
  type LitVal = Val

  mkty = \case
    SWord -> WordT
    SByte -> ByteT
    SBuf -> BufT
    SStorage -> StoreT

  frees = foldExpr go mempty
    where
      go = \case
        Var a -> HashSet.singleton $ FreeVar SWord a
        AbstractBuf a -> HashSet.singleton $ FreeVar SBuf a
        AbstractStore -> HashSet.singleton $ FreeVar SStorage "AbstractStore"
        _ -> mempty

  parse t s = case t of
    SWord -> atom VWord
    SByte -> atom VByte
    _ -> Left . T.pack $ "unable to parse values of type: " <> show t
    where
      atom :: Read a => (a -> Val t) -> Err (Val t)
      atom l = case s of
        A v -> case T.stripPrefix "#x" v of
          Just w -> Right . l . read . T.unpack $ w
          Nothing -> Left msg
        _ -> Left msg
      msg = "unable to parse " <> tshow s <> " into a " <> tshow t

data Val (t :: EType) where
  VWord    :: W256 -> Val EWord
  VByte    :: Word8 -> Val Byte
  VBuf     :: ByteString -> Val Buf
  VStorage :: Map W256 W256 -> Val Buf

deriving instance Eq (Val t)
deriving instance Show (Val t)

instance ToSMT (Expr a) where
  toSMT = \case
    Lit w -> LitBV 256 w
    Var a -> A a
    Add a b -> op "bvadd" [a, b]
    Sub a b -> op "bvsub" [a, b]
    ConcreteBuf bs -> toSMT bs
    WriteWord idx val b -> L [A "store", toSMT b, toSMT idx, toSMT val]
    ReadWord idx b -> L [A "select", toSMT b, toSMT idx]
    s -> error $ "toSMT: " <> show s

instance ToSMT ByteString where
  toSMT bytes = fst $ BS.foldl' write (AsConst BufT (A "#x00"), 0) bytes
    where
      write :: (SMT, Word64) -> Word8 -> (SMT, Word64)
      write (prev, idx) = \case
        0 -> (prev, idx + 1)
        byte -> ( L [A "store", prev, toSMT (LitByte byte), toSMT (Lit . into $ idx)] , idx + 1)

op :: ToSMT a => Text -> [a] -> SMT
op nm args = L (A nm : fmap toSMT args)


-- Some Useful Patterns ----------------------------------------------------------------------------


pattern AsConst :: SMT -> SMT -> SMT
pattern AsConst t v = L [L [A "as", A "const", t], v]

pattern LitBV :: (Read i, From i Integer) => Int -> i -> SMT
pattern LitBV sz v <- L [A "_", BVVal (read -> v), A (tread -> sz)] where
  LitBV sz v = L [A "_", A ("bv" <> tshow (into @Integer v)), A (tshow sz)]

pattern BVVal :: String -> SMT
pattern BVVal v <- A (T.unpack -> 'b':'v':v)

pattern BitVecT :: Int -> SMT
pattern BitVecT n <- L [A "_", A "BitVec", A (tread -> n)] where
  BitVecT n = L [A "_", A "BitVec", A (tshow n)] where

pattern ArrayT :: SMT -> SMT -> SMT
pattern ArrayT from to = L [A "Array", from, to]


-- Internals ---------------------------------------------------------------------------------------





-- EType Singleton ---------------------------------------------------------------------------------


data STy (a :: EType) where
  SWord :: STy EWord
  SByte :: STy Byte
  SBuf :: STy Buf
  SStorage :: STy Storage

deriving instance Eq (STy a)
deriving instance Show (STy a)

instance Repr STy EWord where repr = SWord
instance Repr STy Byte where repr = SByte
instance Repr STy Buf where repr = SBuf
instance Repr STy Storage where repr = SStorage

instance Hashable (STy t) where
  hashWithSalt s SWord = hashWithSalt s (0 :: Int)
  hashWithSalt s SByte = hashWithSalt s (1 :: Int)
  hashWithSalt s SBuf = hashWithSalt s (2 :: Int)
  hashWithSalt s SStorage = hashWithSalt s (3 :: Int)


-- Instances ---------------------------------------------------------------------------------------

instance Eq FreeVar where
  (FreeVar (s0 :: a) n0) == (FreeVar (s1 :: b) n1) = case eqT @a @b of
    Just Refl -> s0 == s1 && n0 == n1
    Nothing -> False

instance Eq Assignment where
  (Assign (s0 :: a) n0 v0) == (Assign (s1 :: b) n1 v1) = case eqT @a @b of
    Just Refl -> s0 == s1 && n0 == n1 && v0 == v1
    Nothing -> False

instance Hashable FreeVar where
  hashWithSalt s (FreeVar st n) = s `hashWithSalt` st `hashWithSalt` n

instance Hashable Assignment where
  hashWithSalt s (Assign st n v) = s `hashWithSalt` st `hashWithSalt` n `hashWithSalt` v

deriving instance Show Assignment

tshow :: Show a => a -> Text
tshow = T.pack . show

tread :: Read a => Text -> a
tread = read . T.unpack
