{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EVM.Props where

import Control.Monad.Except
import Data.Functor.Identity
import Data.ByteString (ByteString)
import Data.Kind
import Data.List
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as L
import Data.Text.Lazy.Builder
import Data.Set (Set)
import Data.Set qualified as Set
import Data.SExpresso.SExpr
import Data.SExpresso.Print.Lazy
import Data.Typeable
import Witch

import EVM.Types qualified as E (Expr(..), EType(..), W256(..))
import EVM.Expr qualified as Expr
import EVM.Traversals (foldExpr)


-- Expr Test Instance ------------------------------------------------------------------------------


test :: Set (Prop E.Expr)
test = Set.fromList
  [ Eq (E.Lit 1) (E.Lit 1)
  , Eq (E.ReadWord (E.Var "hi") (E.AbstractBuf "b")) (E.Lit 0)
  , Eq (E.AbstractBuf "b") (E.ConcreteBuf "")
  ]

pattern Word :: SMT
pattern Word = Sexp [A "_", A "BitVec", A "256"]

pattern Byte :: SMT
pattern Byte = Sexp [A "_", A "BitVec", A "8"]

pattern Buf :: SMT
pattern Buf = Sexp [A "Array", Word, Byte]

pattern Store :: SMT
pattern Store = Sexp [A "Array", Word, Word]

pattern EmptyBuf :: SMT
pattern EmptyBuf = AsConst Buf (A "#x00")

pattern AsConst :: SMT -> SMT -> SMT
pattern AsConst t v = Sexp [Sexp [A "as", A "const", t], v]

pattern LitBV :: E.W256 -> SMT
pattern LitBV v <- Sexp [A "_", BVVal (read -> v), A "256"] where
  LitBV v = Sexp [A "_", A ("bv" <> (T.pack $ show (into v :: Integer))), A "256"]

pattern BVVal :: String -> SMT
pattern BVVal v <- A (T.unpack -> 'b':'v':v)

instance ToSMT (E.Expr a) where
  toSMT x = case x of
    E.Lit a -> LitBV a
    E.Var a -> A a
    E.AbstractBuf a -> A a
    E.GT a b -> ebool "bvugt" [a, b]
    E.LT a b -> ebool "bvult" [a, b]
    E.Not a -> ebool "bvnot" [a]
    E.SHL a b -> op "bvshl" [a, b]
    E.Add a b -> op "bvadd" [a, b]
    E.ConcreteBuf "" -> EmptyBuf
    E.ReadByte idx buf -> readByte idx buf
    E.ReadWord idx buf -> readWord idx buf
    e -> error $ "TODO: " <> show e
    where
      ebool n args = Sexp [A "ite", op n args, A "1", A "0"]

readByte :: E.Expr E.EWord -> E.Expr E.Buf -> SMT
readByte idx buf = Sexp [A "select", toSMT buf, toSMT idx]

readWord :: E.Expr E.EWord -> E.Expr E.Buf -> SMT
readWord idx buf
  = Sexp
      [ A "concat"
      , readByte idx buf
      , readByte (Expr.add idx (E.Lit 1)) buf
      , readByte (Expr.add idx (E.Lit 2)) buf
      , readByte (Expr.add idx (E.Lit 3)) buf
      , readByte (Expr.add idx (E.Lit 4)) buf
      , readByte (Expr.add idx (E.Lit 5)) buf
      , readByte (Expr.add idx (E.Lit 6)) buf
      , readByte (Expr.add idx (E.Lit 7)) buf
      , readByte (Expr.add idx (E.Lit 8)) buf
      , readByte (Expr.add idx (E.Lit 9)) buf
      , readByte (Expr.add idx (E.Lit 10)) buf
      , readByte (Expr.add idx (E.Lit 11)) buf
      , readByte (Expr.add idx (E.Lit 12)) buf
      , readByte (Expr.add idx (E.Lit 13)) buf
      , readByte (Expr.add idx (E.Lit 14)) buf
      , readByte (Expr.add idx (E.Lit 15)) buf
      , readByte (Expr.add idx (E.Lit 16)) buf
      , readByte (Expr.add idx (E.Lit 17)) buf
      , readByte (Expr.add idx (E.Lit 18)) buf
      , readByte (Expr.add idx (E.Lit 19)) buf
      , readByte (Expr.add idx (E.Lit 20)) buf
      , readByte (Expr.add idx (E.Lit 21)) buf
      , readByte (Expr.add idx (E.Lit 22)) buf
      , readByte (Expr.add idx (E.Lit 23)) buf
      , readByte (Expr.add idx (E.Lit 24)) buf
      , readByte (Expr.add idx (E.Lit 25)) buf
      , readByte (Expr.add idx (E.Lit 26)) buf
      , readByte (Expr.add idx (E.Lit 27)) buf
      , readByte (Expr.add idx (E.Lit 28)) buf
      , readByte (Expr.add idx (E.Lit 29)) buf
      , readByte (Expr.add idx (E.Lit 30)) buf
      , readByte (Expr.add idx (E.Lit 31)) buf
      ]

instance ToOrder (E.Expr E.EWord) where
  geq a b = op "bvuge" [a, b]
  leq a b = op "bvule" [a, b]
  gt a b = op "bvugt" [a, b]
  lt a b = op "bvult" [a, b]

op :: ToSMT e => Text -> [e] -> SMT
op n args = Sexp (A n : fmap toSMT args)

parseWord :: SMT -> Either Text (LitVal E.EWord)
parseWord = \case
  Sexp [Sexp [A _, A v]] -> case T.stripPrefix "#x" v of
    Just w -> Right . WordVal . read . T.unpack $ w
    Nothing -> Left (msg v)
  s -> Left (msg s)
  where
    msg s = "unable to parse: " <> (T.pack . show $ s) <> " into a word"

parseBuf :: SMT -> Either Text (LitVal E.Buf)
parseBuf = \case
  Sexp [Sexp [A _, EmptyBuf]] -> Right $ BufVal ""
  s -> Left $ "unable to parse: " <> (T.pack . show $ s) <> "into a buffer"

parseStore :: SMT -> Either Text (LitVal E.Storage)
parseStore = undefined

parseByte :: SMT -> Either Text (LitVal E.Byte)
parseByte = undefined

data LitVal e where
  WordVal :: E.W256 -> LitVal E.EWord
  BufVal :: ByteString -> LitVal E.Buf

deriving instance Eq (LitVal e)
deriving instance Ord (LitVal e)
deriving instance Show (LitVal e)

instance ModelFns E.Expr where
  data FreeVar E.Expr = forall a . Typeable a => FreeVar Text (E.Expr a)
  data Assignment E.Expr = forall a . Typeable a => Assignment (E.Expr a) (LitVal a)

  frees = foldExpr go mempty
    where
      go :: E.Expr a -> Set (FreeVar E.Expr)
      go = \case
        v@(E.Var a) -> Set.singleton (FreeVar a v)
        v@(E.AbstractBuf a) -> Set.singleton (FreeVar a v)
        v@(E.AbstractStore) -> Set.singleton (FreeVar "abstractStore" v)
        _ -> mempty

  extract getVal (FreeVar nm (e :: E.Expr t))
    | Just Refl <- eqT @t @E.EWord = go parseWord
    | Just Refl <- eqT @t @E.Byte = go parseByte
    | Just Refl <- eqT @t @E.Buf = go parseBuf
    | Just Refl <- eqT @t @E.Storage = go parseStore
    | otherwise = error $ "no smt encoding for: " <> show e
    where
      go parseFn = runExceptT $ do
        raw <- ExceptT . getVal $ (A nm)
        val <- ExceptT . pure . parseFn $ raw
        pure (Assignment e val)

  declare (FreeVar nm (e :: E.Expr t))
    | Just Refl <- eqT @t @E.EWord = declareConst nm Word
    | Just Refl <- eqT @t @E.Byte = declareConst nm Byte
    | Just Refl <- eqT @t @E.Buf = declareConst nm Buf
    | Just Refl <- eqT @t @E.Storage = declareConst nm Store
    | otherwise = error $ "no smt encoding for: " <> show e

deriving instance Show (FreeVar E.Expr)
instance Eq (FreeVar E.Expr) where
  FreeVar nm0 (e0 :: E.Expr t0) == FreeVar nm1 (e1 :: E.Expr t1)
    = case eqT @t0 @t1 of
        Just Refl -> nm0 == nm1 && e0 == e1
        Nothing -> False
instance Ord (FreeVar E.Expr) where
  FreeVar nm0 (e0 :: E.Expr t0) <= FreeVar nm1 (e1 :: E.Expr t1)
    = case eqT @t0 @t1 of
        Just Refl -> nm0 <= nm1 && e0 <= e1
        Nothing -> False

deriving instance Show (Assignment E.Expr)
instance Eq (Assignment E.Expr) where
  Assignment (e0 :: E.Expr t0) v0 == Assignment (e1 :: E.Expr t1) v1
    = case eqT @t0 @t1 of
        Just Refl -> e0 == e1 && v0 == v1
        Nothing -> False
instance Ord (Assignment E.Expr) where
  Assignment (e0 :: E.Expr t0) v0 <= Assignment (e1 :: E.Expr t1) v1
    = case eqT @t0 @t1 of
        Just Refl -> e0 <= e1 && v0 <= v1
        Nothing -> False


-- Serialization -------------------------------------------------------------------------------


type SMT = Sexp Text

newtype Script = Script [SMT]
  deriving (Show, Eq)

deriving instance (Ord SMT)

serialize :: SMT -> Builder
serialize = flatPrintBuilder (mkPrinter id)

asText :: SMT -> Text
asText = L.toStrict . toLazyText . serialize

formatScript :: Script -> Text
formatScript (Script cmds)
  = L.toStrict
  . toLazyText
  . mconcat
  . intersperse (fromText "\n")
  $ fmap serialize cmds

-- | Types that can be encoded as expressions in smt
class ToSMT e where
  toSMT :: e -> SMT

-- | Types that have a comparable encoding in smt
class ToSMT e => ToOrder e where
  geq :: e -> e -> SMT
  leq :: e -> e -> SMT
  lt :: e -> e -> SMT
  gt :: e -> e -> SMT

-- | Types that allow script construction and model extraction
class (Ord (FreeVar f), Ord (Assignment f)) => ModelFns (f :: k -> Type) where
  data FreeVar f :: Type
  data Assignment f :: Type
  frees :: f e -> Set (FreeVar f)
  declare :: FreeVar f -> SMT
  extract :: (SMT -> IO (Either Text SMT)) -> FreeVar f -> IO (Either Text (Assignment f))

declareConst :: Text -> SMT -> SMT
declareConst nm ty = Sexp [A "declare-const", A nm, ty]

assert :: SMT -> SMT
assert p = Sexp [A "assert", p]

mkScript :: ModelFns f => Set (Prop f) -> Script
mkScript ps = Script $ Set.toList (decls ps) <> (Set.toList . Set.map (assert . toSMT) $ ps)

decls :: ModelFns f => Set (Prop f) -> Set SMT
decls (Set.toList -> ps) = mconcat $ fmap (foldInner (Set.map declare . frees)) ps

free :: ModelFns f => Set (Prop f) -> Set (FreeVar f)
free (Set.toList -> ps) = mconcat $ fmap (foldInner frees) ps


-- Core SMT Theories -------------------------------------------------------------------------------


data Prop (f :: k -> Type) where
  T    :: Prop f
  F    :: Prop f
  Not  :: Prop f -> Prop f
  Impl :: Prop f -> Prop f -> Prop f
  And  :: Prop f -> Prop f -> Prop f
  Or   :: Prop f -> Prop f -> Prop f
  Xor  :: Prop f -> Prop f -> Prop f
  Eq   :: (InnerCs f t, ToSMT (f t)) => f t -> f t -> Prop f
  Neq  :: (InnerCs f t, ToSMT (f t)) => f t -> f t -> Prop f
  Gt   :: (InnerCs f t, ToOrder (f t)) => f t -> f t -> Prop f
  Lt   :: (InnerCs f t, ToOrder (f t)) => f t -> f t -> Prop f
  Leq  :: (InnerCs f t, ToOrder (f t)) => f t -> f t -> Prop f
  Geq  :: (InnerCs f t, ToOrder (f t)) => f t -> f t -> Prop f

type InnerCs f t = (Typeable (f t), Eq (f t), Ord (f t), Show (f t))

deriving instance Show (Prop f)

instance Eq (Prop f) where
  T == T = True
  F == F = True
  Not a == Not b = a == b
  Impl a b == Impl c d = a == c && b == d
  And a b == And c d = a == c && b == d
  Or a b == Or c d = a == c && b == d
  Xor a b == Xor c d = a == c && b == d
  Eq (a :: e0) b == Eq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  Neq (a :: e0) b == Neq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  Gt (a :: e0) b == Gt (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  Lt (a :: e0) b == Lt (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  Leq (a :: e0) b == Leq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  Geq (a :: e0) b == Geq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  _ == _ = False

instance Ord (Prop f) where
  T <= T = True
  F <= F = True
  Not a <= Not b = a <= b
  Impl a b <= Impl c d = a <= c && b <= d
  And a b <= And c d = a <= c && b <= d
  Or a b <= Or c d = a <= c && b <= d
  Xor a b <= Xor c d = a <= c && b <= d
  Eq (a :: e0) b <= Eq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  Neq (a :: e0) b <= Neq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  Gt (a :: e0) b <= Gt (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  Lt (a :: e0) b <= Lt (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  Leq (a :: e0) b <= Leq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  Geq (a :: e0) b <= Geq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  _ <= _ = False

instance ToSMT (Prop f) where
  toSMT = \case
    T -> A "true"
    F -> A "false"
    Not e -> Sexp [A "not", toSMT e]
    Impl a b -> Sexp [A "=>", toSMT a, toSMT b]
    And a b -> Sexp [A "and", toSMT a, toSMT b]
    Or a b -> Sexp [A "or", toSMT a, toSMT b]
    Xor a b -> Sexp [A "xor", toSMT a, toSMT b]
    Eq a b -> Sexp [A "=", toSMT a, toSMT b]
    Neq a b -> Sexp [A "distinct", toSMT a, toSMT b]
    Gt a b -> gt a b
    Lt a b -> lt a b
    Geq a b -> geq a b
    Leq a b -> leq a b


-- Traversal ---------------------------------------------------------------------------------------


foldInner :: Monoid b => (forall t . f t -> b) -> Prop f -> b
foldInner f expr = runIdentity (foldInnerM (Identity . f) expr)

foldInnerM :: (Monad m, Monoid b) => (forall t . f t -> m b) -> Prop f -> m b
foldInnerM f = \case
  T -> pure mempty
  F -> pure mempty
  Not a -> foldInnerM f a
  Impl a b -> do
    a' <- foldInnerM f a
    b' <- foldInnerM f b
    pure (a' <> b')
  And a b -> do
    a' <- foldInnerM f a
    b' <- foldInnerM f b
    pure (a' <> b')
  Or a b -> do
    a' <- foldInnerM f a
    b' <- foldInnerM f b
    pure (a' <> b')
  Xor a b -> do
    a' <- foldInnerM f a
    b' <- foldInnerM f b
    pure (a' <> b')
  Eq a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
  Neq a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
  Gt a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
  Lt a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
  Geq a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
  Leq a b -> do
    a' <- f a
    b' <- f b
    pure (a' <> b')
