{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EVM.Props where

import Control.Monad
import Data.Functor.Identity
import Data.SExpresso.SExpr
import Data.SExpresso.Print.Lazy
import Data.Kind
import Data.List (intersperse)
import Data.Text (Text)
import Data.Text qualified as T
import qualified Data.Text.Lazy as L
import Data.Text.Lazy.Builder
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Typeable
import Witch

import EVM.Types qualified as E (Expr(..), EType(..), W256(..), toNum)
import EVM.Traversals (foldExpr)


-- Expr Test Instance ------------------------------------------------------------------------------


data HProp where
  P :: forall a . Typeable a => Prop (E.Expr a) -> HProp

instance ToSMT HProp where
  toSMT (P p) = toSMT p

instance Eq HProp where
  P (l :: Prop (E.Expr a)) == P (r :: Prop (E.Expr b))
    = case eqT @a @b of
        Just Refl -> l == r
        Nothing -> False

instance Ord HProp where
  P (l :: Prop (E.Expr a)) <= P (r :: Prop (E.Expr b))
    = case eqT @a @b of
        Just Refl -> l <= r
        Nothing -> False


test :: Set (HProp)
test = Set.fromList
  [ P $ Eq (E.Lit 0) (E.Lit 1)
  , P $ Gt (E.ReadWord (E.Var "hi") (E.AbstractBuf "b")) (E.Lit 1)
  , P $ Eq (E.AbstractBuf "b") (E.ConcreteBuf "")
  ]

serial :: Text
serial = L.toStrict
       . toLazyText
       . mconcat
       . intersperse (fromText "\n")
       . Set.toList
       $ Set.map (serialize . toSMT) test

op :: ToSMT e => Text -> [e] -> SMT
op n args = Sexp (A n : fmap toSMT args)

instance SmtOrder (E.Expr E.EWord) where
  geq a b = op "bvuge" [a, b]
  leq a b = op "bvule" [a, b]
  gt a b = op "bvugt" [a, b]
  lt a b = op "bvult" [a, b]

pattern Word :: SMT
pattern Word = Sexp [A "_", A "BitVec", A "256"]

pattern Byte :: SMT
pattern Byte = Sexp [A "_", A "BitVec", A "8"]

pattern Buf :: SMT
pattern Buf = Sexp [A "Array", Word, Byte]

pattern Store :: SMT
pattern Store = Sexp [A "Array", Word, Word]

pattern EmptyBuf :: SMT
pattern EmptyBuf = Sexp [Sexp [A "as", A "const", Buf], A "#b00000000"]

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
    E.ReadWord idx b -> Sexp [A "select", toSMT b, toSMT idx ]
    e -> error $ "TODO: " <> show e
    where
      ebool n args = Sexp [A "ite", op n args, A "1", A "0"]


-- Serialization -------------------------------------------------------------------------------


type SMT = Sexp Text

serialize :: SMT -> Builder
serialize = flatPrintBuilder (mkPrinter id)

deriving instance (Ord SMT)

class ToSMT e where
  toSMT :: e -> SMT

data LitVal (t :: E.EType) where
  WordLit :: E.W256 -> LitVal E.EWord

data FreeVar where
  FreeVar :: forall ty . Typeable ty => E.Expr ty -> Text -> FreeVar

data Assignment where
  Assignment :: forall ty. Typeable ty => E.Expr ty -> LitVal ty -> Assignment

deriving instance Eq (LitVal a)
deriving instance Ord (LitVal a)

data Some (f :: k -> Type) = forall x . Typeable x => Some (f x)

instance Eq (Some E.Expr) where
  (Some (e0 :: E.Expr t0)) == (Some (e1 :: E.Expr t1)) = case eqT @t0 @t1 of
    Just Refl -> e0 == e1
    Nothing -> False

instance Ord (Some E.Expr) where
  (Some (e0 :: E.Expr t0)) <= (Some (e1 :: E.Expr t1)) = case eqT @t0 @t1 of
    Just Refl -> e0 <= e1
    Nothing -> False

instance Eq FreeVar where
  (FreeVar (e0 :: E.Expr t0) nm0) == (FreeVar (e1 :: E.Expr t1) nm1)
    = case eqT @t0 @t1 of
        Just Refl -> e0 == e1 && nm0 == nm1
        Nothing -> False

instance Ord FreeVar where
  compare (FreeVar (e0 :: E.Expr t0) nm0) (FreeVar (e1 :: E.Expr t1) nm1) =
    case eqT @t0 @t1 of
      Just Refl -> compare (compare e0 e1) (compare nm0 nm1)
      Nothing -> compare (E.toNum e0) (E.toNum e0)

instance Eq Assignment where
  (Assignment (e0 :: E.Expr t0) nm0) == (Assignment (e1 :: E.Expr t1) nm1)
    = case eqT @t0 @t1 of
        Just Refl -> e0 == e1 && nm0 == nm1
        Nothing -> False

instance Ord Assignment where
  compare (Assignment (e0 :: E.Expr t0) nm0) (Assignment (e1 :: E.Expr t1) nm1) =
    case eqT @t0 @t1 of
      Just Refl -> compare (compare e0 e1) (compare nm0 nm1)
      Nothing -> compare (E.toNum e0) (E.toNum e0)

class MkModel (f :: k -> Type) where
  type LitRep f :: k -> Type
  freeVars :: f e -> Map Text (Some f)
  extractModel :: Map Text (Some f) -> IO (Map (Some f) (Some (LitRep f)))
  declareVar :: Text -> Some f -> SMT

instance MkModel E.Expr where
  type LitRep (E.Expr) = LitVal

  freeVars = foldExpr go mempty
    where
      go :: E.Expr a -> Map Text (Some E.Expr)
      go = \case
        v@(E.Var n) -> Map.singleton n (Some v)
        _ -> mempty

  extractModel (Map.toList -> fvs) = do
      assigns <- forM fvs $ \(nm, Some e) -> do
        raw <- getValue nm
        pure $ case e of
                  E.Var _ -> (Some e, Some $ parseWord raw)
                  _ -> undefined
      pure $ Map.fromList assigns

  declareVar nm (Some (e :: E.Expr ty))
    | Just Refl <- eqT @ty @E.EWord = declareConst nm Word
    | Just Refl <- eqT @ty @E.Buf = declareConst nm Buf
    | Just Refl <- eqT @ty @E.Byte = declareConst nm Byte
    | Just Refl <- eqT @ty @E.Storage = declareConst nm Store
    | otherwise = error $ "no smt encoding for: " <> show e

data SolverGroup
data CheckSatResult

class CheckSat e where
  checkSat :: SolverGroup -> Set (Prop e) -> IO CheckSatResult

mkScript :: forall f e . (MkModel f, ToSMT (f e)) => Set (Prop (f e)) -> Builder
mkScript (Set.toList -> ps) =  mconcat
                            . intersperse (fromText "\n")
                            . fmap serialize $ script
  where
    frees :: Map Text (Some f)
    frees = mconcat $ fmap (foldProp freeVars) ps

    decls :: [SMT]
    decls = fmap (uncurry declareVar) (Map.toList frees)

    script :: [SMT]
    script = decls <> fmap toSMT ps

getValue :: Text -> IO SMT
getValue = undefined

parseWord :: SMT -> LitVal E.EWord
parseWord = undefined

declareConst :: Text -> SMT -> SMT
declareConst nm ty = Sexp [A "declare-const", A nm, ty]


-- Core SMT Theories -------------------------------------------------------------------------------


data Prop e where
  T :: Prop e
  F :: Prop e
  Not :: Prop e -> Prop e
  Impl :: Prop e -> Prop e -> Prop e
  And :: Prop e -> Prop e -> Prop e
  Or :: Prop e -> Prop e -> Prop e
  Xor :: Prop e -> Prop e -> Prop e
  Eq :: e -> e -> Prop e
  Distinct :: e -> e -> Prop e
  Gt :: SmtOrder e => e -> e -> Prop e
  Lt :: SmtOrder e => e -> e -> Prop e
  Leq :: SmtOrder e => e -> e -> Prop e
  Geq :: SmtOrder e => e -> e -> Prop e

deriving instance Eq e => Eq (Prop e)
deriving instance Ord e => Ord (Prop e)

class SmtOrder e where
  geq :: e -> e -> SMT
  leq :: e -> e -> SMT
  lt :: e -> e -> SMT
  gt :: e -> e -> SMT

instance ToSMT e => ToSMT (Prop e) where
  toSMT = \case
    T -> A "true"
    F -> A "false"
    Not e -> Sexp [A "not", toSMT e]
    Impl a b -> Sexp [A "=>", toSMT a, toSMT b]
    And a b -> Sexp [A "and", toSMT a, toSMT b]
    Or a b -> Sexp [A "or", toSMT a, toSMT b]
    Xor a b -> Sexp [A "xor", toSMT a, toSMT b]
    Eq a b -> Sexp [A "=", toSMT a, toSMT b]
    Distinct a b -> Sexp [A "distinct", toSMT a, toSMT b]
    Gt a b -> gt a b
    Lt a b -> lt a b
    Geq a b -> geq a b
    Leq a b -> leq a b



-- Traversal ---------------------------------------------------------------------------------------


-- | Maps function over the smt ast
mapSMT :: (SMT -> SMT) -> SMT -> SMT
mapSMT f = \case
  SAtom t -> f (SAtom t)
  SList () args -> f $ Sexp (fmap (mapSMT f) args)

-- | Maps a (potentially type changing) pure function over the prop
mapProp :: forall a b . (Prop a -> Prop b) -> Prop a -> Prop b
mapProp f expr = runIdentity (mapPropM (Identity . f) expr)

-- | Maps a (potentially type changing) monadic action over the prop
mapPropM :: Monad m => forall a b . (Prop a -> m (Prop b)) -> Prop a -> m (Prop b)
mapPropM f = \case
  T -> f T
  F -> f F
  Not a -> do
    a' <- mapPropM f a
    pure $ Not a'
  Impl a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ Impl a' b'
  And a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ And a' b'
  Or a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ Or a' b'
  Xor a b -> do
    a' <- mapPropM f a
    b' <- mapPropM f b
    pure $ Or a' b'
  Gt a b -> f (Gt a b)
  Lt a b -> f (Lt a b)
  Geq a b -> f (Geq a b)
  Leq a b -> f (Leq a b)
  Eq a b -> f (Eq a b)
  Distinct a b -> f (Distinct a b)

foldProp :: Monoid b => (e -> b) -> Prop e -> b
foldProp f expr = runIdentity (foldPropM (Identity . f) expr)

foldPropM :: (Monad m, Monoid b) => (e -> m b) -> Prop e -> m b
foldPropM f = \case
  T -> pure mempty
  F -> pure mempty
  Not a -> foldPropM f a
  Impl a b -> do
    a' <- foldPropM f a
    b' <- foldPropM f b
    pure $ a' <> b'
  And a b -> do
    a' <- foldPropM f a
    b' <- foldPropM f b
    pure $ a' <> b'
  Or a b -> do
    a' <- foldPropM f a
    b' <- foldPropM f b
    pure $ a' <> b'
  Xor a b -> do
    a' <- foldPropM f a
    b' <- foldPropM f b
    pure $ a' <> b'
  Gt a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
  Lt a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
  Geq a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
  Leq a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
  Eq a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
  Distinct a b -> do
    a' <- f a
    b' <- f b
    pure $ a' <> b'
