{-# LANGUAGE DataKinds #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}

module EVM.Props where

import Data.Functor.Identity
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
import EVM.Traversals (foldExpr)


-- Expr Test Instance ------------------------------------------------------------------------------


test :: Set (Prop)
test = Set.fromList
  [ Eq (E.Lit 0) (E.Lit 1)
  , Gt (E.ReadWord (E.Var "hi") (E.AbstractBuf "b")) (E.Lit 1)
  , Eq (E.AbstractBuf "b") (E.ConcreteBuf "")
  ]

op :: ToSMT e => Text -> [e] -> SMT
op n args = Sexp (A n : fmap toSMT args)

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

instance ComparableEncoding (E.Expr E.EWord) where
  geq a b = op "bvuge" [a, b]
  leq a b = op "bvule" [a, b]
  gt a b = op "bvugt" [a, b]
  lt a b = op "bvult" [a, b]

data LitVal e where
  WordVal :: E.W256 -> LitVal E.EWord

parseWord :: SMT -> LitVal E.EWord
parseWord = undefined

parseBuf :: SMT -> LitVal E.Buf
parseBuf = undefined

parseStore :: SMT -> LitVal E.Storage
parseStore = undefined

parseByte :: SMT -> LitVal E.Byte
parseByte = undefined

getValue :: SMT -> IO SMT
getValue = undefined

instance Typeable e => ModelFns (E.Expr e) where
  data FreeVar (E.Expr e) = forall a . Typeable a => FreeVar Text (E.Expr a)
  data Assignment (E.Expr e) = forall a . Typeable a => Assignment (E.Expr a) (LitVal a)

  frees = foldExpr go mempty
    where
      go :: E.Expr a -> Set (FreeVar (E.Expr e))
      go = \case
        v@(E.Var a) -> Set.singleton (FreeVar a v)
        v@(E.AbstractBuf a) -> Set.singleton (FreeVar a v)
        v@(E.AbstractStore) -> Set.singleton (FreeVar "abstractStore" v)
        _ -> mempty

  extract (FreeVar nm (e :: E.Expr t))
    | Just Refl <- eqT @t @E.EWord = do
        raw <- getValue (A nm)
        pure $ Assignment e (parseWord raw)
    | Just Refl <- eqT @t @E.Byte = do
        raw <- getValue (A nm)
        pure $ Assignment e (parseByte raw)
    | Just Refl <- eqT @t @E.Buf = do
        raw <- getValue (A nm)
        pure $ Assignment e (parseBuf raw)
    | Just Refl <- eqT @t @E.Storage = do
        raw <- getValue (A nm)
        pure $ Assignment e (parseStore raw)
    | otherwise = error $ "no smt encoding for: " <> show e

  declare (FreeVar nm (e :: E.Expr t))
    | Just Refl <- eqT @t @E.EWord = declareConst nm Word
    | Just Refl <- eqT @t @E.Byte = declareConst nm Byte
    | Just Refl <- eqT @t @E.Buf = declareConst nm Buf
    | Just Refl <- eqT @t @E.Storage = declareConst nm Store
    | otherwise = error $ "no smt encoding for: " <> show e

instance Typeable e => (Eq (FreeVar (E.Expr e))) where
  FreeVar nm0 (e0 :: E.Expr t0) == FreeVar nm1 (e1 :: E.Expr t1)
    = case eqT @t0 @t1 of
        Just Refl -> nm0 == nm1 && e0 == e1
        Nothing -> False

instance Typeable e => (Ord (FreeVar (E.Expr e))) where
  FreeVar nm0 (e0 :: E.Expr t0) <= FreeVar nm1 (e1 :: E.Expr t1)
    = case eqT @t0 @t1 of
        Just Refl -> nm0 <= nm1 && e0 <= e1
        Nothing -> False


-- Serialization -------------------------------------------------------------------------------


type SMT = Sexp Text

newtype Script = Script [SMT]
  deriving (Show, Eq)

deriving instance (Ord SMT)

serialize :: SMT -> Builder
serialize = flatPrintBuilder (mkPrinter id)

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
class ToSMT e => ComparableEncoding e where
  geq :: e -> e -> SMT
  leq :: e -> e -> SMT
  lt :: e -> e -> SMT
  gt :: e -> e -> SMT

-- | Types that allow script construction and model extraction
class ToSMT e => ModelFns e where
  data FreeVar e :: Type
  data Assignment e :: Type
  frees :: e -> Set (FreeVar e)
  declare :: FreeVar e -> SMT
  extract :: FreeVar e -> IO (Assignment e)

declareConst :: Text -> SMT -> SMT
declareConst nm ty = Sexp [A "declare-const", A nm, ty]

mkScript :: Set Prop -> Script
mkScript ps = Script $ Set.toList (decls ps) <> (Set.toList . Set.map toSMT $ ps)

decls :: Set Prop -> Set SMT
decls (Set.toList -> ps) = mconcat $ fmap go ps
  where
    go :: Prop -> Set SMT
    go = \case
      T -> mempty
      F -> mempty
      Not a -> go a
      Impl a b -> go a <> go b
      And a b -> go a <> go b
      Or a b -> go a <> go b
      Xor a b -> go a <> go b
      Eq a b -> Set.map declare (frees a) <> Set.map declare (frees b)
      Distinct a b -> Set.map declare (frees a) <> Set.map declare (frees b)
      Gt a b -> Set.map declare (frees a) <> Set.map declare (frees b)
      Lt a b -> Set.map declare (frees a) <> Set.map declare (frees b)
      Geq a b -> Set.map declare (frees a) <> Set.map declare (frees b)
      Leq a b -> Set.map declare (frees a) <> Set.map declare (frees b)


-- Core SMT Theories -------------------------------------------------------------------------------


data Prop where
  T :: Prop
  F :: Prop
  Not :: Prop-> Prop
  Impl :: Prop -> Prop -> Prop
  And :: Prop -> Prop -> Prop
  Or :: Prop -> Prop -> Prop
  Xor :: Prop -> Prop -> Prop
  Eq :: (Eq e, Ord e, Typeable e, ModelFns e) => e -> e -> Prop
  Distinct :: (Eq e, Ord e, Typeable e, ModelFns e) => e -> e -> Prop
  Gt :: (Eq e, Ord e, Typeable e, ModelFns e, ComparableEncoding e) => e -> e -> Prop
  Lt :: (Eq e, Ord e, Typeable e, ModelFns e, ComparableEncoding e) => e -> e -> Prop
  Leq :: (Eq e, Ord e, Typeable e, ModelFns e, ComparableEncoding e) => e -> e -> Prop
  Geq :: (Eq e, Ord e, Typeable e, ModelFns e, ComparableEncoding e) => e -> e -> Prop

instance Eq Prop where
  T == T = True
  F == F = True
  Not a == Not b = a == b
  Impl a b == Impl c d = a == c && b == d
  And a b == And c d = a == c && b == d
  Eq (a :: e0) b == Eq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a == c && b == d
    Nothing -> False
  _ == _ = False

instance Ord Prop where
  T <= T = True
  F <= F = True
  Not a <= Not b = a <= b
  Eq (a :: e0) b <= Eq (c :: e1) d = case eqT @e0 @e1 of
    Just Refl -> a <= c && b <= d
    Nothing -> False
  _ <= _ = False

instance ToSMT Prop where
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

-- | Maps a pure function over the prop
mapProp :: (Prop -> Prop) -> Prop -> Prop
mapProp f expr = runIdentity (mapPropM (Identity . f) expr)

-- | Maps a monadic action over the prop
mapPropM :: Monad m => (Prop -> m Prop) -> Prop -> m Prop
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
