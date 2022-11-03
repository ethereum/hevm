{-# Language DataKinds #-}

{- |
    Module: EVM.Traversals
    Description: Generic traversal functions for Expr datatypes
-}
module EVM.Traversals where

import Prelude hiding (Word, LT, GT)

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import EVM.Types

foldProp :: forall b . Monoid b => (forall a . Expr a -> b) -> b -> Prop -> b
foldProp f acc p = acc <> (go p)
  where
    go :: Prop -> b
    go = \case
      PBool _ -> mempty
      PEq a b -> (foldExpr f mempty a) <> (foldExpr f mempty b)
      PLT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PLEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PNeg a -> go a
      PAnd a b -> go a <> go b
      POr a b -> go a <> go b

-- | Recursively folds a given function over a given expression
-- Recursion schemes do this & a lot more, but defining them over GADT's isn't worth the hassle
foldProp :: forall b . Monoid b => (forall a . Expr a -> b) -> b -> Prop -> b
foldProp f acc p = acc <> (go p)
  where
    go :: Prop -> b
    go = \case
      PBool _ -> mempty
      PEq a b -> (foldExpr f mempty a) <> (foldExpr f mempty b)
      PLT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGT a b -> foldExpr f mempty a <> foldExpr f mempty b
      PGEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PLEq a b -> foldExpr f mempty a <> foldExpr f mempty b
      PNeg a -> go a
      PAnd a b -> go a <> go b
      POr a b -> go a <> go b

-- | Recursively folds a given function over a given expression
-- Recursion schemes do this & a lot more, but defining them over GADT's isn't worth the hassle
foldExpr :: forall b c . Monoid b => (forall a . Expr a -> b) -> b -> Expr c -> b
foldExpr f acc expr = acc <> (go expr)
  where
    go :: forall a . Expr a -> b
    go = \case

      -- literals & variables

      e@(Lit _) -> f e
      e@(LitByte _) -> f e
      e@(Var _) -> f e
      e@(GVar _) -> f e

      -- bytes

      e@(IndexWord a b) -> f e <> (go a) <> (go b)
      e@(EqByte a b) -> f e <> (go a) <> (go b)

      e@(JoinBytes
        zero one two three four five six seven
        eight nine ten eleven twelve thirteen fourteen fifteen
        sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
        twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone)
        -> f e
        <> (go zero) <> (go one) <> (go two) <> (go three)
        <> (go four) <> (go five) <> (go six) <> (go seven)
        <> (go eight) <> (go nine) <> (go ten) <> (go eleven)
        <> (go twelve) <> (go thirteen) <> (go fourteen)
        <> (go fifteen) <> (go sixteen) <> (go seventeen)
        <> (go eighteen) <> (go nineteen) <> (go twenty)
        <> (go twentyone) <> (go twentytwo) <> (go twentythree)
        <> (go twentyfour) <> (go twentyfive) <> (go twentysix)
        <> (go twentyseven) <> (go twentyeight) <> (go twentynine)
        <> (go thirty) <> (go thirtyone)

      -- control flow

      e@Invalid -> f e
      e@SelfDestruct -> f e
      e@IllegalOverflow -> f e
      e@(Revert a) -> f e <> (go a)
      e@(Return a b) -> f e <> (go a) <> (go b)
      e@(ITE a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(TmpErr _) -> f e

      -- integers

      e@(Add a b) -> f e <> (go a) <> (go b)
      e@(Sub a b) -> f e <> (go a) <> (go b)
      e@(Mul a b) -> f e <> (go a) <> (go b)
      e@(Div a b) -> f e <> (go a) <> (go b)
      e@(SDiv a b) -> f e <> (go a) <> (go b)
      e@(Mod a b) -> f e <> (go a) <> (go b)
      e@(SMod a b) -> f e <> (go a) <> (go b)
      e@(AddMod a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(MulMod a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(Exp a b) -> f e <> (go a) <> (go b)
      e@(SEx a b) -> f e <> (go a) <> (go b)
      e@(Min a b) -> f e <> (go a) <> (go b)

      -- booleans

      e@(LT a b) -> f e <> (go a) <> (go b)
      e@(GT a b) -> f e <> (go a) <> (go b)
      e@(LEq a b) -> f e <> (go a) <> (go b)
      e@(GEq a b) -> f e <> (go a) <> (go b)
      e@(SLT a b) -> f e <> (go a) <> (go b)
      e@(SGT a b) -> f e <> (go a) <> (go b)
      e@(Eq a b) -> f e <> (go a) <> (go b)
      e@(IsZero a) -> f e <> (go a)

      -- bits

      e@(And a b) -> f e <> (go a) <> (go b)
      e@(Or a b) -> f e <> (go a) <> (go b)
      e@(Xor a b) -> f e <> (go a) <> (go b)
      e@(Not a) -> f e <> (go a)
      e@(SHL a b) -> f e <> (go a) <> (go b)
      e@(SHR a b) -> f e <> (go a) <> (go b)
      e@(SAR a b) -> f e <> (go a) <> (go b)

      -- Hashes

      e@(Keccak a) -> f e <> (go a)
      e@(SHA256 a) -> f e <> (go a)

      -- block context

      e@(Origin) -> f e
      e@(Coinbase) -> f e
      e@(Timestamp) -> f e
      e@(BlockNumber) -> f e
      e@(Difficulty) -> f e
      e@(GasLimit) -> f e
      e@(ChainId) -> f e
      e@(BaseFee) -> f e
      e@(BlockHash _) -> f e

      -- frame context

      e@(Caller _) -> f e
      e@(CallValue _) -> f e
      e@(Address _) -> f e
      e@(SelfBalance _ _) -> f e
      e@(Gas _ _) -> f e
      e@(Balance {}) -> f e

      -- code

      e@(CodeSize a) -> f e <> (go a)
      e@(ExtCodeHash a) -> f e <> (go a)

      -- logs

      e@(LogEntry a b c) -> f e <> (go a) <> (go b) <> (foldl (<>) mempty (fmap f c))

      -- Contract Creation

      e@(Create a b c d g h)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (foldl (<>) mempty (fmap go g))
        <> (go h)
      e@(Create2 a b c d g h i)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (go g)
        <> (foldl (<>) mempty (fmap go h))
        <> (go i)

      -- Calls

      e@(Call a b c d g h i j k)
        -> f e
        <> (go a)
        <> (maybe mempty (go) b)
        <> (go c)
        <> (go d)
        <> (go g)
        <> (go h)
        <> (go i)
        <> (foldl (<>) mempty (fmap go j))
        <> (go k)

      e@(CallCode a b c d g h i j k)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (go g)
        <> (go h)
        <> (go i)
        <> (foldl (<>) mempty (fmap go j))
        <> (go k)

      e@(DelegeateCall a b c d g h i j k)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (go g)
        <> (go h)
        <> (go i)
        <> (foldl (<>) mempty (fmap go j))
        <> (go k)

      -- storage

      e@(EmptyStore) -> f e
      e@(ConcreteStore _) -> f e
      e@(AbstractStore) -> f e
      e@(SLoad a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(SStore a b c d) -> f e <> (go a) <> (go b) <> (go c) <> (go d)

      -- buffers

      e@(ConcreteBuf _) -> f e
      e@(AbstractBuf _) -> f e
      e@(ReadWord a b) -> f e <> (go a) <> (go b)
      e@(ReadByte a b) -> f e <> (go a) <> (go b)
      e@(WriteWord a b c) -> f e <> (go a) <> (go b) <> (go c)
      e@(WriteByte a b c) -> f e <> (go a) <> (go b) <> (go c)

      e@(CopySlice a b c d g)
        -> f e
        <> (go a)
        <> (go b)
        <> (go c)
        <> (go d)
        <> (go g)
      e@(BufLength a) -> f e <> (go a)

mapProp :: (forall a . Expr a -> Expr a) -> Prop -> Prop
mapProp f = \case
  PBool b -> PBool b
  PEq a b -> PEq (mapExpr f (f a)) (mapExpr f (f b))
  PLT a b -> PLT (mapExpr f (f a)) (mapExpr f (f b))
  PGT a b -> PGT (mapExpr f (f a)) (mapExpr f (f b))
  PLEq a b -> PLEq (mapExpr f (f a)) (mapExpr f (f b))
  PGEq a b -> PGEq (mapExpr f (f a)) (mapExpr f (f b))
  PNeg a -> PNeg (mapProp f a)
  PAnd a b -> PAnd (mapProp f a) (mapProp f b)
  POr a b -> POr (mapProp f a) (mapProp f b)

-- | Recursively applies a given function to every node in a given expr instance
-- Recursion schemes do this & a lot more, but defining them over GADT's isn't worth the hassle
mapExpr :: (forall a . Expr a -> Expr a) -> Expr b -> Expr b
mapExpr f expr = case (f expr) of

  -- literals & variables

  Lit a -> Lit a
  LitByte a -> LitByte a
  Var a -> Var a
  GVar a -> GVar a

  -- bytes

  IndexWord a b -> IndexWord (mapExpr f (f a)) (mapExpr f (f b))
  EqByte a b -> EqByte (mapExpr f (f a)) (mapExpr f (f b))

  JoinBytes
    zero one two three four five six seven
    eight nine ten eleven twelve thirteen fourteen fifteen
    sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
    twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone
    -> JoinBytes
        (mapExpr f (f zero)) (mapExpr f (f one)) (mapExpr f (f two)) (mapExpr f (f three))
        (mapExpr f (f four)) (mapExpr f (f five)) (mapExpr f (f six)) (mapExpr f (f seven))
        (mapExpr f (f eight)) (mapExpr f (f nine)) (mapExpr f (f ten)) (mapExpr f (f eleven))
        (mapExpr f (f twelve)) (mapExpr f (f thirteen)) (mapExpr f (f fourteen))
        (mapExpr f (f fifteen)) (mapExpr f (f sixteen)) (mapExpr f (f seventeen))
        (mapExpr f (f eighteen)) (mapExpr f (f nineteen)) (mapExpr f (f twenty))
        (mapExpr f (f twentyone)) (mapExpr f (f twentytwo)) (mapExpr f (f twentythree))
        (mapExpr f (f twentyfour)) (mapExpr f (f twentyfive)) (mapExpr f (f twentysix))
        (mapExpr f (f twentyseven)) (mapExpr f (f twentyeight)) (mapExpr f (f twentynine))
        (mapExpr f (f thirty)) (mapExpr f (f thirtyone))

  -- control flow

  Invalid -> Invalid
  SelfDestruct -> SelfDestruct
  IllegalOverflow -> IllegalOverflow
  Revert a -> Revert (mapExpr f (f a))
  Return a b -> Return (mapExpr f (f a)) (mapExpr f (f b))
  ITE a b c -> ITE (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))
  TmpErr a -> TmpErr a

  -- integers

  Add a b -> Add (mapExpr f (f a)) (mapExpr f (f b))
  Sub a b -> Sub (mapExpr f (f a)) (mapExpr f (f b))
  Mul a b -> Mul (mapExpr f (f a)) (mapExpr f (f b))
  Div a b -> Div (mapExpr f (f a)) (mapExpr f (f b))
  SDiv a b -> SDiv (mapExpr f (f a)) (mapExpr f (f b))
  Mod a b -> Mod (mapExpr f (f a)) (mapExpr f (f b))
  SMod a b -> SMod (mapExpr f (f a)) (mapExpr f (f b))
  AddMod a b c -> AddMod (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))
  MulMod a b c -> MulMod (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))
  Exp a b -> Exp (mapExpr f (f a)) (mapExpr f (f b))
  SEx a b -> SEx (mapExpr f (f a)) (mapExpr f (f b))
  Min a b -> Min (mapExpr f (f a)) (mapExpr f (f b))

  -- booleans

  LT a b ->  LT (mapExpr f (f a)) (mapExpr f (f b))
  GT a b ->  GT (mapExpr f (f a)) (mapExpr f (f b))
  LEq a b -> LEq (mapExpr f (f a)) (mapExpr f (f b))
  GEq a b -> GEq (mapExpr f (f a)) (mapExpr f (f b))
  SLT a b -> SLT (mapExpr f (f a)) (mapExpr f (f b))
  SGT a b -> SGT (mapExpr f (f a)) (mapExpr f (f b))
  Eq a b ->  Eq (mapExpr f (f a)) (mapExpr f (f b))
  IsZero a -> IsZero (mapExpr f (f a))

  -- bits

  And a b -> And (mapExpr f (f a)) (mapExpr f (f b))
  Or a b ->  Or (mapExpr f (f a)) (mapExpr f (f b))
  Xor a b -> Xor (mapExpr f (f a)) (mapExpr f (f b))
  Not a -> Not (mapExpr f (f a))
  SHL a b -> SHL (mapExpr f (f a)) (mapExpr f (f b))
  SHR a b -> SHR (mapExpr f (f a)) (mapExpr f (f b))
  SAR a b -> SAR (mapExpr f (f a)) (mapExpr f (f b))

  -- Hashes

  Keccak a -> Keccak (mapExpr f (f a))
  SHA256 a -> SHA256 (mapExpr f (f a))

  -- block context

  Origin -> Origin
  Coinbase -> Coinbase
  Timestamp -> Timestamp
  BlockNumber -> BlockNumber
  Difficulty -> Difficulty
  GasLimit -> GasLimit
  ChainId -> ChainId
  BaseFee -> BaseFee
  BlockHash a -> BlockHash (mapExpr f (f a))

  -- frame context

  Caller a -> Caller a
  CallValue a -> CallValue a
  Address a -> Address a
  SelfBalance a b -> SelfBalance a b
  Gas a b -> Gas a b
  Balance a b c -> Balance a b (mapExpr f (f c))

  -- code

  CodeSize a -> CodeSize (mapExpr f (f a))
  ExtCodeHash a -> ExtCodeHash (mapExpr f (f a))

  -- logs

  LogEntry a b c -> LogEntry (mapExpr f (f a)) (mapExpr f (f b)) (fmap (mapExpr f . f) c)

  -- Contract Creation

  Create a b c d e g
    -> Create
         (mapExpr f (f a))
         (mapExpr f (f b))
         (mapExpr f (f c))
         (mapExpr f (f d))
         (fmap (mapExpr f . f) e)
         (mapExpr f (f g))
  Create2 a b c d e g h
    -> Create2
         (mapExpr f (f a))
         (mapExpr f (f b))
         (mapExpr f (f c))
         (mapExpr f (f d))
         (mapExpr f (f e))
         (fmap (mapExpr f . f) g)
         (mapExpr f (f h))

  -- Calls

  Call a b c d e g h i j
    -> Call
         (mapExpr f (f a))
         (fmap (mapExpr f . f) b)
         (mapExpr f (f c))
         (mapExpr f (f d))
         (mapExpr f (f e))
         (mapExpr f (f g))
         (mapExpr f (f h))
         (fmap (mapExpr f . f) i)
         (mapExpr f (f j))
  CallCode a b c d e g h i j
    -> CallCode
        (mapExpr f (f a))
        (mapExpr f (f b))
        (mapExpr f (f c))
        (mapExpr f (f d))
        (mapExpr f (f e))
        (mapExpr f (f g))
        (mapExpr f (f h))
        (fmap (mapExpr f . f) i)
        (mapExpr f (f j))
  DelegeateCall a b c d e g h i j
    -> DelegeateCall
        (mapExpr f (f a))
        (mapExpr f (f b))
        (mapExpr f (f c))
        (mapExpr f (f d))
        (mapExpr f (f e))
        (mapExpr f (f g))
        (mapExpr f (f h))
        (fmap (mapExpr f . f) i)
        (mapExpr f (f j))

  -- storage

  EmptyStore -> EmptyStore
  ConcreteStore a -> ConcreteStore a
  AbstractStore -> AbstractStore
  SLoad a b c -> SLoad (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))
  SStore a b c d -> SStore (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c)) (mapExpr f (f d))

  -- buffers

  ConcreteBuf a -> ConcreteBuf a
  AbstractBuf a -> AbstractBuf a
  ReadWord a b -> ReadWord (mapExpr f (f a)) (mapExpr f (f b))
  ReadByte a b -> ReadByte (mapExpr f (f a)) (mapExpr f (f b))
  WriteWord a b c -> WriteWord (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))
  WriteByte a b c -> WriteByte (mapExpr f (f a)) (mapExpr f (f b)) (mapExpr f (f c))

  CopySlice a b c d e
    -> CopySlice
         (mapExpr f (f a))
         (mapExpr f (f b))
         (mapExpr f (f c))
         (mapExpr f (f d))
         (mapExpr f (f e))
  BufLength a -> BufLength (mapExpr f (f a))


mapExprM :: Monad m => (forall a . Expr a -> m (Expr a)) -> Expr b -> m (Expr b)
mapExprM f expr = case expr of

  -- literals & variables

  Lit a -> f (Lit a)
  LitByte a -> f (LitByte a)
  Var a -> f (Var a)
  GVar a -> f (GVar a)

  -- bytes

  IndexWord a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (IndexWord a' b')    
  EqByte a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (EqByte a' b')    

  JoinBytes zero one two three four five six seven eight nine
    ten eleven twelve thirteen fourteen fifteen sixteen seventeen
    eighteen nineteen twenty twentyone twentytwo twentythree twentyfour
    twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone -> do
    zero' <- mapExprM f zero
    one' <- mapExprM f one
    two' <- mapExprM f two
    three' <- mapExprM f three
    four' <- mapExprM f four
    five' <- mapExprM f five
    six' <- mapExprM f six
    seven' <- mapExprM f seven
    eight' <- mapExprM f eight
    nine' <- mapExprM f nine
    ten' <- mapExprM f ten
    eleven' <- mapExprM f eleven
    twelve' <- mapExprM f twelve
    thirteen' <- mapExprM f thirteen
    fourteen' <- mapExprM f fourteen
    fifteen' <- mapExprM f fifteen
    sixteen' <- mapExprM f sixteen
    seventeen' <- mapExprM f seventeen
    eighteen' <- mapExprM f eighteen
    nineteen' <- mapExprM f nineteen
    twenty' <- mapExprM f twenty
    twentyone' <- mapExprM f twentyone
    twentytwo' <- mapExprM f twentytwo
    twentythree' <- mapExprM f twentythree
    twentyfour' <- mapExprM f twentyfour
    twentyfive' <- mapExprM f twentyfive
    twentysix' <- mapExprM f twentysix
    twentyseven' <- mapExprM f twentyseven
    twentyeight' <- mapExprM f twentyeight
    twentynine' <- mapExprM f twentynine
    thirty' <- mapExprM f thirty
    thirtyone' <- mapExprM f thirtyone
    f (JoinBytes zero' one' two' three' four' five' six' seven' eight' nine'
         ten' eleven' twelve' thirteen' fourteen' fifteen' sixteen' seventeen'
         eighteen' nineteen' twenty' twentyone' twentytwo' twentythree' twentyfour'
         twentyfive' twentysix' twentyseven' twentyeight' twentynine' thirty' thirtyone')

  -- control flow

  Invalid -> f Invalid
  SelfDestruct -> f SelfDestruct
  IllegalOverflow -> f IllegalOverflow
  Revert a -> do
    a' <- mapExprM f a
    f (Revert a')
  Return a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Return a' b')

  ITE a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (ITE a' b' c')

  TmpErr a -> f (TmpErr a)

  -- integers

  Add a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Add a' b')
  Sub a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Sub a' b')
  Mul a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Mul a' b')
  Div a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Div a' b')
  SDiv a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SDiv a' b')
  Mod a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Mod a' b')
  SMod a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SMod a' b')
  AddMod a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (AddMod a' b' c')
  MulMod a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (MulMod a' b' c')
  Exp a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Exp a' b')
  SEx a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SEx a' b')
  Min a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Min a' b')

  -- booleans

  LT a b -> do 
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (LT a' b')
  GT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (GT a' b')
  LEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (LEq a' b')
  GEq a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (GEq a' b')
  SLT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SLT a' b')
  SGT a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SGT a' b')
  Eq a b ->  do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Eq a' b')
  IsZero a -> do
    a' <- mapExprM f a
    f (IsZero a')

  -- bits

  And a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (And a' b')
  Or a b ->  do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Or a' b')
  Xor a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (Xor a' b')
  Not a -> do
    a' <- mapExprM f a
    f (Not a')
  SHL a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SHL a' b')
  SHR a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SHR a' b')
  SAR a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (SAR a' b')
    

  -- Hashes

  Keccak a -> do
    a' <- mapExprM f a
    f (Keccak a')

  SHA256 a -> do
    a' <- mapExprM f a
    f (SHA256 a')

  -- block context

  Origin -> f Origin
  Coinbase -> f Coinbase
  Timestamp -> f Timestamp
  BlockNumber -> f BlockNumber
  Difficulty -> f Difficulty
  GasLimit -> f GasLimit
  ChainId -> f ChainId
  BaseFee -> f BaseFee
  BlockHash a -> do
    a' <- mapExprM f a
    f (BlockHash a')

  -- frame context

  Caller a -> f (Caller a)
  CallValue a -> f (CallValue a)
  Address a -> f (Address a)
  SelfBalance a b -> f (SelfBalance a b)
  Gas a b -> f (Gas a b)
  Balance a b c -> do
    c' <- mapExprM f c
    f (Balance a b c')

  -- code

  CodeSize a -> do
    a' <- mapExprM f a
    f (CodeSize a')
  ExtCodeHash a -> do
    a' <- mapExprM f a
    f (ExtCodeHash a')

  -- logs

  EmptyLog -> f EmptyLog
  Log a b c d -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapM (mapExprM f) c
    d' <- mapExprM f d
    f (Log a' b' c' d')

  -- Contract Creation

  Create a b c d e g -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    g' <- mapExprM f g
    f (Create a' b' c' d' e' g')
  Create2 a b c d e g h -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    g' <- mapExprM f g
    h' <- mapExprM f h
    f (Create2 a' b' c' d' e' g' h')
    
  -- Calls

  Call a b c d e g h i j -> do
    a' <- mapExprM f a
    b' <- mapM (mapExprM f) b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    g' <- mapExprM f g
    h' <- mapExprM f h
    i' <- mapExprM f i
    j' <- mapExprM f j
    f (Call a' b' c' d' e' g' h' i' j')
  CallCode a b c d e g h i j -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    g' <- mapExprM f g
    h' <- mapExprM f h
    i' <- mapExprM f i
    j' <- mapExprM f j
    f (CallCode a' b' c' d' e' g' h' i' j')
  DelegeateCall a b c d e g h i j -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    g' <- mapExprM f g
    h' <- mapExprM f h
    i' <- mapExprM f i
    j' <- mapExprM f j
    f (DelegeateCall a' b' c' d' e' g' h' i' j')

  -- storage

  EmptyStore -> f EmptyStore
  ConcreteStore a -> do
    f (ConcreteStore a)
  AbstractStore -> f AbstractStore
  SLoad a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (SLoad a' b' c')
  SStore a b c d -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    f (SStore a' b' c' d')

  -- buffers

  ConcreteBuf a -> do
    f (ConcreteBuf a)
  AbstractBuf a -> do
    f (AbstractBuf a)
  ReadWord a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (ReadWord a' b')
  ReadByte a b -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    f (ReadByte a' b')
  WriteWord a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (WriteWord a' b' c')
  WriteByte a b c -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    f (WriteByte a' b' c')

  CopySlice a b c d e -> do
    a' <- mapExprM f a
    b' <- mapExprM f b
    c' <- mapExprM f c
    d' <- mapExprM f d
    e' <- mapExprM f e
    f (CopySlice a' b' c' d' e')
    
  BufLength a -> do
    a' <- mapExprM f a
    f (BufLength a)
    
