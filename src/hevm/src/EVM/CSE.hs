{-# Language DataKinds #-}

{- |
    Module: EVM.CSE
    Description: Common subexpression elimination for Expr ast
-}

module EVM.CSE where

import Prelude hiding (Word, LT, GT)

import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.State

import EVM.Types


-- maps expressions to variable names
data BuilderState = BuilderState
  { bufs :: (Int, Map (Expr Buf) Int)
  , stores :: (Int, Map (Expr Storage) Int)
  }
  deriving (Show)

data Prog a = Prog
  { code       :: Expr a
  , bufEnv    :: Map (GVar Buf) (Expr Buf)
  , storeEnv   :: Map (GVar Storage) (Expr Storage)
  , facts      :: [Prop]
  }

initState :: BuilderState
initState = BuilderState
  { bufs = (0, Map.empty)
  , stores = (0, Map.empty)
  }

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
    

-- | Common subexpression elimination pass for Expr
eliminate' :: Expr a -> State BuilderState (Expr a)
eliminate' e = mapExprM go e
  where 
    go :: Expr a -> State BuilderState (Expr a)
    go = \case
      -- buffers
      e@(ConcreteBuf bs) -> do
        s <- get
        let (next, bs) = bufs s
        case Map.lookup e bs of
          Just v -> pure $ GVar (Id v)
          Nothing -> do
            let bs' = Map.insert e next bs
            put $ s{bufs=(next + 1, bs')}
            pure $ GVar (Id next)
      e@(WriteWord i v b) -> do
        s <- get
        let (next, bs) = bufs s
        case Map.lookup e bs of
          Just v -> pure $ GVar (Id v)
          Nothing -> do
            let bs' = Map.insert e next bs
            put $ s{bufs=(next + 1, bs')}
            pure $ GVar (Id next)
      e@(WriteByte i v b) -> do
        s <- get
        let (next, bs) = bufs s
        case Map.lookup e bs of
          Just v -> pure $ GVar (Id v)
          Nothing -> do
            let bs' = Map.insert e next bs
            put $ s{bufs=(next + 1, bs')}
            pure $ GVar (Id next)
      e@(CopySlice srcOff dstOff s src dst) -> do
        s <- get
        let (next, bs) = bufs s
        case Map.lookup e bs of
          Just v -> pure $ GVar (Id v)
          Nothing -> do
            let bs' = Map.insert e next bs
            put $ s{bufs=(next + 1, bs')}
            pure $ GVar (Id next)
      -- storage
      e@(SStore addr i v s) -> do
        s <- get
        let (next, ss) = stores s
        case Map.lookup e ss of
          Just v -> pure $ GVar (Id v)
          Nothing -> do
            let ss' = Map.insert e next ss
            put $ s{stores=(next + 1, ss')}
            pure $ GVar (Id next)


eliminate :: Expr a -> Prog a
eliminate e =
  let (e', st) = runState (eliminate' e) initState in
  Prog { code = e
       , bufEnv = invertKeyVal $ snd (bufs st)
       , storeEnv = invertKeyVal $ snd (stores st)
       , facts = []
       }
  where
    invertKeyVal =  Map.fromList . map (\(x, y) -> (Id y, x)) . Map.toList
