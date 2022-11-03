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
import EVM.Traversals


-- maps expressions to variable names
data BuilderState = BuilderState
  { bufs :: (Int, Map (Expr Buf) Int)
  , stores :: (Int, Map (Expr Storage) Int)
  }
  deriving (Show)

data Prog a = Prog
  { code       :: Expr a
  , bufEnv     :: Map (GVar Buf) (Expr Buf)
  , storeEnv   :: Map (GVar Storage) (Expr Storage)
  , facts      :: [Prop]
  }

initState :: BuilderState
initState = BuilderState
  { bufs = (0, Map.empty)
  , stores = (0, Map.empty)
  }


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
      e -> pure e

eliminate :: Expr a -> Prog a
eliminate e =
  let (e', st) = runState (eliminate' e) initState in
  Prog { code = e'
       , bufEnv = invertKeyVal $ snd (bufs st)
       , storeEnv = invertKeyVal $ snd (stores st)
       , facts = []
       }
  where
    invertKeyVal =  Map.fromList . map (\(x, y) -> (Id y, x)) . Map.toList
