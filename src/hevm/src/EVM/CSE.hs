{-# Language DataKinds #-}

{- |
    Module: EVM.CSE
    Description: Common subexpression elimination for Expr ast
-}

module EVM.CSE (BufEnv, StoreEnv, eliminateExpr, eliminateProps) where

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

type BufEnv = Map Int (Expr Buf)
type StoreEnv = Map Int (Expr Storage)

initState :: BuilderState
initState = BuilderState
  { bufs = (0, Map.empty)
  , stores = (0, Map.empty)
  }


go :: Expr a -> State BuilderState (Expr a)
go = \case
  -- buffers
  e@(WriteWord {}) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (BufVar next)
  e@(WriteByte {}) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (BufVar next)
  e@(CopySlice {}) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (BufVar v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (BufVar next)
  -- storage
  e@(SStore {}) -> do
    s <- get
    let (next, ss) = stores s
    case Map.lookup e ss of
      Just v -> pure $ GVar (StoreVar v)
      Nothing -> do
        let ss' = Map.insert e next ss
        put $ s{stores=(next + 1, ss')}
        pure $ GVar (StoreVar next)
  e -> pure e

invertKeyVal :: forall a. Map a Int -> Map Int a
invertKeyVal =  Map.fromList . map (\(x, y) -> (y, x)) . Map.toList

-- | Common subexpression elimination pass for Expr
eliminateExpr' :: Expr a -> State BuilderState (Expr a)
eliminateExpr' e = mapExprM go e

eliminateExpr :: Expr a -> (Expr a, BufEnv, StoreEnv)
eliminateExpr e =
  let (e', st) = runState (eliminateExpr' e) initState in
  (e', invertKeyVal (snd (bufs st)), invertKeyVal (snd (stores st)))

-- | Common subexpression elimination pass for Prop
eliminateProp' :: Prop -> State BuilderState Prop
eliminateProp' prop = mapPropM go prop

-- | Common subexpression elimination pass for list of Prop
eliminateProps' :: [Prop] -> State BuilderState [Prop]
eliminateProps' props = mapM eliminateProp' props


-- | Common subexpression elimination pass for list of Prop
eliminateProps :: [Prop] -> ([Prop], BufEnv, StoreEnv)
eliminateProps props =
  let (props', st) = runState (eliminateProps' props) initState in
  (props',  invertKeyVal (snd (bufs st)),  invertKeyVal (snd (stores st)))
