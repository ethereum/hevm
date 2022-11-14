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
import Data.Text (Text)
import qualified Data.Text as T

import EVM.Types
import EVM.Traversals

-- maps expressions to variable names
data BuilderState = BuilderState
  { bufs :: (Int, Map (Expr Buf) Int)
  , stores :: (Int, Map (Expr Storage) Int)
  }
  deriving (Show)

type BufEnv = Map (GVar Buf) (Expr Buf)
type StoreEnv = Map (GVar Storage) (Expr Storage)

initState :: BuilderState
initState = BuilderState
  { bufs = (0, Map.empty)
  , stores = (0, Map.empty)
  }


go :: Expr a -> State BuilderState (Expr a)
go = \case
  -- buffers
  e@(WriteWord i v b) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (Id v) (makeName "buf" v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (Id next) (makeName "buf" next)
  e@(WriteByte i v b) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (Id v) (makeName "buf" v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (Id next) (makeName "buf" next)
  e@(CopySlice srcOff dstOff s src dst) -> do
    s <- get
    let (next, bs) = bufs s
    case Map.lookup e bs of
      Just v -> pure $ GVar (Id v) (makeName "buf" v)
      Nothing -> do
        let bs' = Map.insert e next bs
        put $ s{bufs=(next + 1, bs')}
        pure $ GVar (Id next) (makeName "buf" next)
  -- storage
  e@(SStore addr i v s) -> do
    s <- get
    let (next, ss) = stores s
    case Map.lookup e ss of
      Just v -> pure $ GVar (Id v) (makeName "store" v)
      Nothing -> do
        let ss' = Map.insert e next ss
        put $ s{stores=(next + 1, ss')}
        pure $ GVar (Id next) (makeName "store" next)
  e -> pure e
  where
    makeName s n = s <> (T.pack . show $ n)

-- | Common subexpression elimination pass for Expr
eliminateExpr' :: Expr a -> State BuilderState (Expr a)
eliminateExpr' e = mapExprM go e

eliminateExpr :: Expr a -> (Expr a, BufEnv, StoreEnv)
eliminateExpr e =
  let (e', st) = runState (eliminateExpr' e) initState in
  (e', invertKeyVal (snd (bufs st)), invertKeyVal (snd (stores st)))
  where
    invertKeyVal =  Map.fromList . map (\(x, y) -> (Id y, x)) . Map.toList


-- | Common subexpression elimination pass for Prop
eliminateProp' :: Prop -> State BuilderState Prop
eliminateProp' prop = mapPropM go prop

eliminateFlat' :: [([Prop], Expr End)] -> State BuilderState [([Prop], Expr End)]
eliminateFlat' leaves = flip mapM leaves $ (\(p, e) -> do
                                               p' <- mapM eliminateProp' p
                                               e' <- eliminateExpr' e
                                               pure $ (p', e'))

-- | Common subexpression elimination pass for flattened Expr programs
eliminateFlat :: [([Prop], Expr End)] -> ([([Prop], Expr End)], BufEnv, StoreEnv)
eliminateFlat leaves =
  let (leaves', st) = runState (eliminateFlat' leaves) initState in
  (leaves',  invertKeyVal (snd (bufs st)),  invertKeyVal (snd (stores st)))
  where
    invertKeyVal =  Map.fromList . map (\(x, y) -> (Id y, x)) . Map.toList



-- | Common subexpression elimination pass for list of Prop
eliminateProps' :: [Prop] -> State BuilderState [Prop]
eliminateProps' props = mapM eliminateProp' props


-- | Common subexpression elimination pass for list of Prop
eliminateProps :: [Prop] -> ([Prop], BufEnv, StoreEnv)
eliminateProps props =
  let (props', st) = runState (eliminateProps' props) initState in
  (props',  invertKeyVal (snd (bufs st)),  invertKeyVal (snd (stores st)))
  where
    invertKeyVal =  Map.fromList . map (\(x, y) -> (Id y, x)) . Map.toList
