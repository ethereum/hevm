{-# LANGUAGE DataKinds #-}
{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}

module EVM.Keccak (keccakAssumptions) where

import Prelude hiding (Word, LT, GT)

import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State

import EVM.Types
import EVM.Traversals


data BuilderState = BuilderState
  { keccaks :: Set (Expr EWord) }
  deriving (Show)

initState :: BuilderState
initState = BuilderState { keccaks = Set.empty }

go :: forall a. Expr a -> State BuilderState (Expr a)
go = \case
  e@(Keccak _) -> do
    s <- get
    put $ s{keccaks=Set.insert e (keccaks s)}
    pure e
  e -> pure e

findKeccakExpr :: forall a. Expr a -> State BuilderState (Expr a)
findKeccakExpr e = mapExprM go e

findKeccakProp :: Prop -> State BuilderState Prop
findKeccakProp p = mapPropM go p

findKeccakPropsExprs :: [Prop] -> [Expr Buf]  -> [Expr Storage]-> State BuilderState ()
findKeccakPropsExprs ps bufs stores = do
  mapM_ findKeccakProp ps;
  mapM_ findKeccakExpr bufs;
  mapM_ findKeccakExpr stores


combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

minProp :: Expr EWord -> Prop
minProp k@(Keccak _) = PGT k (Lit 50)
minProp _ = error "Internal error: expected keccak expression"

injProp :: (Expr EWord, Expr EWord) -> Prop
injProp (k1@(Keccak b1), k2@(Keccak b2)) =
  POr (PEq b1 b2) (PNeg (PEq k1 k2))
injProp _ = error "Internal error: expected keccak expression"

-- Takes a list of props, find all keccak occurences and generates two kinds of assumptions:
--   1. Minimum output value: That the output of the invocation is greater than
--      50 (needed to avoid spurious counterexamples due to storage collisions
--      with solidity mappings & value type storage slots)
--   2. Injectivity: That keccak is an injective function (we avoid quantifiers
--      here by making this claim for each unique pair of keccak invocations
--      discovered in the input expressions)
keccakAssumptions :: [Prop] -> [Expr Buf] -> [Expr Storage] -> [Prop]
keccakAssumptions ps bufs stores = injectivity <> minValue
  where
    (_, st) = runState (findKeccakPropsExprs ps bufs stores) initState

    injectivity = fmap injProp $ combine (Set.toList (keccaks st))
    minValue = fmap minProp (Set.toList (keccaks st))


