{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, keccakCompute) where

import Control.Monad.State
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List (tails)

import EVM.Traversals
import EVM.Types
import EVM.Expr


newtype KeccakStore = KeccakStore
  { keccakExprs :: Set (Expr EWord) }
  deriving (Show)

initState :: KeccakStore
initState = KeccakStore { keccakExprs = Set.empty }

keccakFinder :: forall a. Expr a -> State KeccakStore ()
keccakFinder = \case
  e@(Keccak _) -> modify (\s -> s{keccakExprs=Set.insert e s.keccakExprs})
  _ -> pure ()

findKeccakExpr :: forall a. Expr a -> State KeccakStore ()
findKeccakExpr e = mapExprM_ keccakFinder e

findKeccakProp :: Prop -> State KeccakStore ()
findKeccakProp p = mapPropM_ keccakFinder p

findKeccakPropsExprs :: [Prop] -> [Expr Buf]  -> [Expr Storage]-> State KeccakStore ()
findKeccakPropsExprs ps bufs stores = do
  mapM_ findKeccakProp ps
  mapM_ findKeccakExpr bufs
  mapM_ findKeccakExpr stores


uniquePairs :: [a] -> [(a,a)]
uniquePairs xs = [(x,y) | (x:ys) <- Data.List.tails xs, y <- ys]

minProp :: Expr EWord -> Prop
minProp k@(Keccak _) = PGT k (Lit 256)
minProp _ = internalError "expected keccak expression"

injProp :: (Expr EWord, Expr EWord) -> Prop
injProp (k1@(Keccak b1), k2@(Keccak b2)) =
  PImpl (PEq k1 k2) ((b1 .== b2) .&& (bufLength b1 .== bufLength b2))
injProp _ = internalError "expected keccak expression"


-- Takes a list of props, find all keccak occurrences and generates two kinds of assumptions:
--   1. Minimum output value: That the output of the invocation is greater than
--      256 (needed to avoid spurious counterexamples due to storage collisions
--      with solidity mappings & value type storage slots)
--   2. Injectivity: That keccak is an injective function (we avoid quantifiers
--      here by making this claim for each unique pair of keccak invocations
--      discovered in the input expressions)
keccakAssumptions :: [Prop] -> [Expr Buf] -> [Expr Storage] -> [Prop]
keccakAssumptions ps bufs stores = injectivity <> minValue <> minDiffOfPairs
  where
    (_, st) = runState (findKeccakPropsExprs ps bufs stores) initState

    keccakPairs = uniquePairs (Set.toList st.keccakExprs)
    injectivity = map injProp keccakPairs
    minValue = map minProp (Set.toList st.keccakExprs)
    minDiffOfPairs = map minDistance keccakPairs
     where
      minDistance :: (Expr EWord, Expr EWord) -> Prop
      minDistance (ka@(Keccak a), kb@(Keccak b)) = PImpl ((a ./= b) .|| (bufLength a ./= bufLength b)) (PAnd req1 req2)
        where
          req1 = (PGEq (Sub ka kb) (Lit 256))
          req2 = (PGEq (Sub kb ka) (Lit 256))
      minDistance _ = internalError "expected Keccak expression"

compute :: forall a. Expr a -> [Prop]
compute = \case
  e@(Keccak buf) -> do
    let b = simplify buf
    case keccak b of
      lit@(Lit _) -> [PEq lit e]
      _ -> []
  _ -> []

computeKeccakExpr :: forall a. Expr a -> [Prop]
computeKeccakExpr e = foldExpr compute [] e

computeKeccakProp :: Prop -> [Prop]
computeKeccakProp p = foldProp compute [] p

keccakCompute :: [Prop] -> [Expr Buf] -> [Expr Storage] -> [Prop]
keccakCompute ps buf stores =
  concatMap computeKeccakProp ps <>
  concatMap computeKeccakExpr buf <>
  concatMap computeKeccakExpr stores
