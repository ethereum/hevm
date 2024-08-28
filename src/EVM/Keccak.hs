{-# LANGUAGE DataKinds #-}

{- |
    Module: EVM.Keccak
    Description: Expr passes to determine Keccak assumptions
-}
module EVM.Keccak (keccakAssumptions, keccakCompute) where

import Control.Monad.State
import Data.Set (Set)
import Data.Set qualified as Set

import EVM.Traversals
import EVM.Types
import EVM.Expr


newtype KeccakStore = KeccakStore
  { keccakEqs :: Set (Expr EWord) }
  deriving (Show)

initState :: KeccakStore
initState = KeccakStore { keccakEqs = Set.empty }

keccakFinder :: forall a. Expr a -> State KeccakStore (Expr a)
keccakFinder = \case
  e@(Keccak _) -> do
    s <- get
    put $ s{keccakEqs=Set.insert e s.keccakEqs}
    pure e
  e -> pure e

findKeccakExpr :: forall a. Expr a -> State KeccakStore (Expr a)
findKeccakExpr e = mapExprM keccakFinder e

findKeccakProp :: Prop -> State KeccakStore Prop
findKeccakProp p = mapPropM keccakFinder p

findKeccakPropsExprs :: [Prop] -> [Expr Buf]  -> [Expr Storage]-> State KeccakStore ()
findKeccakPropsExprs ps bufs stores = do
  mapM_ findKeccakProp ps
  mapM_ findKeccakExpr bufs
  mapM_ findKeccakExpr stores


combine :: [a] -> [(a,a)]
combine lst = combine' lst []
  where
    combine' [] acc = concat acc
    combine' (x:xs) acc =
      let xcomb = [ (x, y) | y <- xs] in
      combine' xs (xcomb:acc)

minProp :: Expr EWord -> Prop
minProp k@(Keccak _) = PGT k (Lit 256)
minProp _ = internalError "expected keccak expression"

concVal :: Expr EWord -> Prop
concVal k@(Keccak (ConcreteBuf bs)) = PEq (Lit (keccak' bs)) k
concVal _ = PBool True

injProp :: (Expr EWord, Expr EWord) -> Prop
injProp (k1@(Keccak b1), k2@(Keccak b2)) =
  POr ((b1 .== b2) .&& (bufLength b1 .== bufLength b2)) (PNeg (PEq k1 k2))
injProp _ = internalError "expected keccak expression"


-- Takes a list of props, find all keccak occurrences and generates two kinds of assumptions:
--   1. Minimum output value: That the output of the invocation is greater than
--      256 (needed to avoid spurious counterexamples due to storage collisions
--      with solidity mappings & value type storage slots)
--   2. Injectivity: That keccak is an injective function (we avoid quantifiers
--      here by making this claim for each unique pair of keccak invocations
--      discovered in the input expressions)
keccakAssumptions :: [Prop] -> [Expr Buf] -> [Expr Storage] -> [Prop]
keccakAssumptions ps bufs stores = injectivity <> minValue <> minDiffOfPairs <> concValues
  where
    (_, st) = runState (findKeccakPropsExprs ps bufs stores) initState

    injectivity = fmap injProp $ combine (Set.toList st.keccakEqs)
    concValues = fmap concVal (Set.toList st.keccakEqs)
    minValue = fmap minProp (Set.toList st.keccakEqs)
    minDiffOfPairs = map minDistance $ filter (uncurry (/=)) [(a,b) | a<-(Set.elems st.keccakEqs), b<-(Set.elems st.keccakEqs)]
     where
      minDistance :: (Expr EWord, Expr EWord) -> Prop
      minDistance (ka@(Keccak a), kb@(Keccak b)) = PImpl (a ./= b) (PAnd req1 req2)
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
