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
    ks = Set.toList $ Set.map concretizeKeccakParam st.keccakExprs
    keccakPairs = uniquePairs ks
    injectivity = map injProp keccakPairs
    minValue = map minProp ks
    minDiffOfPairs = map minDistance keccakPairs
     where
      minDistance :: (Expr EWord, Expr EWord) -> Prop
      minDistance (ka@(Keccak a), kb@(Keccak b)) = PImpl ((a ./= b) .|| (bufLength a ./= bufLength b)) (PAnd req1 req2)
        where
          req1 = (PGEq (Sub ka kb) (Lit 256))
          req2 = (PGEq (Sub kb ka) (Lit 256))
      minDistance _ = internalError "expected Keccak expression"

concretizeKeccakParam :: Expr EWord -> Expr EWord
concretizeKeccakParam (Keccak buf) = Keccak (concKeccakSimpExpr buf)
concretizeKeccakParam _ = internalError "Cannot happen"

compute :: forall a. Expr a -> Set Prop
compute = \case
  Keccak buf -> do
    let b = concKeccakSimpExpr buf
    case keccak b of
      lit@(Lit _) -> Set.singleton (PEq lit (Keccak b))
      _ -> Set.empty
  _ -> Set.empty

computeKeccakExpr :: forall a. Expr a -> Set Prop
computeKeccakExpr e = foldExpr compute Set.empty e

computeKeccakProp :: Prop -> Set Prop
computeKeccakProp p = foldProp compute Set.empty p

keccakCompute :: [Prop] -> [Expr Buf] -> [Expr Storage] -> [Prop]
keccakCompute ps buf stores =
  Set.toList $
    (foldMap computeKeccakProp ps) <>
    (foldMap computeKeccakExpr buf) <>
    (foldMap computeKeccakExpr stores)
