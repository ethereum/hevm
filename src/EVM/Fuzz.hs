{-# LANGUAGE ScopedTypeVariables #-}

{- |
    Module: EVM.Fuzz
    Description: Concrete Fuzzer of Exprs
-}

module EVM.Fuzz where

import Prelude hiding (LT, GT, lookup)
import Control.Monad.State
import Data.Maybe (fromMaybe)
import Data.Map.Strict as Map (fromList, Map, (!), (!?), insert)
import EVM.Expr qualified as Expr
import EVM.Expr (bytesToW256)
import Data.Set as Set (insert, Set, empty, toList)
import EVM.Traversals
import Data.ByteString qualified as BS
import Data.Word (Word8)
import Control.Monad.Random.Strict qualified as CMR

import EVM.Types (Prop(..), W256, Expr(..), EType(..), internalError, keccak')
import EVM.SMT (BufModel(..), SMTCex(..))
import Debug.Trace

-- TODO: Extract Var X = Lit Z, and set it
tryCexFuzz :: [Prop] -> Integer -> Maybe (SMTCex)
tryCexFuzz ps tries = CMR.evalRand (testVals tries) (CMR.mkStdGen 1337)
  where
    vars = extractVars ps
    bufs = extractBufs ps
    stores = extractStorage ps
    testVals :: CMR.MonadRandom m => Integer -> m (Maybe SMTCex)
    testVals 0 = pure Nothing
    testVals todo = do
      varVals <- getVals vars
      bufVals <- getBufs bufs
      storeVals <- getStores stores
      let
        ret =  filterCorrectKeccak $ map (substituteEWord varVals . substituteBuf bufVals . substituteStores storeVals) ps
        retSimp =  Expr.simplifyProps ret
      traceM $ "varvals: " <> show varVals -- <> "ret: " <> show ret <> " retsimp: " <> show retSimp
      if null retSimp then pure $ Just (SMTCex {
                                    vars = varVals
                                    , addrs = mempty
                                    , buffers = bufVals
                                    , store = storeVals
                                    , blockContext = mempty
                                    , txContext = mempty
                                    })
                                    else testVals (todo-1)

-- Filter out PEq (Lit X) (keccak (ConcreteBuf Y)) if it's correct
filterCorrectKeccak :: [Prop] -> [Prop]
filterCorrectKeccak ps = filter checkKecc ps
  where
    checkKecc (PEq (Lit x) (Keccak (ConcreteBuf y))) = keccak' y /= x
    checkKecc _ = True

substituteEWord :: Map (Expr EWord) W256 -> Prop -> Prop
substituteEWord valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go orig@(Var _) = Lit (valMap ! orig)
    go orig@(TxValue) = Lit (valMap ! orig)
    go a = a


substituteBuf :: Map (Expr Buf) BufModel -> Prop -> Prop
substituteBuf valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go orig@(AbstractBuf _) = case (valMap !? orig) of
                                Just (Flat x) -> ConcreteBuf x
                                Just (Comp _) -> internalError "No compressed allowed in fuzz"
                                Nothing -> orig
    go a = a

substituteStores ::  Map (Expr 'EAddr) (Map W256 W256) -> Prop -> Prop
substituteStores valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go (AbstractStore a) = case valMap !? a of
                                  Just m -> ConcreteStore m
                                  Nothing -> ConcreteStore mempty
    go a = a

-- Var extraction
-- TODO extract all Lit's and stick them into the values once in a while
data CollectVars = CollectVars {vars :: Set.Set (Expr EWord)
                               ,vals :: Set.Set W256
                               }
  deriving (Show)

initVarsState :: CollectVars
initVarsState = CollectVars {vars = Set.empty
                            ,vals =  Set.empty
                            }

findVarProp :: Prop -> State CollectVars Prop
findVarProp p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectVars (Expr a)
    go = \case
      e@(Var a) -> do
        s :: CollectVars <- get
        put CollectVars {vars=Set.insert (Var a) s.vars, vals = s.vals}
        pure e
      e@(Lit a) -> do
        s :: CollectVars <- get
        put $ s{vals=Set.insert a s.vals}
        pure e
      e -> pure e


extractVars :: [Prop] -> CollectVars
extractVars ps = execState (mapM_ findVarProp ps) initVarsState



--- Buf extraction
newtype CollectBufs = CollectBufs { bufs :: Set.Set (Expr Buf) }
  deriving (Show)

initBufsState :: CollectBufs
initBufsState = CollectBufs { bufs = Set.empty }

extractBufs :: [Prop] -> [Expr Buf]
extractBufs ps = Set.toList bufs
 where
  CollectBufs bufs = execState (mapM_ findBufProp ps) initBufsState

findBufProp :: Prop -> State CollectBufs Prop
findBufProp p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectBufs (Expr a)
    go = \case
      e@(AbstractBuf a) -> do
        s <- get
        put $ s{bufs=Set.insert (AbstractBuf a) s.bufs}
        pure e
      e -> pure e

--- Store extraction
data CollectStorage = CollectStorage { stores :: Set.Set (Expr EAddr)
                                     , loads :: Set.Set W256
                                     -- TODO values
                                     }
  deriving (Show)

initStorageState :: CollectStorage
initStorageState = CollectStorage { stores = Set.empty, loads = Set.empty }

extractStorage :: [Prop] -> CollectStorage
extractStorage ps = execState (mapM_ findStorageProp ps) initStorageState

findStorageProp :: Prop -> State CollectStorage Prop
findStorageProp p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectStorage (Expr a)
    go = \case
      e@(AbstractStore a) -> do
        s <- get
        put $ s{stores=Set.insert a s.stores}
        pure e
      e@(SLoad (Lit val) _) -> do
        s <- get
        put $ s{loads=Set.insert val s.loads}
        pure e
      e -> pure e

-- Var value generation
getVals :: CMR.MonadRandom m => CollectVars -> m (Map (Expr EWord) W256)
getVals vars = do
    bufs <- go (Set.toList vars.vars) mempty
    addTxStuff bufs
  where
    addTxStuff :: CMR.MonadRandom m => Map (Expr EWord) W256 -> m (Map (Expr EWord) W256)
    addTxStuff a = pure $ Map.insert TxValue 0 a -- TODO change from 0 sometimes
    go :: CMR.MonadRandom m => [Expr EWord] -> Map (Expr EWord) W256 -> m (Map (Expr EWord) W256)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      pickKnown :: Bool <- CMR.getRandom
      let choices :: [W256] = Set.toList (vars.vals)
      val <- if (not pickKnown) || (null vars.vals) then do getRndW256
                                                    else do pickOne choices
      go ax (Map.insert a val valMap)

-- Storage value generation
getStores :: CMR.MonadRandom m => CollectStorage -> m (Map (Expr EAddr) (Map W256 W256))
getStores storesLoads = go (Set.toList storesLoads.stores) mempty
  where
    go :: CMR.MonadRandom m => [Expr EAddr] -> Map (Expr EAddr) (Map W256 W256) -> m (Map (Expr EAddr) (Map W256 W256))
    go [] addrToValsMap = pure addrToValsMap
    -- TODO: add more than one write to a single address
    go (addr:ax) addrToValsMap = do
      emptySize :: Bool <- CMR.getRandom
      valMap <- if emptySize then pure $ Map.fromList [(0 :: W256,0::W256)]
                             else do
                               a <- getRndElem storesLoads.loads
                               b <- getRndW256
                               pure $ Map.fromList [(fromMaybe (0::W256) a, b)]
      go ax (Map.insert addr valMap addrToValsMap)
    getRndElem :: CMR.MonadRandom m => Set W256 -> m (Maybe W256)
    getRndElem choices = if null choices then pure Nothing
                         else do fmap Just $ pickOne $ Set.toList choices

-- Picks one element from list. List must be non-empty
pickOne :: CMR.MonadRandom m => [k] -> m k
pickOne s = do
  k <- CMR.getRandomR (0, (length s)-1)
  pure $ s !! k

-- Buf value generation
getBufs :: CMR.MonadRandom m => [Expr Buf] -> m (Map (Expr Buf) BufModel)
getBufs bufs = go bufs mempty
  where
    go :: CMR.MonadRandom m => [Expr Buf] -> Map (Expr Buf) BufModel -> m (Map (Expr Buf) BufModel)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      emptySize :: Bool <- CMR.getRandom
      size <- if emptySize then (pure 0)
                           else getRndW8
      bytes <- getRndW8s (fromIntegral size)
      go ax (Map.insert a (Flat $ BS.pack bytes) valMap)

getRndW8 :: CMR.MonadRandom m => m Word8
getRndW8 = do CMR.getRandom

getRndW256 :: CMR.MonadRandom m => m W256
getRndW256 = do
      val <- getRndW8s 32
      pure $ bytesToW256 val

getRndW8s :: CMR.MonadRandom m => Int -> m [Word8]
getRndW8s n = replicateM n getRndW8
