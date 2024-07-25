{- |
    Module: EVM.Fuzz
    Description: Concrete Fuzzer of Exprs
-}

module EVM.Fuzz where

import Control.Monad (replicateM)
import Control.Monad.State (State, get, put, execState)
import Data.Map.Strict as Map (fromList, Map, (!), (!?), insert)
import Data.Maybe (fromMaybe)
import Data.Set as Set (insert, Set, empty, toList, fromList)
import Data.ByteString qualified as BS
import Data.Word (Word8)

import EVM.Expr qualified as Expr
import EVM.Expr (bytesToW256)
import EVM.SMT qualified as SMT (BufModel(..), SMTCex(..))
import EVM.Traversals
import EVM.Types (Prop(..), W256, Expr(..), EType(..), internalError, keccak')

import Test.QuickCheck (Arbitrary(arbitrary))
import Test.QuickCheck.Gen
import Test.QuickCheck.Random (mkQCGen)

-- TODO: Extract Var X = Lit Z, and set it
tryCexFuzz :: [Prop] -> Integer -> (Maybe (SMT.SMTCex))
tryCexFuzz prePs tries = unGen (testVals tries) (mkQCGen 0) 1337
  where
    ps = Expr.simplifyProps $ Expr.concKeccakProps prePs
    vars = extractVars ps
    bufs = extractBufs ps
    stores = extractStorage ps
    testVals :: Integer -> Gen (Maybe SMT.SMTCex)
    testVals 0 = pure Nothing
    testVals todo = do
      varvals <- getvals vars
      bufVals <- getBufs bufs
      storeVals <- getStores stores
      let
        ret = filterCorrectKeccak $ map (substituteEWord varvals . substituteBuf bufVals . substituteStores storeVals) ps
        retSimp = Expr.simplifyProps $ Expr.concKeccakProps ret
      if null retSimp then pure $ Just (SMT.SMTCex {
                                    vars = varvals
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


substituteBuf :: Map (Expr Buf) SMT.BufModel -> Prop -> Prop
substituteBuf valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    go orig@(AbstractBuf _) = case (valMap !? orig) of
                                Just (SMT.Flat x) -> ConcreteBuf x
                                Just (SMT.Comp _) -> internalError "No compressed allowed in fuzz"
                                Nothing -> orig
    go a = a

substituteStores ::  Map (Expr 'EAddr) (Map W256 W256) -> Prop -> Prop
substituteStores valMap p = mapProp go p
  where
    go :: Expr a -> Expr a
    -- TODO: Is this OK??
    go (AbstractStore a _) = case valMap !? a of
                                  Just m -> ConcreteStore m
                                  Nothing -> ConcreteStore mempty
    go a = a

-- Var extraction
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
        s <- get
        put s {vars = Set.insert (Var a) s.vars}
        pure e
      e@(Lit a) -> do
        s <- get
        put (s {vals=Set.insert a s.vals} ::CollectVars)
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
        put s {bufs=Set.insert (AbstractBuf a) s.bufs}
        pure e
      e -> pure e

--- Store extraction
data CollectStorage = CollectStorage { addrs :: Set.Set (Expr EAddr, Maybe W256)
                                     , keys :: Set.Set W256
                                     , vals :: Set.Set W256
                                     }
  deriving (Show)

instance Semigroup (CollectStorage) where
  (CollectStorage a b c) <> (CollectStorage a2 b2 c2) = CollectStorage (a <> a2) (b <> b2) (c <> c2)

initStorageState :: CollectStorage
initStorageState = CollectStorage { addrs = Set.empty, keys = Set.empty, vals = Set.fromList [0x0, 0x1, Expr.maxLit] }

extractStorage :: [Prop] -> CollectStorage
extractStorage ps = execState (mapM_ findStoragePropInner ps) initStorageState <>
    execState (mapM_ findStoragePropComp ps) initStorageState

findStoragePropComp :: Prop -> State CollectStorage Prop
findStoragePropComp p = go2 p
  where
    go2 :: Prop -> State CollectStorage (Prop)
    go2 = \case
      PNeg x -> go2 x
      e@(PEq (Lit val) (SLoad {})) -> do
        s <- get
        put (s {vals=Set.insert val s.vals} :: CollectStorage)
        pure e
      e@(PLT (Lit val) (SLoad {})) -> do
        s <- get
        put (s {vals=Set.insert val s.vals} :: CollectStorage)
        pure e
      (PGT a@(Lit _) b@(SLoad {})) -> go2 (PLT a b)
      (PGEq a@(Lit _) b@(SLoad {})) -> go2 (PLT a b)
      (PLEq a@(Lit _) b@(SLoad {})) -> go2 (PLT a b)
      e -> pure e

findStoragePropInner :: Prop -> State CollectStorage Prop
findStoragePropInner p = mapPropM go p
  where
    go :: forall a. Expr a -> State CollectStorage (Expr a)
    go = \case
      e@(AbstractStore a idx) -> do
        s <- get
        put s {addrs=Set.insert (a, idx) s.addrs}
        pure e
      e@(SLoad (Lit val) _) -> do
        s <- get
        put s {keys=Set.insert val s.keys}
        pure e
      e@(SStore _ (Lit val) _) -> do
        s <- get
        put (s {vals=Set.insert val s.vals} :: CollectStorage)
        pure e
      e -> pure e

-- Var value and TX value generation
getvals :: CollectVars -> Gen (Map (Expr EWord) W256)
getvals vars = do
    bufs <- go (Set.toList vars.vars) mempty
    addTxStuff bufs
  where
    addTxStuff :: Map (Expr EWord) W256 -> Gen (Map (Expr EWord) W256)
    addTxStuff a = do
      val <- frequency [ (20, pure 0)
                       , (1, getRndW256)
                       ]
      pure $ Map.insert TxValue val a
    go :: [Expr EWord] -> Map (Expr EWord) W256 -> Gen (Map (Expr EWord) W256)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      pickKnown :: Bool <- arbitrary
      val <- if (not pickKnown) || (null vars.vals) then do getRndW256
                                                    else elements $ Set.toList (vars.vals)
      go ax (Map.insert a val valMap)

-- Storage value generation
getStores :: CollectStorage -> Gen (Map (Expr EAddr) (Map W256 W256))
getStores storesLoads = go (Set.toList storesLoads.addrs) mempty
  where
    go :: [(Expr EAddr, Maybe W256)] -> Map (Expr EAddr) (Map W256 W256) -> Gen (Map (Expr EAddr) (Map W256 W256))
    go [] addrToValsMap = pure addrToValsMap
    go ((addr, _):ax) addrToValsMap = do
      -- number of elements inserted into storage
      numElems :: Int <- frequency [(1, pure 0)
                                   ,(10, choose (1, 10))
                                   ,(1, choose (11, 100))
                                   ]
      l <- replicateM numElems oneWrite
      go ax (Map.insert addr (Map.fromList l) addrToValsMap)
        where
          oneWrite :: Gen (W256, W256)
          oneWrite = do
                    a <- getRndElem storesLoads.keys
                    b <- frequency [(1, getRndW256)
                                   ,(3, elements $ Set.toList storesLoads.vals)
                                   ]
                    pure (fromMaybe (0::W256) a, b)
    getRndElem :: Set W256 -> Gen (Maybe W256)
    getRndElem choices = if null choices then pure Nothing
                         else do fmap Just $ elements $ Set.toList choices

-- Buf value generation
getBufs :: [Expr Buf] -> Gen (Map (Expr Buf) SMT.BufModel)
getBufs bufs = go bufs mempty
  where
    go :: [Expr Buf] -> Map (Expr Buf) SMT.BufModel -> Gen (Map (Expr Buf) SMT.BufModel)
    go [] valMap = pure valMap
    go (a:ax) valMap = do
      bytes :: [Word8] <- frequency [
              (1, do
                x :: Int <- choose (1, 100)
                replicateM x arbitrary)
            , (1, replicateM 0 arbitrary)
       ]
      go ax (Map.insert a (SMT.Flat $ BS.pack bytes) valMap)

getRndW256 :: Gen W256
getRndW256 = do
      val <- replicateM 32 arbitrary
      pure $ bytesToW256 val
