{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TupleSections #-}

module Main where

import Prelude hiding (Word)

import EVM qualified
import EVM (contractcode, storage, origStorage, balance, nonce, initialContract, StorageBase(..))
import EVM.Concrete qualified as EVM
import EVM.Dapp (emptyDapp)
import EVM.Expr (litAddr)
import EVM.FeeSchedule qualified
import EVM.Fetch qualified
import EVM.Stepper qualified
import EVM.Solvers (withSolvers, Solver(Z3))
import EVM.Transaction
import EVM.TTY qualified as TTY
import EVM.Types

import Control.Arrow ((***), (&&&))
import Control.Lens
import Control.Monad
import Control.Monad.State.Strict (execStateT)
import Data.Aeson ((.:), (.:?), FromJSON (..))
import Data.Aeson qualified as JSON
import Data.Aeson.Types qualified as JSON
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as Lazy
import Data.ByteString.Lazy qualified as LazyByteString
import Data.List (isInfixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, isNothing, isJust)
import Data.Word (Word64)
import System.Environment (lookupEnv, getEnv)
import System.FilePath.Find qualified as Find
import System.FilePath.Posix (makeRelative, (</>))
import Witherable (Filterable, catMaybes)

import Test.Tasty
import Test.Tasty.ExpectedFailure
import Test.Tasty.HUnit

type Storage = Map W256 W256

data Which = Pre | Post

data Block = Block
  { blockCoinbase    :: Addr
  , blockDifficulty  :: W256
  , blockGasLimit    :: Word64
  , blockBaseFee     :: W256
  , blockNumber      :: W256
  , blockTimestamp   :: W256
  , blockTxs         :: [Transaction]
  } deriving Show

data Case = Case
  { testVmOpts      :: EVM.VMOpts
  , checkContracts  :: Map Addr (EVM.Contract, Storage)
  , testExpectation :: Map Addr (EVM.Contract, Storage)
  } deriving Show

data BlockchainCase = BlockchainCase
  { blockchainBlocks  :: [Block]
  , blockchainPre     :: Map Addr (EVM.Contract, Storage)
  , blockchainPost    :: Map Addr (EVM.Contract, Storage)
  , blockchainNetwork :: String
  } deriving Show

main :: IO ()
main = do
  tests <- prepareTests
  defaultMain tests

prepareTests :: IO TestTree
prepareTests = do
  repo <- getEnv "HEVM_ETHEREUM_TESTS_REPO"
  let testsDir = "BlockchainTests/GeneralStateTests"
  let dir = repo </> testsDir
  jsonFiles <- Find.find Find.always (Find.extension Find.==? ".json") dir
  putStrLn "Loading and parsing json files from ethereum-tests..."
  isCI <- isJust <$> lookupEnv "CI"
  let problematicTests = if isCI then commonProblematicTests <> ciProblematicTests else commonProblematicTests
  let ignoredFiles = if isCI then ciIgnoredFiles else []
  groups <- mapM (\f -> testGroup (makeRelative repo f) <$> (if any (`isInfixOf` f) ignoredFiles then pure [] else testsFromFile f problematicTests)) jsonFiles
  putStrLn "Loaded."
  pure $ testGroup "ethereum-tests" groups

testsFromFile :: String -> Map String (TestTree -> TestTree) -> IO [TestTree]
testsFromFile file problematicTests = do
  parsed <- parseBCSuite <$> LazyByteString.readFile file
  case parsed of
   Left "No cases to check." -> pure [] -- error "no-cases ok"
   Left _err -> pure [] -- error err
   Right allTests -> pure $
     (\(name, x) -> testCase' name $ runVMTest False (name, x)) <$> Map.toList allTests
  where
  testCase' name assertion =
    case Map.lookup name problematicTests of
      Just f -> f (testCase name assertion)
      Nothing -> testCase name assertion

-- CI has issues with some heaver tests, disable in bulk
ciIgnoredFiles :: [String]
ciIgnoredFiles = []

commonProblematicTests :: Map String (TestTree -> TestTree)
commonProblematicTests = Map.fromList
  [ ("loopMul_d0g0v0_London", ignoreTestBecause "hevm is too slow")
  , ("loopMul_d1g0v0_London", ignoreTestBecause "hevm is too slow")
  , ("loopMul_d2g0v0_London", ignoreTestBecause "hevm is too slow")
  , ("CALLBlake2f_MaxRounds_d0g0v0_London", ignoreTestBecause "very slow, bypasses timeout due time spent in FFI")
  ]

ciProblematicTests :: Map String (TestTree -> TestTree)
ciProblematicTests = Map.fromList
  [ ("Return50000_d0g1v0_London", ignoreTest)
  , ("Return50000_2_d0g1v0_London", ignoreTest)
  , ("randomStatetest177_d0g0v0_London", ignoreTest)
  , ("static_Call50000_d0g0v0_London", ignoreTest)
  , ("static_Call50000_d1g0v0_London", ignoreTest)
  , ("static_Call50000bytesContract50_1_d1g0v0_London", ignoreTest)
  , ("static_Call50000bytesContract50_2_d1g0v0_London", ignoreTest)
  , ("static_Return50000_2_d0g0v0_London", ignoreTest)
  , ("loopExp_d10g0v0_London", ignoreTest)
  , ("loopExp_d11g0v0_London", ignoreTest)
  , ("loopExp_d12g0v0_London", ignoreTest)
  , ("loopExp_d13g0v0_London", ignoreTest)
  , ("loopExp_d14g0v0_London", ignoreTest)
  , ("loopExp_d8g0v0_London", ignoreTest)
  , ("loopExp_d9g0v0_London", ignoreTest)
  ]

runVMTest :: Bool -> (String, Case) -> IO ()
runVMTest diffmode (_name, x) =
 do
  let vm0 = vmForCase x
  result <- execStateT (EVM.Stepper.interpret (EVM.Fetch.zero 0 (Just 0)) . void $ EVM.Stepper.execFully) vm0
  maybeReason <- checkExpectation diffmode x result
  case maybeReason of
    Just reason -> assertFailure reason
    Nothing -> pure ()

-- | Example usage:
-- | $ cabal new-repl ethereum-tests
-- | ghci> debugVMTest "BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest/twoOps.json" "twoOps_d0g0v0_London"
debugVMTest :: String -> String -> IO ()
debugVMTest file test = do
  repo <- getEnv "HEVM_ETHEREUM_TESTS_REPO"
  Right allTests <- parseBCSuite <$> LazyByteString.readFile (repo </> file)
  let x = case filter (\(name, _) -> name == test) $ Map.toList allTests of
        [(_, x')] -> x'
        _ -> error "test not found"
  let vm0 = vmForCase x
  result <- withSolvers Z3 0 Nothing $ \solvers ->
    TTY.runFromVM solvers Nothing Nothing emptyDapp vm0
  void $ checkExpectation True x result

splitEithers :: (Filterable f) => f (Either a b) -> (f a, f b)
splitEithers =
  (catMaybes *** catMaybes)
  . (fmap fst &&& fmap snd)
  . (fmap (preview _Left &&& preview _Right))

checkStateFail :: Bool -> Case -> EVM.VM -> (Bool, Bool, Bool, Bool) -> IO String
checkStateFail diff x vm (okMoney, okNonce, okData, okCode) = do
  let
    printContracts :: Map Addr (EVM.Contract, Storage) -> IO ()
    printContracts cs = putStrLn $ Map.foldrWithKey (\k (c, s) acc ->
      acc ++ show k ++ " : "
                   ++ (show . toInteger  $ (view nonce c)) ++ " "
                   ++ (show . toInteger  $ (view balance c)) ++ " "
                   ++ (printStorage s)
        ++ "\n") "" cs

    reason = map fst (filter (not . snd)
        [ ("bad-state",       okMoney || okNonce || okData  || okCode)
        , ("bad-balance", not okMoney || okNonce || okData  || okCode)
        , ("bad-nonce",   not okNonce || okMoney || okData  || okCode)
        , ("bad-storage", not okData  || okMoney || okNonce || okCode)
        , ("bad-code",    not okCode  || okMoney || okNonce || okData)
        ])
    check = x.checkContracts
    expected = x.testExpectation
    actual = Map.map (,mempty) $ view (EVM.env . EVM.contracts) vm -- . to (fmap (clearZeroStorage.clearOrigStorage))) vm
    printStorage = show -- TODO: fixme

  when diff $ do
    putStr (unwords reason)
    putStrLn "\nPre balance/state: "
    printContracts check
    putStrLn "\nExpected balance/state: "
    printContracts expected
    putStrLn "\nActual balance/state: "
    printContracts actual
  pure (unwords reason)

checkExpectation :: Bool -> Case -> EVM.VM -> IO (Maybe String)
checkExpectation diff x vm = do
  let expectation = x.testExpectation
      (okState, b2, b3, b4, b5) = checkExpectedContracts vm expectation
  if okState then
    pure Nothing
  else
    Just <$> checkStateFail diff x vm (b2, b3, b4, b5)

-- quotient account state by nullness
(~=) :: Map Addr (EVM.Contract, Storage) -> Map Addr (EVM.Contract, Storage) -> Bool
(~=) cs1 cs2 =
    let nullAccount = EVM.initialContract (EVM.RuntimeCode (EVM.ConcreteRuntimeCode ""))
        padNewAccounts cs ks = Map.union cs $ Map.fromList [(k, (nullAccount, mempty)) | k <- ks]
        padded_cs1 = padNewAccounts cs1 (Map.keys cs2)
        padded_cs2 = padNewAccounts cs2 (Map.keys cs1)
    in and $ zipWith (===) (Map.elems padded_cs1) (Map.elems padded_cs2)

(===) :: (EVM.Contract, Storage) -> (EVM.Contract, Storage) -> Bool
(c1, s1) === (c2, s2) =
  codeEqual && storageEqual && (c1 ^. balance == c2 ^. balance) && (c1 ^. nonce ==  c2 ^. nonce)
  where
    storageEqual = s1 == s2
    codeEqual = case (c1 ^. contractcode, c2 ^. contractcode) of
      (EVM.RuntimeCode a', EVM.RuntimeCode b') -> a' == b'
      _ -> error "unexpected code"

checkExpectedContracts :: EVM.VM -> Map Addr (EVM.Contract, Storage) -> (Bool, Bool, Bool, Bool, Bool)
checkExpectedContracts vm expected =
  let cs = zipWithStorages $ vm ^. EVM.env . EVM.contracts -- . to (fmap (clearZeroStorage.clearOrigStorage))
      expectedCs = clearStorage <$> expected
  in ( (expectedCs ~= cs)
     , (clearBalance <$> expectedCs) ~= (clearBalance <$> cs)
     , (clearNonce   <$> expectedCs) ~= (clearNonce   <$> cs)
     , (clearStorage <$> expectedCs) ~= (clearStorage <$> cs)
     , (clearCode    <$> expectedCs) ~= (clearCode    <$> cs)
     )
  where
  zipWithStorages = Map.mapWithKey (\addr c -> (c, lookupStorage addr))
  lookupStorage _ =
    case vm ^. EVM.env . EVM.storage of
      ConcreteStore _ -> mempty -- clearZeroStorage $ fromMaybe mempty $ Map.lookup (num addr) s
      EmptyStore -> mempty
      AbstractStore -> mempty -- error "AbstractStore, should this be handled?"
      SStore {} -> mempty -- error "SStore, should this be handled?"
      GVar _ -> error "unexpected global variable"

clearStorage :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearStorage (c, _) = (c, mempty)

clearBalance :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearBalance (c, s) = (set balance 0 c, s)

clearNonce :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearNonce (c, s) = (set nonce 0 c, s)

clearCode :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearCode (c, s) = (set contractcode (EVM.RuntimeCode (EVM.ConcreteRuntimeCode "")) c, s)

newtype ContractWithStorage = ContractWithStorage (EVM.Contract, Storage)

instance FromJSON ContractWithStorage where
  parseJSON (JSON.Object v) = do
    code <- (EVM.RuntimeCode . EVM.ConcreteRuntimeCode <$> (hexText <$> v .: "code"))
    storage' <- v .: "storage"
    balance' <- v .: "balance"
    nonce'   <- v .: "nonce"
    let c = EVM.initialContract code
              & balance .~ balance'
              & nonce   .~ nonce'
    return $ ContractWithStorage (c, storage')

  parseJSON invalid =
    JSON.typeMismatch "Contract" invalid

instance FromJSON BlockchainCase where
  parseJSON (JSON.Object v) = BlockchainCase
    <$> v .: "blocks"
    <*> parseContracts Pre v
    <*> parseContracts Post v
    <*> v .: "network"
  parseJSON invalid =
    JSON.typeMismatch "GeneralState test case" invalid

instance FromJSON Block where
  parseJSON (JSON.Object v) = do
    v'         <- v .: "blockHeader"
    txs        <- v .: "transactions"
    coinbase   <- addrField v' "coinbase"
    difficulty <- wordField v' "difficulty"
    gasLimit   <- word64Field v' "gasLimit"
    number     <- wordField v' "number"
    baseFee    <- fmap read <$> v' .:? "baseFeePerGas"
    timestamp  <- wordField v' "timestamp"
    return $ Block coinbase difficulty gasLimit (fromMaybe 0 baseFee) number timestamp txs
  parseJSON invalid =
    JSON.typeMismatch "Block" invalid

parseContracts ::
  Which -> JSON.Object -> JSON.Parser (Map Addr (EVM.Contract, Storage))
parseContracts w v =
  (Map.map unwrap) <$> (v .: which >>= parseJSON)
  where which = case w of
          Pre  -> "pre"
          Post -> "postState"
        unwrap (ContractWithStorage x) = x

parseBCSuite ::
  Lazy.ByteString -> Either String (Map String Case)
parseBCSuite x = case (JSON.eitherDecode' x) :: Either String (Map String BlockchainCase) of
  Left e        -> Left e
  Right bcCases -> let allCases = fromBlockchainCase <$> bcCases
                       keepError (Left e) = errorFatal e
                       keepError _        = True
                       filteredCases = Map.filter keepError allCases
                       (erroredCases, parsedCases) = splitEithers filteredCases
    in if Map.size erroredCases > 0
    then Left ("errored case: " ++ (show erroredCases))
    else if Map.size parsedCases == 0
    then Left "No cases to check."
    else Right parsedCases


data BlockchainError
  = TooManyBlocks
  | TooManyTxs
  | NoTxs
  | SignatureUnverified
  | InvalidTx
  | OldNetwork
  | FailedCreate
  deriving Show

errorFatal :: BlockchainError -> Bool
errorFatal TooManyBlocks = True
errorFatal TooManyTxs = True
errorFatal SignatureUnverified = True
errorFatal InvalidTx = True
errorFatal _ = False

fromBlockchainCase :: BlockchainCase -> Either BlockchainError Case
fromBlockchainCase (BlockchainCase blocks preState postState network) =
  case (blocks, network) of
    ([block], "London") -> case block.blockTxs of
      [tx] -> fromBlockchainCase' block tx preState postState
      []        -> Left NoTxs
      _         -> Left TooManyTxs
    ([_], _) -> Left OldNetwork
    (_, _)   -> Left TooManyBlocks

fromBlockchainCase' :: Block -> Transaction
                       -> Map Addr (EVM.Contract, Storage) -> Map Addr (EVM.Contract, Storage)
                       -> Either BlockchainError Case
fromBlockchainCase' block tx preState postState =
  let isCreate = isNothing tx.txToAddr in
  case (sender 1 tx, checkTx tx block preState) of
      (Nothing, _) -> Left SignatureUnverified
      (_, Nothing) -> Left (if isCreate then FailedCreate else InvalidTx)
      (Just origin, Just checkState) -> Right $ Case
        (EVM.VMOpts
         { vmoptContract      = EVM.initialContract theCode
         , vmoptCalldata      = (cd, [])
         , vmoptValue         = Lit tx.txValue
         , vmoptAddress       = toAddr
         , vmoptCaller        = litAddr origin
         , vmoptStorageBase   = Concrete
         , vmoptOrigin        = origin
         , vmoptGas           = tx.txGasLimit  - fromIntegral (txGasCost feeSchedule tx)
         , vmoptGaslimit      = tx.txGasLimit
         , vmoptBlockGaslimit = block.blockGasLimit
         , vmoptGasprice      = effectiveGasPrice
         , vmoptBaseFee       = block.blockBaseFee
         , vmoptPriorityFee   = priorityFee tx block.blockBaseFee
         , vmoptNumber        = block.blockNumber
         , vmoptTimestamp     = Lit block.blockTimestamp
         , vmoptCoinbase      = block.blockCoinbase
         , vmoptPrevRandao    = block.blockDifficulty
         , vmoptMaxCodeSize   = 24576
         , vmoptSchedule      = feeSchedule
         , vmoptChainId       = 1
         , vmoptCreate        = isCreate
         , vmoptTxAccessList  = txAccessMap tx
         , vmoptAllowFFI      = False
         })
        checkState
        postState
          where
            toAddr = fromMaybe (EVM.createAddress origin senderNonce) tx.txToAddr
            senderNonce = view (accountAt origin . nonce) (Map.map fst preState)
            feeSchedule = EVM.FeeSchedule.berlin
            toCode = Map.lookup toAddr preState
            theCode = if isCreate
                      then EVM.InitCode tx.txData mempty
                      else maybe (EVM.RuntimeCode (EVM.ConcreteRuntimeCode "")) (view contractcode . fst) toCode
            effectiveGasPrice = effectiveprice tx block.blockBaseFee
            cd = if isCreate
                 then mempty
                 else ConcreteBuf tx.txData

effectiveprice :: Transaction -> W256 -> W256
effectiveprice tx baseFee = priorityFee tx baseFee + baseFee

priorityFee :: Transaction -> W256 -> W256
priorityFee tx baseFee = let
    (txPrioMax, txMaxFee) = case tx.txType of
               EIP1559Transaction ->
                 let maxPrio = fromJust tx.txMaxPriorityFeeGas
                     maxFee = fromJust tx.txMaxFeePerGas
                 in (maxPrio, maxFee)
               _ ->
                 let gasPrice = fromJust tx.txGasPrice
                 in (gasPrice, gasPrice)
  in min txPrioMax (txMaxFee - baseFee)

maxBaseFee :: Transaction -> W256
maxBaseFee tx =
  case tx.txType of
     EIP1559Transaction -> fromJust tx.txMaxFeePerGas
     _ -> fromJust tx.txGasPrice

validateTx :: Transaction -> Block -> Map Addr (EVM.Contract, Storage) -> Maybe ()
validateTx tx block cs = do
  let cs' = Map.map fst cs
  origin        <- sender 1 tx
  originBalance <- (view balance) <$> view (at origin) cs'
  originNonce   <- (view nonce)   <$> view (at origin) cs'
  let gasDeposit = (effectiveprice tx block.blockBaseFee) * (num tx.txGasLimit)
  if gasDeposit + tx.txValue <= originBalance
    && tx.txNonce == originNonce && block.blockBaseFee <= maxBaseFee tx
  then Just ()
  else Nothing

checkTx :: Transaction -> Block -> Map Addr (EVM.Contract, Storage) -> Maybe (Map Addr (EVM.Contract, Storage))
checkTx tx block prestate = do
  origin <- sender 1 tx
  validateTx tx block prestate
  let isCreate   = isNothing tx.txToAddr
      senderNonce = view (accountAt origin . nonce) (Map.map fst prestate)
      toAddr      = fromMaybe (EVM.createAddress origin senderNonce) tx.txToAddr
      prevCode    = view (accountAt toAddr . contractcode) (Map.map fst prestate)
      prevNonce   = view (accountAt toAddr . nonce) (Map.map fst prestate)
  if isCreate && ((case prevCode of {EVM.RuntimeCode (EVM.ConcreteRuntimeCode b) -> not (BS.null b); _ -> True}) || (prevNonce /= 0))
  then mzero
  else
    return prestate

vmForCase :: Case -> EVM.VM
vmForCase x =
  let
    a = x.checkContracts
    cs = Map.map fst a
    st = Map.mapKeys num $ Map.map snd a
    vm = EVM.makeVm x.testVmOpts
      & set (EVM.env . EVM.contracts) cs
      & set (EVM.env . EVM.storage) (ConcreteStore st)
      & set (EVM.env . EVM.origStorage) st
  in
    initTx vm
