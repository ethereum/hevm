{-# LANGUAGE ImplicitParams #-}

module EVM.UnitTest where

import EVM
import EVM.ABI
import EVM.SMT
import EVM.Solvers
import EVM.Dapp
import EVM.Effects
import EVM.Exec
import EVM.Expr (readStorage')
import EVM.Expr qualified as Expr
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified as Fetch
import EVM.Format
import EVM.Solidity
import EVM.SymExec (defaultVeriOpts, symCalldata, verify, isQed, extractCex, runExpr, prettyCalldata, panicMsg, VeriOpts(..), flattenExpr, isUnknown, isError, groupIssues)
import EVM.Types
import EVM.Transaction (initTx)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper

import Control.Monad (void, when, forM, forM_)
import Control.Monad.ST (RealWorld, ST, stToIO)
import Control.Monad.State.Strict (execState, get, put, liftIO)
import Optics.Core
import Optics.State
import Optics.State.Operators
import Data.Binary.Get (runGet)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as BSLazy
import Data.Decimal (DecimalRaw(..))
import Data.Foldable (toList)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.Text (isPrefixOf, stripSuffix, intercalate, Text, pack, unpack)
import Data.Text qualified as Text
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as Text
import Data.Word (Word64)
import GHC.Natural
import System.IO (hFlush, stdout)
import Witch (unsafeInto, into)

data UnitTestOptions s = UnitTestOptions
  { rpcInfo     :: Fetch.RpcInfo
  , solvers     :: SolverGroup
  , verbose     :: Maybe Int
  , maxIter     :: Maybe Integer
  , askSmtIters :: Integer
  , smtTimeout  :: Maybe Natural
  , solver      :: Maybe Text
  , match       :: Text
  , dapp        :: DappInfo
  , testParams  :: TestVMParams
  , ffiAllowed  :: Bool
  }

data TestVMParams = TestVMParams
  { address       :: Expr EAddr
  , caller        :: Expr EAddr
  , origin        :: Expr EAddr
  , gasCreate     :: Word64
  , gasCall       :: Word64
  , baseFee       :: W256
  , priorityFee   :: W256
  , balanceCreate :: W256
  , coinbase      :: Expr EAddr
  , number        :: W256
  , timestamp     :: W256
  , gaslimit      :: Word64
  , gasprice      :: W256
  , maxCodeSize   :: W256
  , prevrandao    :: W256
  , chainId       :: W256
  }

defaultGasForCreating :: Word64
defaultGasForCreating = 0xffffffffffff

defaultGasForInvoking :: Word64
defaultGasForInvoking = 0xffffffffffff

defaultBalanceForTestContract :: W256
defaultBalanceForTestContract = 0xffffffffffffffffffffffff

defaultMaxCodeSize :: W256
defaultMaxCodeSize = 0xffffffff

type ABIMethod = Text

-- | Used in various places for dumping traces
writeTraceDapp :: App m => DappInfo -> VM t RealWorld -> m ()
writeTraceDapp dapp vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ Text.writeFile "VM.trace" (showTraceTree dapp vm)

writeTrace :: App m => VM t RealWorld -> m ()
writeTrace vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ writeFile "VM.trace" (show $ traceForest vm)

-- | Generate VeriOpts from UnitTestOptions
makeVeriOpts :: UnitTestOptions s -> VeriOpts
makeVeriOpts opts =
   defaultVeriOpts { maxIter = opts.maxIter
                   , askSmtIters = opts.askSmtIters
                   , rpcInfo = opts.rpcInfo
                   }

-- | Top level CLI endpoint for hevm test
unitTest :: App m => UnitTestOptions RealWorld -> Contracts -> m Bool
unitTest opts (Contracts cs) = do
  let unitTests = findUnitTests opts.match $ Map.elems cs
  results <- concatMapM (runUnitTestContract opts cs) unitTests
  pure $ and results

-- | Assuming a constructor is loaded, this stepper will run the constructor
-- to create the test contract, give it an initial balance, and run `setUp()'.
initializeUnitTest :: UnitTestOptions s -> SolcContract -> Stepper Concrete s ()
initializeUnitTest opts theContract = do

  let addr = opts.testParams.address

  Stepper.evm $ do
    -- Make a trace entry for running the constructor
    pushTrace (EntryTrace "constructor")

  -- Constructor is loaded; run until it returns code
  void Stepper.execFully

  Stepper.evm $ do
    -- Give a balance to the test target
    #env % #contracts % ix addr % #balance %= (`Expr.add` (Lit opts.testParams.balanceCreate))

    -- call setUp(), if it exists, to initialize the test contract
    let theAbi = theContract.abiMap
        setUp  = abiKeccak (encodeUtf8 "setUp()")

    when (isJust (Map.lookup setUp theAbi)) $ do
      abiCall opts.testParams (Left ("setUp()", emptyAbi))
      popTrace
      pushTrace (EntryTrace "setUp()")

  -- Let `setUp()' run to completion
  res <- Stepper.execFully
  Stepper.evm $ case res of
    Left e -> pushTrace (ErrorTrace e)
    _ -> popTrace

runUnitTestContract
  :: App m
  => UnitTestOptions RealWorld
  -> Map Text SolcContract
  -> (Text, [Sig])
  -> m [Bool]
runUnitTestContract
  opts@(UnitTestOptions {..}) contractMap (name, testSigs) = do

  -- Print a header
  liftIO $ putStrLn $ "\nChecking " ++ show (length testSigs) ++ " function(s) in contract " ++ unpack name

  -- Look for the wanted contract by name from the Solidity info
  case Map.lookup name contractMap of
    Nothing ->
      -- Fail if there's no such contract
      internalError $ "Contract " ++ unpack name ++ " not found"

    Just theContract -> do
      -- Construct the initial VM and begin the contract's constructor
      vm0 :: VM Concrete RealWorld <- liftIO $ stToIO $ initialUnitTestVm opts theContract
      vm1 <- Stepper.interpret (Fetch.oracle solvers rpcInfo) vm0 $ do
        Stepper.enter name
        initializeUnitTest opts theContract
        Stepper.evm get

      writeTraceDapp dapp vm1
      case vm1.result of
        Just (VMFailure _) -> liftIO $ do
          Text.putStrLn "\x1b[31m[BAIL]\x1b[0m setUp() "
          tick $ failOutput vm1 opts "setUp()"
          pure [False]
        Just (VMSuccess _) -> do
          forM testSigs $ \s -> symRun opts vm1 s
        _ -> internalError "setUp() did not end with a result"

-- | Define the thread spawner for symbolic tests
symRun :: App m => UnitTestOptions RealWorld -> VM Concrete RealWorld -> Sig -> m Bool
symRun opts@UnitTestOptions{..} vm (Sig testName types) = do
    liftIO $ putStrLn $ "\x1b[96m[RUNNING]\x1b[0m " <> Text.unpack testName
    let cd = symCalldata testName types [] (AbstractBuf "txdata")
        shouldFail = "proveFail" `isPrefixOf` testName
        testContract store = fromMaybe (internalError "test contract not found in state") (Map.lookup vm.state.contract store)

    -- define postcondition depending on `shouldFail`
    -- We directly encode the failure conditions from failed() in ds-test since this is easier to encode than a call into failed()
    -- we need to read from slot 0 in the test contract and mask it with 0x10 to get the value of _failed
    -- we don't need to do this when reading the failed from the cheatcode address since we don't do any packing there
    let failed store = case Map.lookup cheatCode store of
          Just cheatContract -> readStorage' (Lit 0x6661696c65640000000000000000000000000000000000000000000000000000) cheatContract.storage .== Lit 1
          Nothing -> And (readStorage' (Lit 0) (testContract store).storage) (Lit 2) .== Lit 2
        postcondition = curry $ case shouldFail of
          True -> \(_, post) -> case post of
                                  Success _ _ _ store -> failed store
                                  _ -> PBool True
          False -> \(_, post) -> case post of
                                   Success _ _ _ store -> PNeg (failed store)
                                   Failure _ _ (Revert msg) -> case msg of
                                     ConcreteBuf b -> PBool $ b /= panicMsg 0x01
                                     b -> b ./= ConcreteBuf (panicMsg 0x01)
                                   Failure _ _ _ -> PBool True
                                   Partial _ _ _ -> PBool True
                                   _ -> internalError "Invalid leaf node"

    vm' <- Stepper.interpret (Fetch.oracle solvers rpcInfo) vm $
      Stepper.evm $ do
        pushTrace (EntryTrace testName)
        makeTxCall testParams cd
        get
    writeTraceDapp dapp vm'

    -- check postconditions against vm
    (e, results) <- verify solvers (makeVeriOpts opts) (symbolify vm') (Just postcondition)
    let allReverts = not . (any Expr.isSuccess) . flattenExpr $ e
    when (any isUnknown results || any isError results) $ liftIO $ do
      putStrLn $ "      \x1b[33mWARNING\x1b[0m: hevm was only able to partially explore the test " <> Text.unpack testName <> " due to: ";
      forM_ (groupIssues (filter isError results)) $ \(num, str) -> putStrLn $ "      " <> show num <> "x -> " <> str
      forM_ (groupIssues (filter isUnknown results)) $ \(num, str) -> putStrLn $ "      " <> show num <> "x -> " <> str

    -- display results
    if all isQed results
    then if allReverts && (not shouldFail)
         then do
           liftIO $ putStr $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n" <> Text.unpack allBranchRev
           pure False
         else do
           liftIO $ putStr $ "   \x1b[32m[PASS]\x1b[0m " <> Text.unpack testName <> "\n"
           pure True
    else do
      -- not all is Qed
      let x = mapMaybe extractCex results
      let y = symFailure opts testName (fst cd) types x
      liftIO $ putStr $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n" <> Text.unpack y
      pure False

allBranchRev :: Text
allBranchRev = intercalate "\n"
  [ Text.concat $ indentLines 3 <$>
      [ "Reason:"
      , "  No reachable assertion violations, but all branches reverted"
      , "  Prefix this testname with `proveFail` if this is expected"
      ]
  ]
symFailure :: UnitTestOptions RealWorld -> Text -> Expr Buf -> [AbiType] -> [(Expr End, SMTCex)] -> Text
symFailure UnitTestOptions {..} testName cd types failures' =
  mconcat
    [ Text.concat $ indentLines 3 . mkMsg <$> failures'
    ]
    where
      showRes = \case
        Success _ _ _ _ -> if "proveFail" `isPrefixOf` testName
                           then "Successful execution"
                           else "Failed: DSTest Assertion Violation"
        res ->
          let ?context = dappContext (traceContext res)
          in Text.pack $ prettyvmresult res
      mkMsg (leaf, cex) = intercalate "\n" $
        ["Counterexample:"
        ,"  result:   " <> showRes leaf
        ,"  calldata: " <> let ?context = dappContext (traceContext leaf)
                           in prettyCalldata cex cd testName types
        ] <> verbText leaf
      verbText leaf = case verbose of
            Just _ -> [Text.unlines [ indentLines 2 (showTraceTree' dapp leaf)]]
            _ -> mempty
      dappContext TraceContext { contracts, labels } =
        DappContext { info = dapp, contracts, labels }

execSymTest :: UnitTestOptions RealWorld -> ABIMethod -> (Expr Buf, [Prop]) -> Stepper Symbolic RealWorld (Expr End)
execSymTest UnitTestOptions{ .. } method cd = do
  -- Set up the call to the test method
  Stepper.evm $ do
    makeTxCall testParams cd
    pushTrace (EntryTrace method)
  -- Try running the test method
  runExpr

checkSymFailures :: VMOps t => UnitTestOptions RealWorld -> Stepper t RealWorld (VM t RealWorld)
checkSymFailures UnitTestOptions { .. } = do
  -- Ask whether any assertions failed
  Stepper.evm $ do
    popTrace
    abiCall testParams (Left ("failed()", emptyAbi))
  Stepper.runFully

indentLines :: Int -> Text -> Text
indentLines n s =
  let p = Text.replicate n " "
  in Text.unlines (map (p <>) (Text.lines s))

passOutput :: VM t s -> UnitTestOptions s -> Text -> Text
passOutput vm UnitTestOptions { .. } testName =
  let ?context = DappContext { info = dapp
                             , contracts = vm.env.contracts
                             , labels = vm.labels }
  in let v = fromMaybe 0 verbose
  in if (v > 1) then
    mconcat
      [ "Success: "
      , fromMaybe "" (stripSuffix "()" testName)
      , "\n"
      , if (v > 2) then indentLines 2 (showTraceTree dapp vm) else ""
      , indentLines 2 (formatTestLogs dapp.eventMap vm.logs)
      , "\n"
      ]
    else ""

failOutput :: VM t s -> UnitTestOptions s -> Text -> Text
failOutput vm UnitTestOptions { .. } testName =
  let ?context = DappContext { info = dapp
                             , contracts = vm.env.contracts
                             , labels = vm.labels }
  in mconcat
  [ "Failure: "
  , fromMaybe "" (stripSuffix "()" testName)
  , "\n"
  , case verbose of
      Just _ -> indentLines 2 (showTraceTree dapp vm)
      _ -> ""
  , indentLines 2 (formatTestLogs dapp.eventMap vm.logs)
  , "\n"
  ]

formatTestLogs :: (?context :: DappContext) => Map W256 Event -> [Expr Log] -> Text
formatTestLogs events xs =
  case catMaybes (toList (fmap (formatTestLog events) xs)) of
    [] -> "\n"
    ys -> "\n" <> intercalate "\n" ys <> "\n\n"

-- Here we catch and render some special logs emitted by ds-test,
-- with the intent to then present them in a separate view to the
-- regular trace output.
formatTestLog :: (?context :: DappContext) => Map W256 Event -> Expr Log -> Maybe Text
formatTestLog _ (LogEntry _ _ []) = Nothing
formatTestLog _ (GVar _) = internalError "unexpected global variable"
formatTestLog events (LogEntry _ args (topic:_)) =
  case maybeLitWord topic >>= \t1 -> (Map.lookup t1 events) of
    Nothing -> Nothing
    Just (Event name _ argInfos) ->
      case (name <> parenthesise (abiTypeSolidity <$> argTypes)) of
        "log(string)" -> Just $ unquote $ showValue AbiStringType args

        -- log_named_x(string, x)
        "log_named_bytes32(string, bytes32)" -> log_named
        "log_named_address(string, address)" -> log_named
        "log_named_int(string, int256)"      -> log_named
        "log_named_uint(string, uint256)"    -> log_named
        "log_named_bytes(string, bytes)"     -> log_named
        "log_named_string(string, string)"   -> log_named

        -- log_named_decimal_x(string, uint, x)
        "log_named_decimal_int(string, int256, uint256)"   -> log_named_decimal
        "log_named_decimal_uint(string, uint256, uint256)" -> log_named_decimal

        -- log_x(x)
        "log_bytes32(bytes32)" -> log_unnamed
        "log_address(address)" -> log_unnamed
        "log_int(int256)"      -> log_unnamed
        "log_uint(uint256)"    -> log_unnamed
        "log_bytes(bytes)"     -> log_unnamed
        "log_string(string)"   -> log_unnamed

        -- log_named_x(bytes32, x), as used in older versions of ds-test.
        -- bytes32 are opportunistically represented as strings in Format.hs
        "log_named_bytes32(bytes32, bytes32)" -> log_named
        "log_named_address(bytes32, address)" -> log_named
        "log_named_int(bytes32, int256)"      -> log_named
        "log_named_uint(bytes32, uint256)"    -> log_named

        _ -> Nothing

        where
          argTypes = [argType | (_, argType, NotIndexed) <- argInfos]
          unquote = Text.dropAround (\c -> c == '"' || c == '«' || c == '»')
          log_unnamed =
            Just $ showValue (head argTypes) args
          log_named =
            let (key, val) = case take 2 (textValues argTypes args) of
                  [k, v] -> (k, v)
                  _ -> internalError "shouldn't happen"
            in Just $ unquote key <> ": " <> val
          showDecimal dec val =
            pack $ show $ Decimal (unsafeInto dec) val
          log_named_decimal =
            case args of
              (ConcreteBuf b) ->
                case toList $ runGet (getAbiSeq (length argTypes) argTypes) (BSLazy.fromStrict b) of
                  [key, (AbiUInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  [key, (AbiInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  _ -> Nothing
              _ -> Just "<symbolic decimal>"

abiCall :: VMOps t => TestVMParams -> Either (Text, AbiValue) ByteString -> EVM t s ()
abiCall params args =
  let cd = case args of
        Left (sig, args') -> abiMethod sig args'
        Right b -> b
  in makeTxCall params (ConcreteBuf cd, [])

makeTxCall :: VMOps t => TestVMParams -> (Expr Buf, [Prop]) -> EVM t s ()
makeTxCall params (cd, cdProps) = do
  resetState
  assign (#tx % #isCreate) False
  execState (loadContract params.address) <$> get >>= put
  assign (#state % #calldata) cd
  #constraints %= (<> cdProps)
  assign (#state % #caller) params.caller
  assign (#state % #gas) (toGas params.gasCall)
  origin <- fromMaybe (initialContract (RuntimeCode (ConcreteRuntimeCode ""))) <$> use (#env % #contracts % at params.origin)
  let insufficientBal = maybe False (\b -> b < params.gasprice * (into params.gasCall)) (maybeLitWord origin.balance)
  when insufficientBal $ internalError "insufficient balance for gas cost"
  vm <- get
  put $ initTx vm

initialUnitTestVm :: VMOps t => UnitTestOptions s -> SolcContract -> ST s (VM t s)
initialUnitTestVm (UnitTestOptions {..}) theContract = do
  vm <- makeVm $ VMOpts
           { contract = initialContract (InitCode theContract.creationCode mempty)
           , otherContracts = []
           , calldata = mempty
           , value = Lit 0
           , address = testParams.address
           , caller = testParams.caller
           , origin = testParams.origin
           , gas = toGas testParams.gasCreate
           , gaslimit = testParams.gasCreate
           , coinbase = testParams.coinbase
           , number = testParams.number
           , timestamp = Lit testParams.timestamp
           , blockGaslimit = testParams.gaslimit
           , gasprice = testParams.gasprice
           , baseFee = testParams.baseFee
           , priorityFee = testParams.priorityFee
           , maxCodeSize = testParams.maxCodeSize
           , prevRandao = testParams.prevrandao
           , schedule = feeSchedule
           , chainId = testParams.chainId
           , create = True
           , baseState = EmptyBase
           , txAccessList = mempty -- TODO: support unit test access lists???
           , allowFFI = ffiAllowed
           , freshAddresses = 0
           , beaconRoot = 0
           }
  let creator =
        initialContract (RuntimeCode (ConcreteRuntimeCode ""))
          & set #nonce (Just 1)
          & set #balance (Lit testParams.balanceCreate)
  pure $ vm & set (#env % #contracts % at (LitAddr ethrunAddress)) (Just creator)

paramsFromRpc :: Fetch.RpcInfo -> IO TestVMParams
paramsFromRpc rpcinfo = do
  (miner,ts,blockNum,ran,limit,base) <- case rpcinfo of
    Nothing -> pure (SymAddr "miner", Lit 0, 0, 0, 0, 0)
    Just (block, url) -> Fetch.fetchBlockFrom block url >>= \case
      Nothing -> internalError "Could not fetch block"
      Just Block{..} -> pure ( coinbase
                             , timestamp
                             , number
                             , prevRandao
                             , gaslimit
                             , baseFee
                             )
  let ts' = fromMaybe (internalError "received unexpected symbolic timestamp via rpc") (maybeLitWord ts)
  pure $ TestVMParams
    -- TODO: make this symbolic! It needs some tweaking to the way that our
    -- symbolic interpreters work to allow us to symbolically exec constructor initialization
    { address = LitAddr 0xacab
    , caller = SymAddr "caller"
    , origin = SymAddr "origin"
    , gasCreate = defaultGasForCreating
    , gasCall = defaultGasForInvoking
    , baseFee = base
    , priorityFee = 0
    , balanceCreate = defaultBalanceForTestContract
    , coinbase = miner
    , number = blockNum
    , timestamp = ts'
    , gaslimit = limit
    , gasprice = 0
    , maxCodeSize = defaultMaxCodeSize
    , prevrandao = ran
    , chainId = 99
    }

tick :: Text -> IO ()
tick x = Text.putStr x >> hFlush stdout
