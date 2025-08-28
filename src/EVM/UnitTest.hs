{-# LANGUAGE ImplicitParams #-}

module EVM.UnitTest where

import EVM
import EVM.ABI
import EVM.Solvers
import EVM.Dapp
import EVM.Effects
import EVM.Exec
import EVM.Expr qualified as Expr
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified as Fetch
import EVM.Format
import EVM.Solidity
import EVM.SymExec (defaultVeriOpts, symCalldata, verify, extractCex, prettyCalldata, panicMsg, VeriOpts(..), flattenExpr, groupIssues, groupPartials, IterConfig(..), defaultIterConf)
import EVM.Types
import EVM.Transaction (initTx)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.Expr (maybeLitWordSimp)
import Data.List (foldl')

import Control.Monad (void, when, forM, forM_)
import Control.Monad.ST (RealWorld, ST, stToIO)
import Control.Monad.State.Strict (execState, get, put, liftIO)
import Optics.Core
import Optics.State
import Optics.State.Operators
import Data.Binary.Get (runGet)
import Data.ByteString (ByteString)
import Data.ByteString.Char8 qualified as BS
import Data.ByteString.Internal (c2w)
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
import Data.Vector qualified as V
import Data.Char (ord)

data UnitTestOptions s = UnitTestOptions
  { rpcInfo     :: Fetch.RpcInfo
  , solvers     :: SolverGroup
  , maxIter     :: Maybe Integer
  , askSmtIters :: Integer
  , smtTimeout  :: Maybe Natural
  , match       :: Text
  , prefix      :: Text
  , dapp        :: DappInfo
  , testParams  :: TestVMParams
  , ffiAllowed  :: Bool
  , checkFailBit:: Bool
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
   defaultVeriOpts { iterConf = defaultIterConf {maxIter = opts.maxIter, askSmtIters = opts.askSmtIters }
                   , rpcInfo = opts.rpcInfo
                   }

-- | Top level CLI endpoint for hevm test
-- | Returns tuple of (No Cex, No warnings)
unitTest :: App m => UnitTestOptions RealWorld -> Contracts -> m (Bool, Bool)
unitTest opts (Contracts cs) = do
  let unitTestContrs = findUnitTests opts.prefix opts.match $ Map.elems cs
  conf <- readConfig
  when conf.debug $ liftIO $ do
    putStrLn $ "Found " ++ show (length unitTestContrs) ++ " unit test contract(s) to test:"
    let x = map (\(a,b) -> "  --> " <> a <> "  ---  functions: " <> (Text.pack $ show b)) unitTestContrs
    putStrLn $ unlines $ map Text.unpack x
  results <- concatMapM (runUnitTestContract opts cs) unitTestContrs
  when conf.debug $ liftIO $ putStrLn $ "unitTest individual results: " <> show results
  let (firsts, seconds) = unzip results
  pure (and firsts, and seconds)

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

-- Returns tuple of (No Cex, No warnings)
runUnitTestContract
  :: App m
  => UnitTestOptions RealWorld
  -> Map Text SolcContract
  -> (Text, [Sig])
  -> m [(Bool, Bool)]
runUnitTestContract
  opts@(UnitTestOptions {..}) contractMap (name, testSigs) = do
  liftIO $ putStrLn $ "Checking " ++ show (length testSigs) ++ " function(s) in contract " ++ unpack name

  -- Look for the wanted contract by name from the Solidity info
  case Map.lookup name contractMap of
    Nothing -> internalError $ "Contract " ++ unpack name ++ " not found"
    Just theContract -> do
      -- Construct the initial VM and begin the contract's constructor
      vm0 :: VM Concrete RealWorld <- liftIO $ stToIO $ initialUnitTestVm opts theContract
      vm1 <- Stepper.interpret (Fetch.oracle solvers rpcInfo) vm0 $ do
        Stepper.enter name
        initializeUnitTest opts theContract
        Stepper.evm get

      writeTraceDapp dapp vm1
      failOut <- failOutput vm1 opts "setUp()"
      case vm1.result of
        Just (VMFailure _) -> liftIO $ do
          Text.putStrLn "   \x1b[31m[BAIL]\x1b[0m setUp() "
          tick $ indentLines 3 failOut
          pure [(True, False)]
        Just (VMSuccess _) -> do
          forM testSigs $ \s -> symRun opts vm1 s
        _ -> internalError "setUp() did not end with a result"

-- Define the thread spawner for symbolic tests
-- Returns tuple of (No Cex, No warnings)
symRun :: App m => UnitTestOptions RealWorld -> VM Concrete RealWorld -> Sig -> m (Bool, Bool)
symRun opts@UnitTestOptions{..} vm (Sig testName types) = do
    let callSig = testName <> "(" <> (Text.intercalate "," (map abiTypeSolidity types)) <> ")"
    liftIO $ putStrLn $ "\x1b[96m[RUNNING]\x1b[0m " <> Text.unpack callSig
    cd <- symCalldata callSig types [] (AbstractBuf "txdata")
    let shouldFail = "proveFail" `isPrefixOf` callSig

    -- define postcondition depending on `shouldFail`
    let testContract store = fromMaybe (internalError "test contract not found in state") (Map.lookup vm.state.contract store)
        failed store = case Map.lookup cheatCode store of
          Just cheatContract -> Expr.readStorage' (Lit 0x6661696c65640000000000000000000000000000000000000000000000000000) cheatContract.storage .== Lit 1
          Nothing -> And (Expr.readStorage' (Lit 0) (testContract store).storage) (Lit 2) .== Lit 2
        postcondition = curry $ case shouldFail of
          True -> \(_, post) -> case post of
            Success _ _ _ store -> if opts.checkFailBit then failed store else PBool False
            _ -> PBool True
          False -> \(_, post) -> case post of
            Success _ _ _ store -> if opts.checkFailBit then PNeg (failed store) else PBool True
            Failure _ _ (UnrecognizedOpcode 0xfe) -> PBool False
            Failure _ _ (Revert msg) -> case msg of
              ConcreteBuf b ->
                -- NOTE: assertTrue/assertFalse does not have the double colon after "assertion failed"
                let assertFail = (selector "Error(string)" `BS.isPrefixOf` b) &&
                      ("assertion failed" `BS.isPrefixOf` (BS.drop txtOffset b))
                in if assertFail || b == panicMsg 0x01 then PBool False
                else PBool True
              _ -> symbolicFail msg
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
    (end, results) <- verify solvers (makeVeriOpts opts) (symbolify vm') (Just postcondition)
    let ends = flattenExpr end
    conf <- readConfig
    when conf.debug $ liftIO $ forM_ (filter Expr.isFailure ends) $ \case
      (Failure _ _ a) ->  putStrLn $ "   -> debug of func: " <> Text.unpack testName <> " Failure at the end of expr: " <> show a;
      _ -> internalError "cannot be, filtered for failure"

    -- display results
    let t = "the test " <> Text.unpack testName
    let warnings = any Expr.isPartial ends || any isUnknown results || any isError results
    let allReverts = not . (any Expr.isSuccess) $ ends
    let unexpectedAllRevert = allReverts && not shouldFail
    when conf.debug $ liftIO $ putStrLn $ "symRun -- (cex,warnings,unexpectedAllRevert): " <> show (any isCex results, warnings, unexpectedAllRevert)
    txtResult <- case (any isCex results, warnings, unexpectedAllRevert) of
      (False, False, False) -> do
        -- happy case
        pure $ "   \x1b[32m[PASS]\x1b[0m " <> Text.unpack testName <> "\n"
      (True, _, _) -> do
        -- there are counterexamples (and maybe other things, but Cex is most important)
        let x = mapMaybe extractCex results
        y <- symFailure opts testName (fst cd) types x
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n" <> Text.unpack y
      (_, True, _) -> do
        -- There are errors/unknowns/partials, we fail them
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n"
      (_, _, True) -> do
        -- No cexes/errors/unknowns/partials, but all branches reverted
        pure $ "   \x1b[31m[FAIL]\x1b[0m " <> Text.unpack testName <> "\n"
          <> "   No reachable assertion violations, but all branches reverted\n"
    liftIO $ putStr txtResult
    when (unexpectedAllRevert && (warnings || (any isCex results))) $ do
      -- if we display a FAILED due to Cex/warnings, we should also mention everything reverted
      liftIO $ putStrLn $ "   \x1b[33m[WARNING]\x1b[0m " <> Text.unpack testName <> " all branches reverted\n"
    liftIO $ printWarnings ends results t
    pure (not (any isCex results), not (warnings || unexpectedAllRevert))
    where
      -- The offset of the text is: the selector (4B), the offset value (aligned to 32B), and the length of the string (aligned to 32B)
      txtOffset = 4+32+32
      symbolicFail :: Expr Buf -> Prop
      symbolicFail e =
        let origTxt = "assertion failed"
            txtLen = length origTxt
            w8Txt = V.fromList $ map (fromIntegral . ord) origTxt
            panic = e == ConcreteBuf (panicMsg 0x01)
            concretePrefix = Expr.concretePrefix e
            assertFail =
              if (length concretePrefix < txtOffset+txtLen)
              then PAnd (symBytesEq 0 e (BS.unpack $ selector "Error(string)")) (symBytesEq txtOffset e origTxt)
              else PBool (V.drop txtOffset (V.take (txtLen+txtOffset) concretePrefix) == w8Txt)
        in PBool (not panic) .&& PNeg assertFail
      symBytesEq :: Int -> Expr Buf -> String -> Prop
      symBytesEq off buf str = let acc = go str buf off []
        in foldl' PAnd (PBool True) acc
        where
          go :: String -> Expr Buf -> Int -> [Prop] -> [Prop]
          go "" _ _ acc = acc
          go (a:ax) b n acc = go ax b (n+1) (PEq lhs rhs:acc)
            where
              lhs = LitByte (c2w a)
              rhs = Expr.readByte (Lit (fromIntegral n)) b
--
printWarnings :: GetUnknownStr b => [Expr 'End] -> [ProofResult a b] -> String -> IO ()
printWarnings e results testName = do
  when (any isUnknown results || any isError results || any Expr.isPartial e) $ do
    putStrLn $ "   \x1b[33m[WARNING]\x1b[0m hevm was only able to partially explore " <> testName <> " due to: ";
    forM_ (groupIssues (filter isError results)) $ \(num, str) -> putStrLn $ "      " <> show num <> "x -> " <> str
    forM_ (groupIssues (filter isUnknown results)) $ \(num, str) -> putStrLn $ "      " <> show num <> "x -> " <> str
    forM_ (groupPartials e) $ \(num, str) -> putStrLn $ "      " <> show num <> "x -> " <> str
  putStrLn ""

symFailure :: App m => UnitTestOptions RealWorld -> Text -> Expr Buf -> [AbiType] -> [(Expr End, SMTCex)] -> m Text
symFailure UnitTestOptions {..} testName cd types failures' = do
  conf <- readConfig
  pure $ mconcat [ Text.concat $ indentLines 3 . mkMsg conf <$> failures' ]
  where
      showRes = \case
        Success _ _ _ _ -> if "proveFail" `isPrefixOf` testName
                           then "Successful execution"
                           else "Failed: Test Assertion Violation"
        res ->
          let ?context = dappContext (traceContext res)
          in Text.pack $ prettyvmresult res
      mkMsg conf (leaf, cex) = intercalate "\n" $
        ["Counterexample:"
        ,"  calldata: " <> let ?context = dappContext (traceContext leaf)
                           in prettyCalldata cex cd testName types
        ,"  result:   " <> showRes leaf
        ] <> verbText conf leaf
      verbText conf leaf = if conf.verb <= 1 then mempty
                           else [Text.unlines [ indentLines 2 (showTraceTree' dapp leaf)]]
      dappContext TraceContext { contracts, labels } =
        DappContext { info = dapp, contracts, labels }

indentLines :: Int -> Text -> Text
indentLines n s =
  let p = Text.replicate n " "
  in Text.unlines (map (p <>) (Text.lines s))

failOutput :: App m => VM t s -> UnitTestOptions s -> Text -> m Text
failOutput vm UnitTestOptions { .. } testName = do
  conf <- readConfig
  let ?context = DappContext { info = dapp
                             , contracts = vm.env.contracts
                             , labels = vm.labels }
  pure $ mconcat
    [ "Failure: "
    , fromMaybe "" (stripSuffix "()" testName)
    , "\n"
    , if conf.verb <= 1 then ""
      else indentLines 2 (showTraceTree dapp vm)
    , indentLines 2 (formatTestLogs dapp.eventMap vm.logs)
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
  case maybeLitWordSimp topic >>= \t1 -> (Map.lookup t1 events) of
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
          headErr l = fromMaybe (internalError "shouldn't happen") $ listToMaybe l
          argTypes = [argType | (_, argType, NotIndexed) <- argInfos]
          unquote = Text.dropAround (\c -> c == '"' || c == '«' || c == '»')
          log_unnamed =
            Just $ showValue (headErr argTypes) args
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
  let insufficientBal = maybe False (\b -> b < params.gasprice * (into params.gasCall)) (maybeLitWordSimp origin.balance)
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
           , number = Lit testParams.number
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

paramsFromRpc :: forall m . App m => Fetch.RpcInfo -> m TestVMParams
paramsFromRpc rpcInfo = do
  (miner,ts,blockNum,ran,limit,base) <- case rpcInfo.blockNumURL of
    Nothing -> pure (SymAddr "miner", Lit 0, Lit 0, 0, 0, 0)
    Just (Fetch.Latest, url) -> fetch Fetch.Latest url
    Just (Fetch.BlockNumber block, url) -> case rpcInfo.mockBlock >>= Map.lookup block of
        Nothing -> fetch (Fetch.BlockNumber block) url
        Just b ->pure (b.coinbase
                      , b.timestamp
                      , b.number
                      , b.prevRandao
                      , b.gaslimit
                      , b.baseFee
                      )
  let ts' = fromMaybe (internalError "received unexpected symbolic timestamp via rpc") (maybeLitWordSimp ts)
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
    , number = forceLit blockNum
    , timestamp = ts'
    , gaslimit = limit
    , gasprice = 0
    , maxCodeSize = defaultMaxCodeSize
    , prevrandao = ran
    , chainId = 99
    }
  where
    fetch block url = do
      conf <- readConfig
      liftIO $ Fetch.fetchBlockFrom conf block url >>= \case
        Nothing -> internalError "Could not fetch block"
        Just Block{..} -> pure ( coinbase
                               , timestamp
                               , number
                               , prevRandao
                               , gaslimit
                               , baseFee
                               )


tick :: Text -> IO ()
tick x = Text.putStr x >> hFlush stdout
