{-# Language DataKinds #-}
{-# Language ImplicitParams #-}

module EVM.UnitTest where

import Prelude hiding (Word)

import EVM hiding (Unknown, path)
import EVM.ABI
import EVM.Concrete
import EVM.SMT
import EVM.Solvers
import EVM.Dapp
import EVM.Debug (srcMapCodePos)
import EVM.Exec
import EVM.Expr (litAddr, readStorage', simplify)
import EVM.Expr qualified as Expr
import EVM.Facts qualified as Facts
import EVM.Facts.Git qualified as Git
import EVM.FeeSchedule qualified as FeeSchedule
import EVM.Fetch qualified as Fetch
import EVM.Format
import EVM.Solidity
import EVM.SymExec qualified as SymExec
import EVM.SymExec (defaultVeriOpts, symCalldata, verify, isQed, extractCex, runExpr, subModel, VeriOpts)
import EVM.Types hiding (Failure)
import EVM.Transaction (initTx)
import EVM.RLP
import EVM.Stepper (Stepper, interpret)
import EVM.Stepper qualified as Stepper

import Control.Monad.Operational qualified as Operational
import Optics.Core hiding (elements)
import Optics.State
import Optics.State.Operators
import Optics.Zoom
import Control.Monad.Par.Class (spawn_)
import Control.Monad.Par.Class qualified as Par
import Control.Monad.Par.IO (runParIO)
import Control.Monad.State.Strict hiding (state)
import Control.Monad.State.Strict qualified as State
import Data.ByteString.Lazy qualified as BSLazy
import Data.Binary.Get (runGet)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Decimal (DecimalRaw(..))
import Data.Either (isRight)
import Data.Foldable (toList)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, catMaybes, fromJust, isJust, fromMaybe, mapMaybe, isNothing)
import Data.MultiSet (MultiSet)
import Data.MultiSet qualified as MultiSet
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (isPrefixOf, stripSuffix, intercalate, Text, pack, unpack)
import Data.Text qualified as Text
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as Text
import Data.Vector (Vector)
import Data.Vector qualified as Vector
import Data.Word (Word32, Word64)
import GHC.Natural
import System.Environment (lookupEnv)
import System.IO (hFlush, stdout)
import Test.QuickCheck hiding (verbose)

data UnitTestOptions = UnitTestOptions
  { rpcInfo     :: Fetch.RpcInfo
  , solvers     :: SolverGroup
  , verbose     :: Maybe Int
  , maxIter     :: Maybe Integer
  , askSmtIters :: Maybe Integer
  , smtDebug    :: Bool
  , maxDepth    :: Maybe Int
  , smtTimeout  :: Maybe Natural
  , solver      :: Maybe Text
  , covMatch    :: Maybe Text
  , match       :: Text
  , fuzzRuns    :: Int
  , replay      :: Maybe (Text, BSLazy.ByteString)
  , vmModifier  :: VM -> VM
  , dapp        :: DappInfo
  , testParams  :: TestVMParams
  , ffiAllowed  :: Bool
  }

data TestVMParams = TestVMParams
  { address       :: Addr
  , caller        :: Addr
  , origin        :: Addr
  , gasCreate     :: Word64
  , gasCall       :: Word64
  , baseFee       :: W256
  , priorityFee   :: W256
  , balanceCreate :: W256
  , coinbase      :: Addr
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


-- | Generate VeriOpts from UnitTestOptions
makeVeriOpts :: UnitTestOptions -> VeriOpts
makeVeriOpts opts =
   defaultVeriOpts { SymExec.debug = opts.smtDebug
                   , SymExec.maxIter = opts.maxIter
                   , SymExec.askSmtIters = opts.askSmtIters
                   , SymExec.rpcInfo = opts.rpcInfo
                   }

-- | Top level CLI endpoint for dapp-test
dappTest :: UnitTestOptions -> String -> Maybe String -> IO Bool
dappTest opts solcFile cache' = do
  out <- liftIO $ readSolc solcFile
  case out of
    Just (contractMap, _) -> do
      let unitTests = findUnitTests opts.match $ Map.elems contractMap
      results <- concatMapM (runUnitTestContract opts contractMap) unitTests
      let (passing, vms) = unzip results
      case cache' of
        Nothing ->
          pure ()
        Just path ->
          -- merge all of the post-vm caches and save into the state
          let
            evmcache = mconcat [vm.cache | vm <- vms]
          in
            liftIO $ Git.saveFacts (Git.RepoAt path) (Facts.cacheFacts evmcache)

      return $ and passing
    Nothing ->
      error ("Failed to read Solidity JSON for `" ++ solcFile ++ "'")


-- | Assuming a constructor is loaded, this stepper will run the constructor
-- to create the test contract, give it an initial balance, and run `setUp()'.
initializeUnitTest :: UnitTestOptions -> SolcContract -> Stepper ()
initializeUnitTest opts theContract = do

  let addr = opts.testParams.address

  Stepper.evm $ do
    -- Maybe modify the initial VM, e.g. to load library code
    modify opts.vmModifier
    -- Make a trace entry for running the constructor
    pushTrace (EntryTrace "constructor")

  -- Constructor is loaded; run until it returns code
  void Stepper.execFully

  Stepper.evm $ do
    -- Give a balance to the test target
    #env % #contracts % ix addr % #balance %= (+ opts.testParams.balanceCreate)

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

-- | Assuming a test contract is loaded and initialized, this stepper
-- will run the specified test method and return whether it succeeded.
runUnitTest :: UnitTestOptions -> ABIMethod -> AbiValue -> Stepper Bool
runUnitTest a method args = do
  x <- execTestStepper a method args
  checkFailures a method x

execTestStepper :: UnitTestOptions -> ABIMethod -> AbiValue -> Stepper Bool
execTestStepper UnitTestOptions { .. } methodName' method = do
  -- Set up the call to the test method
  Stepper.evm $ do
    abiCall testParams (Left (methodName', method))
    pushTrace (EntryTrace methodName')
  -- Try running the test method
  Stepper.execFully >>= \case
     -- If we failed, put the error in the trace.
    Left e -> Stepper.evm (pushTrace (ErrorTrace e) >> popTrace) >> pure True
    _ -> pure False

exploreStep :: UnitTestOptions -> ByteString -> Stepper Bool
exploreStep UnitTestOptions{..} bs = do
  Stepper.evm $ do
    cs <- use (#env % #contracts)
    abiCall testParams (Right bs)
    let (Method _ inputs sig _ _) = fromMaybe (error "unknown abi call") $ Map.lookup (num $ word $ BS.take 4 bs) dapp.abiMap
        types = snd <$> inputs
    let ?context = DappContext dapp cs
    this <- fromMaybe (error "unknown target") <$> (use (#env % #contracts % at testParams.address))
    let name = maybe "" (contractNamePart . (.contractName)) $ lookupCode this.contractcode dapp
    pushTrace (EntryTrace (name <> "." <> sig <> "(" <> intercalate "," ((pack . show) <$> types) <> ")" <> showCall types (ConcreteBuf bs)))
  -- Try running the test method
  Stepper.execFully >>= \case
     -- If we failed, put the error in the trace.
    Left e -> Stepper.evm (pushTrace (ErrorTrace e) >> popTrace) >> pure True
    _ -> pure False

checkFailures :: UnitTestOptions -> ABIMethod -> Bool -> Stepper Bool
checkFailures UnitTestOptions { .. } method bailed = do
   -- Decide whether the test is supposed to fail or succeed
  let shouldFail = "testFail" `isPrefixOf` method
  if bailed then
    pure shouldFail
  else do
    -- Ask whether any assertions failed
    Stepper.evm $ do
      popTrace
      abiCall testParams $ Left ("failed()", emptyAbi)
    res <- Stepper.execFully
    case res of
      Right (ConcreteBuf r) ->
        let failed = case decodeAbiValue AbiBoolType (BSLazy.fromStrict r) of
              AbiBool f -> f
              _ -> error "fix me with better types"
        in pure (shouldFail == failed)
      c -> error $ "internal error: unexpected failure code: " <> show c

-- | Randomly generates the calldata arguments and runs the test
fuzzTest :: UnitTestOptions -> Text -> [AbiType] -> VM -> Property
fuzzTest opts@UnitTestOptions{..} sig types vm = forAllShow (genAbiValue (AbiTupleType $ Vector.fromList types)) (show . ByteStringS . encodeAbiValue)
  $ \args -> ioProperty $
    fst <$> runStateT (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo) (runUnitTest opts sig args)) vm

tick :: Text -> IO ()
tick x = Text.putStr x >> hFlush stdout

-- | This is like an unresolved source mapping.
data OpLocation = OpLocation
  { srcContract :: Contract
  , srcOpIx :: Int
  } deriving (Show)

instance Eq OpLocation where
  (==) (OpLocation a b) (OpLocation a' b') = b == b' && a.contractcode == a'.contractcode

instance Ord OpLocation where
  compare (OpLocation a b) (OpLocation a' b') = compare (a.contractcode, b) (a'.contractcode, b')

srcMapForOpLocation :: DappInfo -> OpLocation -> Maybe SrcMap
srcMapForOpLocation dapp (OpLocation contr opIx) = srcMap dapp contr opIx

type CoverageState = (VM, MultiSet OpLocation)

currentOpLocation :: VM -> OpLocation
currentOpLocation vm =
  case currentContract vm of
    Nothing ->
      error "internal error: why no contract?"
    Just c ->
      OpLocation
        c
        (fromMaybe (error "internal error: op ix") (vmOpIx vm))

execWithCoverage :: StateT CoverageState IO VMResult
execWithCoverage = do _ <- runWithCoverage
                      fromJust <$> use (_1 % #result)

runWithCoverage :: StateT CoverageState IO VM
runWithCoverage = do
  -- This is just like `exec` except for every instruction evaluated,
  -- we also increment a counter indexed by the current code location.
  vm0 <- use _1
  case vm0.result of
    Nothing -> do
      vm1 <- zoom _1 (State.state (runState exec1) >> get)
      zoom _2 (modify (MultiSet.insert (currentOpLocation vm1)))
      runWithCoverage
    Just _ -> pure vm0


interpretWithCoverage
  :: UnitTestOptions
  -> Stepper a
  -> StateT CoverageState IO a
interpretWithCoverage opts@UnitTestOptions{..} =
  eval . Operational.view

  where
    eval
      :: Operational.ProgramView Stepper.Action a
      -> StateT CoverageState IO a

    eval (Operational.Return x) =
      pure x

    eval (action Operational.:>>= k) =
      case action of
        Stepper.Exec ->
          execWithCoverage >>= interpretWithCoverage opts . k
        Stepper.Run ->
          runWithCoverage >>= interpretWithCoverage opts . k
        Stepper.Wait q ->
          do m <- liftIO ((Fetch.oracle solvers rpcInfo) q)
             zoom _1 (State.state (runState m)) >> interpretWithCoverage opts (k ())
        Stepper.Ask _ ->
          error "cannot make choice in this interpreter"
        Stepper.IOAct q ->
          zoom _1 (StateT (runStateT q)) >>= interpretWithCoverage opts . k
        Stepper.EVM m ->
          zoom _1 (State.state (runState m)) >>= interpretWithCoverage opts . k

coverageReport
  :: DappInfo
  -> MultiSet SrcMap
  -> Map Text (Vector (Int, ByteString))
coverageReport dapp cov =
  let
    sources :: SourceCache
    sources = dapp.sources

    allPositions :: Set (Text, Int)
    allPositions =
      ( Set.fromList
      . mapMaybe (srcMapCodePos sources)
      . toList
      $ mconcat
        ( dapp.solcByName
        & Map.elems
        & map (\x -> x.runtimeSrcmap <> x.creationSrcmap)
        )
      )

    srcMapCov :: MultiSet (Text, Int)
    srcMapCov = MultiSet.mapMaybe (srcMapCodePos sources) cov

    linesByName :: Map Text (Vector ByteString)
    linesByName =
      Map.fromList $ zipWith
          (\(name, _) lines' -> (name, lines'))
          sources.files
          sources.lines

    f :: Text -> Vector ByteString -> Vector (Int, ByteString)
    f name =
      Vector.imap
        (\i bs ->
           let
             n =
               if Set.member (name, i + 1) allPositions
               then MultiSet.occur (name, i + 1) srcMapCov
               else -1
           in (n, bs))
  in
    Map.mapWithKey f linesByName

coverageForUnitTestContract
  :: UnitTestOptions
  -> Map Text SolcContract
  -> SourceCache
  -> (Text, [(Test, [AbiType])])
  -> IO (MultiSet SrcMap)
coverageForUnitTestContract
  opts@(UnitTestOptions {..}) contractMap _ (name, testNames) = do

  -- Look for the wanted contract by name from the Solidity info
  case Map.lookup name contractMap of
    Nothing ->
      -- Fail if there's no such contract
      error $ "Contract " ++ unpack name ++ " not found"

    Just theContract -> do
      -- Construct the initial VM and begin the contract's constructor
      let vm0 = initialUnitTestVm opts theContract
      (vm1, cov1) <-
        execStateT
          (interpretWithCoverage opts
            (Stepper.enter name >> initializeUnitTest opts theContract))
          (vm0, mempty)

      -- Define the thread spawner for test cases
      let
        runOne' (test, _) = spawn_ . liftIO $ do
          (_, (_, cov)) <-
            runStateT
              (interpretWithCoverage opts (runUnitTest opts (extractSig test) emptyAbi))
              (vm1, mempty)
          pure cov
      -- Run all the test cases in parallel and gather their coverages
      covs <-
        runParIO (mapM runOne' testNames >>= mapM Par.get)

      -- Sum up all the coverage counts
      let cov2 = MultiSet.unions (cov1 : covs)

      pure (MultiSet.mapMaybe (srcMapForOpLocation dapp) cov2)

runUnitTestContract
  :: UnitTestOptions
  -> Map Text SolcContract
  -> (Text, [(Test, [AbiType])])
  -> IO [(Bool, VM)]
runUnitTestContract
  opts@(UnitTestOptions {..}) contractMap (name, testSigs) = do

  -- Print a header
  liftIO $ putStrLn $ "Running " ++ show (length testSigs) ++ " tests for "
    ++ unpack name

  -- Look for the wanted contract by name from the Solidity info
  case Map.lookup name contractMap of
    Nothing ->
      -- Fail if there's no such contract
      error $ "Contract " ++ unpack name ++ " not found"

    Just theContract -> do
      -- Construct the initial VM and begin the contract's constructor
      let vm0 = initialUnitTestVm opts theContract
      vm1 <-
        liftIO $ execStateT
          (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo)
            (Stepper.enter name >> initializeUnitTest opts theContract))
          vm0

      case vm1.result of
        Nothing -> error "internal error: setUp() did not end with a result"
        Just (VMFailure _) -> liftIO $ do
          Text.putStrLn "\x1b[31m[BAIL]\x1b[0m setUp() "
          tick "\n"
          tick (Data.Text.pack $ show $ failOutput vm1 opts "setUp()")
          pure [(False, vm1)]
        Just (VMSuccess _) -> do
          let

            runCache :: ([(Either Text Text, VM)], VM) -> (Test, [AbiType])
                        -> IO ([(Either Text Text, VM)], VM)
            runCache (results, vm) (test, types) = do
              (t, r, vm') <- runTest opts vm (test, types)
              liftIO $ Text.putStrLn t
              let vmCached = vm { cache = vm'.cache }
              pure (((r, vm'): results), vmCached)

          -- Run all the test cases and print their status updates,
          -- accumulating the vm cache throughout
          (details, _) <- foldM runCache ([], vm1) testSigs

          let running = [x | (Right x, _) <- details]
          let bailing = [x | (Left  x, _) <- details]

          liftIO $ do
            tick "\n"
            tick (Text.unlines (filter (not . Text.null) running))
            tick (Text.unlines bailing)

          pure [(isRight r, vm) | (r, vm) <- details]


runTest :: UnitTestOptions -> VM -> (Test, [AbiType]) -> IO (Text, Either Text Text, VM)
runTest opts@UnitTestOptions{} vm (ConcreteTest testName, []) = liftIO $ runOne opts vm testName emptyAbi
runTest opts@UnitTestOptions{..} vm (ConcreteTest testName, types) = liftIO $ case replay of
  Nothing ->
    fuzzRun opts vm testName types
  Just (sig, callData) ->
    if sig == testName
    then runOne opts vm testName $
      decodeAbiValue (AbiTupleType (Vector.fromList types)) callData
    else fuzzRun opts vm testName types
runTest opts@UnitTestOptions{..} vm (InvariantTest testName, []) = liftIO $ case replay of
  Nothing -> exploreRun opts vm testName []
  Just (sig, cds) ->
    if sig == testName
    then exploreRun opts vm testName (decodeCalls cds)
    else exploreRun opts vm testName []
runTest _ _ (InvariantTest _, types) = error $ "invariant testing with arguments: " <> show types <> " is not implemented (yet!)"
runTest opts vm (SymbolicTest testName, types) = symRun opts vm testName types

type ExploreTx = (Addr, Addr, ByteString, W256)

decodeCalls :: BSLazy.ByteString -> [ExploreTx]
decodeCalls b = fromMaybe (error "could not decode replay data") $ do
  List v <- rlpdecode $ BSLazy.toStrict b
  pure $ unList <$> v
  where
    unList (List [BS caller', BS target, BS cd, BS ts]) =
      (num (word caller'), num (word target), cd, word ts)
    unList _ = error "fix me with better types"

-- | Runs an invariant test, calls the invariant before execution begins
initialExplorationStepper :: UnitTestOptions -> ABIMethod -> [ExploreTx] -> [Addr] -> Int -> Stepper (Bool, RLP)
initialExplorationStepper opts'' testName replayData targets i = do
  let history = List []
  x <- runUnitTest opts'' testName emptyAbi
  if x
  then explorationStepper opts'' testName replayData targets history i
  else pure (False, history)

explorationStepper :: UnitTestOptions -> ABIMethod -> [ExploreTx] -> [Addr] -> RLP -> Int -> Stepper (Bool, RLP)
explorationStepper _ _ _ _ history 0  = return (True, history)
explorationStepper opts@UnitTestOptions{..} testName replayData targets (List history) i = do
 (caller', target, cd, timestamp') <-
   case preview (ix (i - 1)) replayData of
     Just v -> return v
     Nothing ->
      Stepper.evmIO $ do
       vm <- get
       let cs = vm.env.contracts
           noCode c = case c.contractcode of
             RuntimeCode (ConcreteRuntimeCode "") -> True
             RuntimeCode (SymbolicRuntimeCode c') -> null c'
             _ -> False
           mutable m = m.mutability `elem` [NonPayable, Payable]
           knownAbis :: Map Addr SolcContract
           knownAbis =
             -- exclude contracts without code
             Map.filter (not . BS.null . (.runtimeCode)) $
             -- exclude contracts without state changing functions
             Map.filter (not . null . Map.filter mutable . (.abiMap)) $
             -- exclude testing abis
             Map.filter (isNothing . preview (ix unitTestMarkerAbi) . (.abiMap)) $
             -- pick all contracts with known compiler artifacts
             fmap fromJust (Map.filter isJust $ Map.fromList [(addr, lookupCode c.contractcode dapp) | (addr, c)  <- Map.toList cs])
           selected = [(addr,
                        fromMaybe (error ("no src found for: " <> show addr)) $
                          lookupCode (fromMaybe (error $ "contract not found: " <> show addr) $
                            Map.lookup addr cs).contractcode dapp)
                       | addr  <- targets]
       -- go to IO and generate a random valid call to any known contract
       liftIO $ do
         -- select random contract
         (target, solcInfo) <- generate $ elements (if null targets then Map.toList knownAbis else selected)
         -- choose a random mutable method
         (_, (Method _ inputs sig _ _)) <- generate (elements $ Map.toList $ Map.filter mutable solcInfo.abiMap)
         let types = snd <$> inputs
         -- set the caller to a random address with 90% probability, 10% known EOA address
         let knownEOAs = Map.keys $ Map.filter noCode cs
         AbiAddress caller' <-
           if null knownEOAs
           then generate $ genAbiValue AbiAddressType
           else generate $ frequency
             [ (90, genAbiValue AbiAddressType)
             , (10, AbiAddress <$> elements knownEOAs)
             ]
         -- make a call with random valid data to the function
         args <- generate $ genAbiValue (AbiTupleType $ Vector.fromList types)
         let cd = abiMethod (sig <> "(" <> intercalate "," ((pack . show) <$> types) <> ")") args
         -- increment timestamp with random amount
         timepassed <- num <$> generate (arbitrarySizedNatural :: Gen Word32)
         let ts = fromMaybe (error "symbolic timestamp not supported here") $ maybeLitWord vm.block.timestamp
         return (caller', target, cd, num ts + timepassed)
 let opts' = opts { testParams = testParams {address = target, caller = caller', timestamp = timestamp'}}
     thisCallRLP = List [BS $ word160Bytes caller', BS $ word160Bytes target, BS cd, BS $ word256Bytes timestamp']
 -- set the timestamp
 Stepper.evm $ assign (#block % #timestamp) (Lit timestamp')
 -- perform the call
 bailed <- exploreStep opts' cd
 Stepper.evm popTrace
 let newHistory = if bailed then List history else List (thisCallRLP:history)
     opts'' = opts {testParams = testParams {timestamp = timestamp'}}
     carryOn = explorationStepper opts'' testName replayData targets newHistory (i - 1)
 -- if we didn't revert, run the test function
 if bailed
 then carryOn
 else
   do x <- runUnitTest opts'' testName emptyAbi
      if x
      then carryOn
      else pure (False, List (thisCallRLP:history))
explorationStepper _ _ _ _ _ _  = error "malformed rlp"

getTargetContracts :: UnitTestOptions -> Stepper [Addr]
getTargetContracts UnitTestOptions{..} = do
  vm <- Stepper.evm get
  let contract' = fromJust $ currentContract vm
      theAbi = (fromJust $ lookupCode contract'.contractcode dapp).abiMap
      setUp  = abiKeccak (encodeUtf8 "targetContracts()")
  case Map.lookup setUp theAbi of
    Nothing -> return []
    Just _ -> do
      Stepper.evm $ abiCall testParams (Left ("targetContracts()", emptyAbi))
      res <- Stepper.execFully
      case res of
        Right (ConcreteBuf r) ->
          let vs = case decodeAbiValue (AbiTupleType (Vector.fromList [AbiArrayDynamicType AbiAddressType])) (BSLazy.fromStrict r) of
                AbiTuple v -> v
                _ -> error "fix me with better types"
              targets = case Vector.toList vs of
                [AbiArrayDynamic AbiAddressType ts] ->
                  let unAbiAddress (AbiAddress a) = a
                      unAbiAddress _ = error "fix me with better types"
                  in unAbiAddress <$> Vector.toList ts
                _ -> error "fix me with better types"
          in pure targets
        _ -> error "internal error: unexpected failure code"

exploreRun :: UnitTestOptions -> VM -> ABIMethod -> [ExploreTx] -> IO (Text, Either Text Text, VM)
exploreRun opts@UnitTestOptions{..} initialVm testName replayTxs = do
  let oracle = Fetch.oracle solvers rpcInfo
  (targets, _) <- runStateT (EVM.Stepper.interpret oracle (getTargetContracts opts)) initialVm
  let depth = fromMaybe 20 maxDepth
  ((x, counterex), vm') <-
    if null replayTxs
    then
    foldM (\a@((success, _), _) _ ->
                       if success
                       then runStateT (EVM.Stepper.interpret oracle (initialExplorationStepper opts testName [] targets depth)) initialVm
                       else pure a)
                       ((True, (List [])), initialVm)  -- no canonical "post vm"
                       [0..fuzzRuns]
    else runStateT (EVM.Stepper.interpret oracle (initialExplorationStepper opts testName replayTxs targets (length replayTxs))) initialVm
  if x
  then return ("\x1b[32m[PASS]\x1b[0m " <> testName <>  " (runs: " <> (pack $ show fuzzRuns) <>", depth: " <> pack (show depth) <> ")",
               Right (passOutput vm' opts testName), vm') -- no canonical "post vm"
  else let replayText = if null replayTxs
                        then "\nReplay data: '(" <> pack (show testName) <> "," <> pack (show (show (ByteStringS $ rlpencode counterex))) <> ")'"
                        else " (replayed)"
       in return ("\x1b[31m[FAIL]\x1b[0m " <> testName <> replayText, Left  (failOutput vm' opts testName), vm')

execTest :: UnitTestOptions -> VM -> ABIMethod -> AbiValue -> IO (Bool, VM)
execTest opts@UnitTestOptions{..} vm testName args =
  runStateT
    (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo) (execTestStepper opts testName args))
    vm

-- | Define the thread spawner for normal test cases
runOne :: UnitTestOptions -> VM -> ABIMethod -> AbiValue -> IO (Text, Either Text Text, VM)
runOne opts@UnitTestOptions{..} vm testName args = do
  let argInfo = pack (if args == emptyAbi then "" else " with arguments: " <> show args)
  (bailed, vm') <- execTest opts vm testName args
  (success, vm'') <-
    runStateT
      (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo) (checkFailures opts testName bailed)) vm'
  if success
  then
     let gasSpent = num testParams.gasCall - vm'.state.gas
         gasText = pack $ show (fromIntegral gasSpent :: Integer)
     in
        pure
          ("\x1b[32m[PASS]\x1b[0m "
           <> testName <> argInfo <> " (gas: " <> gasText <> ")"
          , Right (passOutput vm'' opts testName)
          , vm''
          )
  else if bailed then
        pure
          ("\x1b[31m[BAIL]\x1b[0m "
           <> testName <> argInfo
          , Left (failOutput vm'' opts testName)
          , vm''
          )
      else
        pure
          ("\x1b[31m[FAIL]\x1b[0m "
           <> testName <> argInfo
          , Left (failOutput vm'' opts testName)
          , vm''
          )

-- | Define the thread spawner for property based tests
fuzzRun :: UnitTestOptions -> VM -> Text -> [AbiType] -> IO (Text, Either Text Text, VM)
fuzzRun opts@UnitTestOptions{..} vm testName types = do
  let args = Args{ replay          = Nothing
                 , maxSuccess      = fuzzRuns
                 , maxDiscardRatio = 10
                 , maxSize         = 100
                 , chatty          = isJust verbose
                 , maxShrinks      = maxBound
                 }
  quickCheckWithResult args (fuzzTest opts testName types vm) >>= \case
    Success numTests _ _ _ _ _ ->
      pure ("\x1b[32m[PASS]\x1b[0m "
             <> testName <> " (runs: " <> (pack $ show numTests) <> ")"
             -- this isn't the post vm we actually want, as we
             -- can't retrieve the correct vm from quickcheck
           , Right (passOutput vm opts testName)
           , vm
           )
    Failure _ _ _ _ _ _ _ _ _ _ failCase _ _ ->
      let abiValue = decodeAbiValue (AbiTupleType (Vector.fromList types)) $ BSLazy.fromStrict $ hexText (pack $ concat failCase)
          ppOutput = pack $ show abiValue
      in do
        -- Run the failing test again to get a proper trace
        vm' <- execStateT (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo) (runUnitTest opts testName abiValue)) vm
        pure ("\x1b[31m[FAIL]\x1b[0m "
               <> testName <> ". Counterexample: " <> ppOutput
               <> "\nRun:\n dapp test --replay '(\"" <> testName <> "\",\""
               <> (pack (concat failCase)) <> "\")'\nto test this case again, or \n dapp debug --replay '(\""
               <> testName <> "\",\"" <> (pack (concat failCase)) <> "\")'\nto debug it."
             , Left (failOutput vm' opts testName)
             , vm'
             )
    _ -> pure ("\x1b[31m[OOPS]\x1b[0m "
               <> testName
              , Left (failOutput vm opts testName)
              , vm
              )

-- | Define the thread spawner for symbolic tests
symRun :: UnitTestOptions -> VM -> Text -> [AbiType] -> IO (Text, Either Text Text, VM)
symRun opts@UnitTestOptions{..} vm testName types = do
    let cd = symCalldata testName types [] (AbstractBuf "txdata")
        shouldFail = "proveFail" `isPrefixOf` testName
        testContract = vm.state.contract

    -- define postcondition depending on `shouldFail`
    -- We directly encode the failure conditions from failed() in ds-test since this is easier to encode than a call into failed()
    -- we need to read from slot 0 in the test contract and mask it with 0x10 to get the value of _failed
    -- we don't need to do this when reading the failed from the cheatcode address since we don't do any packing there
    let failed store = (And (readStorage' (litAddr testContract) (Lit 0) store) (Lit 2) .== Lit 2)
                   .|| (readStorage' (litAddr cheatCode) (Lit 0x6661696c65640000000000000000000000000000000000000000000000000000) store .== Lit 1)
        postcondition = curry $ case shouldFail of
          True -> \(_, post) -> case post of
                                  Return _ _ store -> failed store
                                  _ -> PBool True
          False -> \(_, post) -> case post of
                                   Return _ _ store -> PNeg (failed store)
                                   _ -> PBool False

    (_, vm') <- runStateT
      (EVM.Stepper.interpret (Fetch.oracle solvers rpcInfo) (Stepper.evm $ do
          popTrace
          makeTxCall testParams cd
        )) vm

    -- check postconditions against vm
    (_, results) <- verify solvers (makeVeriOpts opts) vm' (Just postcondition)

    -- display results
    if all isQed results
    then do
      return ("\x1b[32m[PASS]\x1b[0m " <> testName, Right "", vm)
    else do
      let x = mapMaybe extractCex results
      let y = symFailure opts testName (fst cd) types x
      return ("\x1b[31m[FAIL]\x1b[0m " <> testName, Left y, vm)

symFailure :: UnitTestOptions -> Text -> Expr Buf -> [AbiType] -> [(Expr End, SMTCex)] -> Text
symFailure UnitTestOptions {..} testName cd types failures' =
  mconcat
    [ "Failure: "
    , testName
    , "\n\n"
    , intercalate "\n" $ indentLines 2 . mkMsg <$> failures'
    ]
    where
      ctx = DappContext { info = dapp, env = mempty }
      showRes = \case
                       Return _ _ _ -> if "proveFail" `isPrefixOf` testName
                                      then "Successful execution"
                                      else "Failed: DSTest Assertion Violation"
                       res ->
                         --let ?context = DappContext { _contextInfo = dapp, _contextEnv = vm ^?! EVM.env . EVM.contracts}
                         let ?context = ctx
                         in Text.pack $ prettyvmresult res
      mkMsg (leaf, cex) = Text.unlines
        ["Counterexample:"
        ,""
        ,"  result:   " <> showRes leaf
        ,"  calldata: " <> let ?context = ctx in prettyCalldata cex cd testName types
        , case verbose of
            --Just _ -> unlines
              --[ ""
              --, unpack $ indentLines 2 (showTraceTree dapp vm)
              --]
            _ -> ""
        ]

prettyCalldata :: (?context :: DappContext) => SMTCex -> Expr Buf -> Text -> [AbiType] -> Text
prettyCalldata cex buf sig types = head (Text.splitOn "(" sig) <> showCalldata cex types buf

showCalldata :: (?context :: DappContext) => SMTCex -> [AbiType] -> Expr Buf -> Text
showCalldata cex tps buf = "(" <> intercalate "," (fmap showVal vals) <> ")"
  where
    argdata = Expr.drop 4 $ simplify $ subModel cex buf
    vals = case decodeBuf tps argdata of
             CAbi v -> v
             _ -> error $ "Internal Error: unable to abi decode function arguments:\n" <> (Text.unpack $ formatExpr argdata)

showVal :: AbiValue -> Text
showVal (AbiBytes _ bs) = formatBytes bs
showVal (AbiAddress addr) = Text.pack  . show $ addr
showVal v = Text.pack . show $ v


-- prettyCalldata :: (?context :: DappContext) => Expr Buf -> Text -> [AbiType]-> IO Text
-- prettyCalldata buf sig types = do
--   cdlen' <- num <$> SBV.getValue cdlen
--   cd <- case buf of
--     ConcreteBuf cd -> return $ BS.take cdlen' cd
--     cd -> mapM (SBV.getValue . fromSized) (take cdlen' cd) <&> BS.pack
--   pure $ (head (Text.splitOn "(" sig)) <> showCall types (ConcreteBuffer cd)

execSymTest :: UnitTestOptions -> ABIMethod -> (Expr Buf, [Prop]) -> Stepper (Expr End)
execSymTest UnitTestOptions{ .. } method cd = do
  -- Set up the call to the test method
  Stepper.evm $ do
    makeTxCall testParams cd
    pushTrace (EntryTrace method)
  -- Try running the test method
  runExpr

checkSymFailures :: UnitTestOptions -> Stepper VM
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

passOutput :: VM -> UnitTestOptions -> Text -> Text
passOutput vm UnitTestOptions { .. } testName =
  let ?context = DappContext { info = dapp, env = vm.env.contracts }
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

-- TODO
failOutput :: VM -> UnitTestOptions -> Text -> Text
failOutput vm UnitTestOptions { .. } testName =
  let ?context = DappContext { info = dapp, env = vm.env.contracts}
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
formatTestLog _ (GVar _) = error "unexpected global variable"
formatTestLog events (LogEntry _ args (topic:_)) =
  case maybeLitWord topic >>= \t1 -> (Map.lookup t1 events) of
    Nothing -> Nothing
    Just (Event name _ types) ->
      case (name <> parenthesise (abiTypeSolidity <$> (unindexed types))) of
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
          ts = unindexed types
          unquote = Text.dropAround (\c -> c == '"' || c == '«' || c == '»')
          log_unnamed =
            Just $ showValue (head ts) args
          log_named =
            let (key, val) = case take 2 (textValues ts args) of
                  [k, v] -> (k, v)
                  _ -> error "shouldn't happen"
            in Just $ unquote key <> ": " <> val
          showDecimal dec val =
            pack $ show $ Decimal (num dec) val
          log_named_decimal =
            case args of
              (ConcreteBuf b) ->
                case toList $ runGet (getAbiSeq (length ts) ts) (BSLazy.fromStrict b) of
                  [key, (AbiUInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  [key, (AbiInt 256 val), (AbiUInt 256 dec)] ->
                    Just $ (unquote (showAbiValue key)) <> ": " <> showDecimal dec val
                  _ -> Nothing
              _ -> Just "<symbolic decimal>"

abiCall :: TestVMParams -> Either (Text, AbiValue) ByteString -> EVM ()
abiCall params args =
  let cd = case args of
        Left (sig, args') -> abiMethod sig args'
        Right b -> b
  in makeTxCall params (ConcreteBuf cd, [])

makeTxCall :: TestVMParams -> (Expr Buf, [Prop]) -> EVM ()
makeTxCall params (cd, cdProps) = do
  resetState
  assign (#tx % #isCreate) False
  loadContract params.address
  assign (#state % #calldata) cd
  #constraints %= (<> cdProps)
  assign (#state % #caller) (litAddr params.caller)
  assign (#state % #gas) params.gasCall
  origin' <- fromMaybe (initialContract (RuntimeCode (ConcreteRuntimeCode ""))) <$> use (#env % #contracts % at params.origin)
  let originBal = origin'.balance
  when (originBal < params.gasprice * (num params.gasCall)) $ error "insufficient balance for gas cost"
  vm <- get
  put $ initTx vm

initialUnitTestVm :: UnitTestOptions -> SolcContract -> VM
initialUnitTestVm (UnitTestOptions {..}) theContract =
  let
    vm = makeVm $ VMOpts
           { contract = initialContract (InitCode theContract.creationCode mempty)
           , calldata = mempty
           , value = Lit 0
           , address = testParams.address
           , caller = litAddr testParams.caller
           , origin = testParams.origin
           , gas = testParams.gasCreate
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
           , schedule = FeeSchedule.berlin
           , chainId = testParams.chainId
           , create = True
           , storageBase = Concrete
           , txAccessList = mempty -- TODO: support unit test access lists???
           , allowFFI = ffiAllowed
           }
    creator =
      initialContract (RuntimeCode (ConcreteRuntimeCode ""))
        & set #nonce 1
        & set #balance testParams.balanceCreate
  in vm
    & set (#env % #contracts % at ethrunAddress) (Just creator)


getParametersFromEnvironmentVariables :: Maybe Text -> IO TestVMParams
getParametersFromEnvironmentVariables rpc = do
  block' <- maybe Fetch.Latest (Fetch.BlockNumber . read) <$> (lookupEnv "DAPP_TEST_NUMBER")

  (miner,ts,blockNum,ran,limit,base) <-
    case rpc of
      Nothing  -> return (0,Lit 0,0,0,0,0)
      Just url -> Fetch.fetchBlockFrom block' url >>= \case
        Nothing -> error "Could not fetch block"
        Just EVM.Block{..} -> return (  coinbase
                                      , timestamp
                                      , number
                                      , prevRandao
                                      , gaslimit
                                      , baseFee
                                      )
  let
    getWord s def = maybe def read <$> lookupEnv s
    getAddr s def = maybe def read <$> lookupEnv s
    ts' = fromMaybe (error "Internal Error: received unexpected symbolic timestamp via rpc") (maybeLitWord ts)

  TestVMParams
    <$> getAddr "DAPP_TEST_ADDRESS" (createAddress ethrunAddress 1)
    <*> getAddr "DAPP_TEST_CALLER" ethrunAddress
    <*> getAddr "DAPP_TEST_ORIGIN" ethrunAddress
    <*> getWord "DAPP_TEST_GAS_CREATE" defaultGasForCreating
    <*> getWord "DAPP_TEST_GAS_CALL" defaultGasForInvoking
    <*> getWord "DAPP_TEST_BASEFEE" base
    <*> getWord "DAPP_TEST_PRIORITYFEE" 0
    <*> getWord "DAPP_TEST_BALANCE" defaultBalanceForTestContract
    <*> getAddr "DAPP_TEST_COINBASE" miner
    <*> getWord "DAPP_TEST_NUMBER" blockNum
    <*> getWord "DAPP_TEST_TIMESTAMP" ts'
    <*> getWord "DAPP_TEST_GAS_LIMIT" limit
    <*> getWord "DAPP_TEST_GAS_PRICE" 0
    <*> getWord "DAPP_TEST_MAXCODESIZE" defaultMaxCodeSize
    <*> getWord "DAPP_TEST_PREVRANDAO" ran
    <*> getWord "DAPP_TEST_CHAINID" 99
