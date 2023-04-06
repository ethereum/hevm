-- Main file of the hevm CLI program

{-# Language DataKinds #-}
{-# Language DeriveAnyClass #-}

module Main where

import EVM.Concrete (createAddress)
import EVM (initialContract, makeVm)
import qualified EVM.FeeSchedule as FeeSchedule
import qualified EVM.Fetch
import qualified EVM.Stepper

import EVM.SymExec
import EVM.Debug
import qualified EVM.Expr as Expr
import EVM.Solvers
import qualified EVM.TTY as TTY
import EVM.Solidity
import EVM.Expr (litAddr)
import EVM.Types hiding (word, StorageBase(..))
import qualified EVM.Types as Types
import EVM.Format (hexByteString, strip0x)
import EVM.UnitTest (UnitTestOptions, coverageReport, coverageForUnitTestContract, getParametersFromEnvironmentVariables, dappTest)
import EVM.Dapp (findUnitTests, dappInfo, DappInfo, emptyDapp)
import GHC.Natural
import EVM.Format (showTraceTree, formatExpr)
import Data.Word (Word64)

import qualified EVM.Facts     as Facts
import qualified EVM.Facts.Git as Git
import qualified EVM.UnitTest

import GHC.Conc
import Optics.Core hiding (pre)
import Control.Monad              (void, when, forM_, unless)
import Control.Monad.State.Strict (execStateT, liftIO)
import Data.ByteString            (ByteString)
import Data.List                  (intercalate, isSuffixOf, intersperse)
import Data.Text                  (unpack, pack)
import Data.Maybe                 (fromMaybe, mapMaybe)
import Data.Version               (showVersion)
import Data.DoubleWord            (Word256)
import System.IO                  (stderr)
import System.Directory           (withCurrentDirectory, listDirectory)
import System.Exit                (exitFailure, exitWith, ExitCode(..))

import qualified Data.ByteString        as ByteString
import qualified Data.ByteString.Char8  as Char8
import qualified Data.ByteString.Lazy   as LazyByteString
import qualified Data.Map               as Map
import qualified Data.Text              as T
import qualified Data.Text.IO           as T

import qualified Paths_hevm      as Paths

import Options.Generic as Options
import qualified EVM.Transaction

-- This record defines the program's command-line options
-- automatically via the `optparse-generic` package.
data Command w
  = Symbolic -- Symbolically explore an abstract program, or specialized with specified env & calldata
  -- vm opts
      { code          :: w ::: Maybe ByteString <?> "Program bytecode"
      , calldata      :: w ::: Maybe ByteString <?> "Tx: calldata"
      , address       :: w ::: Maybe Addr       <?> "Tx: address"
      , caller        :: w ::: Maybe Addr       <?> "Tx: caller"
      , origin        :: w ::: Maybe Addr       <?> "Tx: origin"
      , coinbase      :: w ::: Maybe Addr       <?> "Block: coinbase"
      , value         :: w ::: Maybe W256       <?> "Tx: Eth amount"
      , nonce         :: w ::: Maybe W256       <?> "Nonce of origin"
      , gas           :: w ::: Maybe Word64     <?> "Tx: gas amount"
      , number        :: w ::: Maybe W256       <?> "Block: number"
      , timestamp     :: w ::: Maybe W256       <?> "Block: timestamp"
      , basefee       :: w ::: Maybe W256       <?> "Block: base fee"
      , priorityFee   :: w ::: Maybe W256       <?> "Tx: priority fee"
      , gaslimit      :: w ::: Maybe Word64     <?> "Tx: gas limit"
      , gasprice      :: w ::: Maybe W256       <?> "Tx: gas price"
      , create        :: w ::: Bool             <?> "Tx: creation"
      , maxcodesize   :: w ::: Maybe W256       <?> "Block: max code size"
      , prevRandao    :: w ::: Maybe W256       <?> "Block: prevRandao"
      , chainid       :: w ::: Maybe W256       <?> "Env: chainId"
  -- remote state opts
      , rpc           :: w ::: Maybe URL        <?> "Fetch state from a remote node"
      , block         :: w ::: Maybe W256       <?> "Block state is be fetched from"
      , state         :: w ::: Maybe String     <?> "Path to state repository"
      , cache         :: w ::: Maybe String     <?> "Path to rpc cache repository"

  -- symbolic execution opts
      , jsonFile      :: w ::: Maybe String       <?> "Filename or path to dapp build output (default: out/*.solc.json)"
      , dappRoot      :: w ::: Maybe String       <?> "Path to dapp project root directory (default: . )"
      , storageModel  :: w ::: Maybe StorageModel <?> "Select storage model: ConcreteS, SymbolicS (default) or InitialS"
      , sig           :: w ::: Maybe Text         <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]           <?> "Values to encode"
      , debug         :: w ::: Bool               <?> "Run interactively"
      , getModels     :: w ::: Bool               <?> "Print example testcase for each execution path"
      , showTree      :: w ::: Bool               <?> "Print branches explored in tree view"
      , showReachableTree :: w ::: Bool           <?> "Print only reachable branches explored in tree view"
      , smttimeout    :: w ::: Maybe Natural      <?> "Timeout given to SMT solver in milliseconds (default: 60000)"
      , maxIterations :: w ::: Maybe Integer      <?> "Number of times we may revisit a particular branching point"
      , solver        :: w ::: Maybe Text         <?> "Used SMT solver: z3 (default) or cvc5"
      , smtdebug      :: w ::: Bool               <?> "Print smt queries sent to the solver"
      , assertions    :: w ::: Maybe [Word256]    <?> "Comma seperated list of solc panic codes to check for (default: everything except arithmetic overflow)"
      , askSmtIterations :: w ::: Integer         <!> "1" <?> "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability (default: 1)"
      , numSolvers    :: w ::: Maybe Natural      <?> "Number of solver instances to use (default: number of cpu cores)"
      , loopDetectionHeuristic :: w ::: LoopHeuristic <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      }
  | Equivalence -- prove equivalence between two programs
      { codeA         :: w ::: ByteString       <?> "Bytecode of the first program"
      , codeB         :: w ::: ByteString       <?> "Bytecode of the second program"
      , sig           :: w ::: Maybe Text       <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]         <?> "Values to encode"
      , calldata      :: w ::: Maybe ByteString <?> "Tx: calldata"
      , smttimeout    :: w ::: Maybe Natural    <?> "Timeout given to SMT solver in milliseconds (default: 60000)"
      , maxIterations :: w ::: Maybe Integer    <?> "Number of times we may revisit a particular branching point"
      , solver        :: w ::: Maybe Text       <?> "Used SMT solver: z3 (default) or cvc5"
      , smtoutput     :: w ::: Bool             <?> "Print verbose smt output"
      , smtdebug      :: w ::: Bool             <?> "Print smt queries sent to the solver"
      , askSmtIterations :: w ::: Integer       <!> "1" <?> "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability (default: 1)"
      , loopDetectionHeuristic :: w ::: LoopHeuristic <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      }
  | Exec -- Execute a given program with specified env & calldata
      { code        :: w ::: Maybe ByteString <?> "Program bytecode"
      , calldata    :: w ::: Maybe ByteString <?> "Tx: calldata"
      , address     :: w ::: Maybe Addr       <?> "Tx: address"
      , caller      :: w ::: Maybe Addr       <?> "Tx: caller"
      , origin      :: w ::: Maybe Addr       <?> "Tx: origin"
      , coinbase    :: w ::: Maybe Addr       <?> "Block: coinbase"
      , value       :: w ::: Maybe W256       <?> "Tx: Eth amount"
      , nonce       :: w ::: Maybe W256       <?> "Nonce of origin"
      , gas         :: w ::: Maybe Word64     <?> "Tx: gas amount"
      , number      :: w ::: Maybe W256       <?> "Block: number"
      , timestamp   :: w ::: Maybe W256       <?> "Block: timestamp"
      , basefee     :: w ::: Maybe W256       <?> "Block: base fee"
      , priorityFee :: w ::: Maybe W256       <?> "Tx: priority fee"
      , gaslimit    :: w ::: Maybe Word64     <?> "Tx: gas limit"
      , gasprice    :: w ::: Maybe W256       <?> "Tx: gas price"
      , create      :: w ::: Bool             <?> "Tx: creation"
      , maxcodesize :: w ::: Maybe W256       <?> "Block: max code size"
      , prevRandao  :: w ::: Maybe W256       <?> "Block: prevRandao"
      , chainid     :: w ::: Maybe W256       <?> "Env: chainId"
      , debug       :: w ::: Bool             <?> "Run interactively"
      , jsontrace   :: w ::: Bool             <?> "Print json trace output at every step"
      , trace       :: w ::: Bool             <?> "Dump trace"
      , state       :: w ::: Maybe String     <?> "Path to state repository"
      , cache       :: w ::: Maybe String     <?> "Path to rpc cache repository"
      , rpc         :: w ::: Maybe URL        <?> "Fetch state from a remote node"
      , block       :: w ::: Maybe W256       <?> "Block state is be fetched from"
      , jsonFile    :: w ::: Maybe String     <?> "Filename or path to dapp build output (default: out/*.solc.json)"
      , dappRoot    :: w ::: Maybe String     <?> "Path to dapp project root directory (default: . )"
      }
  | DappTest -- Run DSTest unit tests
      { jsonFile      :: w ::: Maybe String             <?> "Filename or path to dapp build output (default: out/*.solc.json)"
      , dappRoot      :: w ::: Maybe String             <?> "Path to dapp project root directory (default: . )"
      , debug         :: w ::: Bool                     <?> "Run interactively"
      , jsontrace     :: w ::: Bool                     <?> "Print json trace output at every step"
      , fuzzRuns      :: w ::: Maybe Int                <?> "Number of times to run fuzz tests"
      , depth         :: w ::: Maybe Int                <?> "Number of transactions to explore"
      , replay        :: w ::: Maybe (Text, ByteString) <?> "Custom fuzz case to run/debug"
      , rpc           :: w ::: Maybe URL                <?> "Fetch state from a remote node"
      , verbose       :: w ::: Maybe Int                <?> "Append call trace: {1} failures {2} all"
      , coverage      :: w ::: Bool                     <?> "Coverage analysis"
      , state         :: w ::: Maybe String             <?> "Path to state repository"
      , cache         :: w ::: Maybe String             <?> "Path to rpc cache repository"
      , match         :: w ::: Maybe String             <?> "Test case filter - only run methods matching regex"
      , covMatch      :: w ::: Maybe String             <?> "Coverage filter - only print coverage for files matching regex"
      , solver        :: w ::: Maybe Text               <?> "Used SMT solver: z3 (default) or cvc5"
      , smtdebug      :: w ::: Bool                     <?> "Print smt queries sent to the solver"
      , ffi           :: w ::: Bool                     <?> "Allow the usage of the hevm.ffi() cheatcode (WARNING: this allows test authors to execute arbitrary code on your machine)"
      , smttimeout    :: w ::: Maybe Natural            <?> "Timeout given to SMT solver in milliseconds (default: 60000)"
      , maxIterations :: w ::: Maybe Integer            <?> "Number of times we may revisit a particular branching point"
      , loopDetectionHeuristic :: w ::: LoopHeuristic   <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      , askSmtIterations :: w ::: Integer               <!> "1" <?> "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability (default: 1)"
      }
  | Version

  deriving (Options.Generic)

type URL = Text


-- For some reason haskell can't derive a
-- parseField instance for (Text, ByteString)
instance Options.ParseField (Text, ByteString)

deriving instance Options.ParseField Word256
deriving instance Options.ParseField [Word256]

instance Options.ParseRecord (Command Options.Wrapped) where
  parseRecord =
    Options.parseRecordWithModifiers Options.lispCaseModifiers

optsMode :: Command Options.Unwrapped -> Mode
optsMode x
  | x.debug = Debug
  | x.jsontrace = JsonTrace
  | otherwise = Run

applyCache :: (Maybe String, Maybe String) -> IO (VM -> VM)
applyCache (state, cache) =
  let applyState = flip Facts.apply
      applyCache' = flip Facts.applyCache
  in case (state, cache) of
    (Nothing, Nothing) -> do
      pure id
    (Nothing, Just cachePath) -> do
      facts <- Git.loadFacts (Git.RepoAt cachePath)
      pure $ applyCache' facts
    (Just statePath, Nothing) -> do
      facts <- Git.loadFacts (Git.RepoAt statePath)
      pure $ applyState facts
    (Just statePath, Just cachePath) -> do
      cacheFacts <- Git.loadFacts (Git.RepoAt cachePath)
      stateFacts <- Git.loadFacts (Git.RepoAt statePath)
      pure $ (applyState stateFacts) . (applyCache' cacheFacts)

unitTestOptions :: Command Options.Unwrapped -> SolverGroup -> String -> IO UnitTestOptions
unitTestOptions cmd solvers testFile = do
  let root = fromMaybe "." cmd.dappRoot
  srcInfo <- readSolc testFile >>= \case
    Nothing -> error "Could not read .sol.json file"
    Just (contractMap, sourceCache) ->
      pure $ dappInfo root contractMap sourceCache

  vmModifier <- applyCache (cmd.state, cmd.cache)

  params <- getParametersFromEnvironmentVariables cmd.rpc

  let
    testn = params.number
    block' = if 0 == testn
       then EVM.Fetch.Latest
       else EVM.Fetch.BlockNumber testn

  pure EVM.UnitTest.UnitTestOptions
    { solvers = solvers
    , rpcInfo = case cmd.rpc of
         Just url -> Just (block', url)
         Nothing  -> Nothing
    , maxIter = cmd.maxIterations
    , askSmtIters = cmd.askSmtIterations
    , smtDebug = cmd.smtdebug
    , smtTimeout = cmd.smttimeout
    , solver = cmd.solver
    , covMatch = pack <$> cmd.covMatch
    , verbose = cmd.verbose
    , match = pack $ fromMaybe ".*" cmd.match
    , maxDepth = cmd.depth
    , fuzzRuns = fromMaybe 100 cmd.fuzzRuns
    , replay = do
        arg' <- cmd.replay
        return (fst arg', LazyByteString.fromStrict (hexByteString "--replay" $ strip0x $ snd arg'))
    , vmModifier = vmModifier
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = cmd.ffi
    }

main :: IO ()
main = do
  cmd <- Options.unwrapRecord "hevm -- Ethereum evaluator"
  let
    root = fromMaybe "." cmd.dappRoot
  case cmd of
    Version {} -> putStrLn (showVersion Paths.version)
    Symbolic {} -> withCurrentDirectory root $ assert cmd
    Equivalence {} -> equivalence cmd
    Exec {} ->
      launchExec cmd
    DappTest {} ->
      withCurrentDirectory root $ do
        cores <- num <$> getNumProcessors
        solver <- getSolver cmd
        withSolvers solver cores cmd.smttimeout $ \solvers -> do
          testFile <- findJsonFile cmd.jsonFile
          testOpts <- unitTestOptions cmd solvers testFile
          case (cmd.coverage, optsMode cmd) of
            (False, Run) -> do
              res <- dappTest testOpts testFile cmd.cache
              unless res exitFailure
            (False, Debug) -> liftIO $ TTY.main testOpts root testFile
            (False, JsonTrace) -> error "json traces not implemented for dappTest"
            (True, _) -> liftIO $ dappCoverage testOpts (optsMode cmd) testFile

findJsonFile :: Maybe String -> IO String
findJsonFile (Just s) = pure s
findJsonFile Nothing = do
  outFiles <- listDirectory "out"
  case filter (isSuffixOf ".sol.json") outFiles of
    [x] -> pure ("out/" ++ x)
    [] ->
      error $ concat
        [ "No `*.sol.json' file found in `./out'.\n"
        , "Maybe you need to run `dapp build'.\n"
        , "You can specify a file with `--json-file'."
        ]
    xs ->
      error $ concat
        [ "Multiple `*.sol.json' files found in `./out'.\n"
        , "Specify one using `--json-file'.\n"
        , "Files found: "
        , intercalate ", " xs
        ]

equivalence :: Command Options.Unwrapped -> IO ()
equivalence cmd = do
  let bytecodeA = hexByteString "--code" . strip0x $ cmd.codeA
      bytecodeB = hexByteString "--code" . strip0x $ cmd.codeB
      veriOpts = VeriOpts { simp = True
                          , debug = False
                          , maxIter = cmd.maxIterations
                          , askSmtIters = cmd.askSmtIterations
                          , loopHeuristic = cmd.loopDetectionHeuristic
                          , rpcInfo = Nothing
                          }
  calldata <- buildCalldata cmd
  solver <- getSolver cmd
  withSolvers solver 3 Nothing $ \s -> do
    res <- equivalenceCheck s bytecodeA bytecodeB veriOpts calldata
    case any isCex res of
      False -> do
        putStrLn "No discrepancies found"
        when (any isTimeout res) $ do
          putStrLn "But timeout(s) occurred"
          exitFailure
      True -> do
        let cexs = mapMaybe getCex res
        T.putStrLn . T.unlines $
          [ "Not equivalent. The following inputs result in differing behaviours:"
          , "" , "-----", ""
          ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (formatCex (AbstractBuf "txdata")) cexs)
        exitFailure

getSolver :: Command Options.Unwrapped -> IO Solver
getSolver cmd = case cmd.solver of
                  Nothing -> pure Z3
                  Just s -> case T.unpack s of
                              "z3" -> pure Z3
                              "cvc5" -> pure CVC5
                              input -> do
                                putStrLn $ "unrecognised solver: " <> input
                                exitFailure

getSrcInfo :: Command Options.Unwrapped -> IO DappInfo
getSrcInfo cmd =
  let root = fromMaybe "." cmd.dappRoot
  in case cmd.jsonFile of
    Nothing ->
      pure emptyDapp
    Just json -> readSolc json >>= \case
      Nothing ->
        pure emptyDapp
      Just (contractMap, sourceCache) ->
        pure $ dappInfo root contractMap sourceCache


-- | Builds a buffer representing calldata based on the given cli arguments
buildCalldata :: Command Options.Unwrapped -> IO (Expr Buf, [Prop])
buildCalldata cmd = case (cmd.calldata, cmd.sig) of
  -- fully abstract calldata
  (Nothing, Nothing) -> pure $ mkCalldata Nothing []
  -- fully concrete calldata
  (Just c, Nothing) -> pure (ConcreteBuf (hexByteString "bytes" . strip0x $ c), [])
  -- calldata according to given abi with possible specializations from the `arg` list
  (Nothing, Just sig') -> do
    method' <- functionAbi sig'
    pure $ mkCalldata (Just (Sig method'.methodSignature (snd <$> method'.inputs))) cmd.arg
  -- both args provided
  (_, _) -> do
    putStrLn "incompatible options provided: --calldata and --sig"
    exitFailure


-- If function signatures are known, they should always be given for best results.
assert :: Command Options.Unwrapped -> IO ()
assert cmd = do
  let block'  = maybe EVM.Fetch.Latest EVM.Fetch.BlockNumber cmd.block
      rpcinfo = (,) block' <$> cmd.rpc
  calldata <- buildCalldata cmd
  preState <- symvmFromCommand cmd calldata
  let errCodes = fromMaybe defaultPanicCodes cmd.assertions
  cores <- num <$> getNumProcessors
  let solverCount = fromMaybe cores cmd.numSolvers
  solver <- getSolver cmd
  withSolvers solver solverCount cmd.smttimeout $ \solvers -> do
    if cmd.debug then do
      srcInfo <- getSrcInfo cmd
      void $ TTY.runFromVM
        solvers
        rpcinfo
        cmd.maxIterations
        srcInfo
        preState
    else do
      let opts = VeriOpts {
        simp = True,
        debug = cmd.smtdebug,
        maxIter = cmd.maxIterations,
        askSmtIters = cmd.askSmtIterations,
        loopHeuristic = cmd.loopDetectionHeuristic,
        rpcInfo = rpcinfo
      }
      (expr, res) <- verify solvers opts preState (Just $ checkAssertions errCodes)
      case res of
        [Qed _] -> do
          putStrLn "\nQED: No reachable property violations discovered\n"
          showExtras solvers cmd calldata expr
        _ -> do
          let cexs = snd <$> mapMaybe getCex res
              timeouts = mapMaybe getTimeout res
              counterexamples
                | null cexs = []
                | otherwise =
                   [ ""
                   , "Discovered the following counterexamples:"
                   , ""
                   ] <> fmap (formatCex (fst calldata)) cexs
              unknowns
                | null timeouts = []
                | otherwise =
                   [ ""
                   , "Could not determine reachability of the following end states:"
                   , ""
                   ] <> fmap (formatExpr) timeouts
          T.putStrLn $ T.unlines (counterexamples <> unknowns)
          showExtras solvers cmd calldata expr
          exitFailure

showExtras :: SolverGroup -> Command Options.Unwrapped -> (Expr Buf, [Prop]) -> Expr End -> IO ()
showExtras solvers cmd calldata expr = do
  when cmd.showTree $ do
    putStrLn "=== Expression ===\n"
    T.putStrLn $ formatExpr expr
    putStrLn ""
  when cmd.showReachableTree $ do
    reached <- reachable solvers expr
    putStrLn "=== Reachable Expression ===\n"
    T.putStrLn (formatExpr . snd $ reached)
    putStrLn ""
  when cmd.getModels $ do
    putStrLn $ "=== Models for " <> show (Expr.numBranches expr) <> " branches ===\n"
    ms <- produceModels solvers expr
    forM_ ms (showModel (fst calldata))

getCex :: ProofResult a b c -> Maybe b
getCex (Cex c) = Just c
getCex _ = Nothing

getTimeout :: ProofResult a b c -> Maybe c
getTimeout (Timeout c) = Just c
getTimeout _ = Nothing

dappCoverage :: UnitTestOptions -> Mode -> String -> IO ()
dappCoverage opts _ solcFile =
  readSolc solcFile >>=
    \case
      Just (contractMap, sourceCache) -> do
        let unitTests = findUnitTests opts.match $ Map.elems contractMap
        covs <- mconcat <$> mapM
          (coverageForUnitTestContract opts contractMap sourceCache) unitTests
        let
          dapp = dappInfo "." contractMap sourceCache
          f (k, vs) = do
            when (shouldPrintCoverage opts.covMatch k) $ do
              putStr ("\x1b[0m" ++ "————— hevm coverage for ") -- Prefixed with color reset
              putStrLn (unpack k ++ " —————")
              putStrLn ""
              forM_ vs $ \(n, bs) -> do
                case ByteString.find (\x -> x /= 0x9 && x /= 0x20 && x /= 0x7d) bs of
                  Nothing -> putStr "\x1b[38;5;240m" -- Gray (Coverage status isn't relevant)
                  Just _ ->
                    case n of
                      -1 -> putStr "\x1b[38;5;240m" -- Gray (Coverage status isn't relevant)
                      0  -> putStr "\x1b[31m" -- Red (Uncovered)
                      _  -> putStr "\x1b[32m" -- Green (Covered)
                Char8.putStrLn bs
              putStrLn ""
        mapM_ f (Map.toList (coverageReport dapp covs))
      Nothing ->
        error ("Failed to read Solidity JSON for `" ++ solcFile ++ "'")

shouldPrintCoverage :: Maybe Text -> Text -> Bool
shouldPrintCoverage (Just covMatch) file = regexMatches covMatch file
shouldPrintCoverage Nothing file = not (isTestOrLib file)

isTestOrLib :: Text -> Bool
isTestOrLib file = T.isSuffixOf ".t.sol" file || areAnyPrefixOf ["src/test/", "src/tests/", "lib/"] file

areAnyPrefixOf :: [Text] -> Text -> Bool
areAnyPrefixOf prefixes t = any (flip T.isPrefixOf t) prefixes

launchExec :: Command Options.Unwrapped -> IO ()
launchExec cmd = do
  dapp <- getSrcInfo cmd
  vm <- vmFromCommand cmd
  -- TODO: we shouldn't need solvers to execute this code
  withSolvers Z3 0 Nothing $ \solvers -> do
    case optsMode cmd of
      Run -> do
        vm' <- execStateT (EVM.Stepper.interpret (EVM.Fetch.oracle solvers rpcinfo) . void $ EVM.Stepper.execFully) vm
        when cmd.trace $ T.hPutStr stderr (showTraceTree dapp vm')
        case vm'.result of
          Just (VMFailure (Revert msg)) -> do
            let res = case msg of
                        ConcreteBuf bs -> bs
                        _ -> "<symbolic>"
            putStrLn $ "Revert: " <> (show $ ByteStringS res)
            exitWith (ExitFailure 2)
          Just (VMFailure err) -> do
            putStrLn $ "Error: " <> show err
            exitWith (ExitFailure 2)
          Just (Unfinished p) -> do
            putStrLn $ "Could not continue execution: " <> show p
            exitWith (ExitFailure 2)
          Just (VMSuccess buf) -> do
            let msg = case buf of
                  ConcreteBuf msg' -> msg'
                  _ -> "<symbolic>"
            print $ "Return: " <> (show $ ByteStringS msg)
            case cmd.state of
              Nothing -> pure ()
              Just path ->
                Git.saveFacts (Git.RepoAt path) (Facts.vmFacts vm')
            case cmd.cache of
              Nothing -> pure ()
              Just path ->
                Git.saveFacts (Git.RepoAt path) (Facts.cacheFacts vm'.cache)
          _ ->
            error "Internal error: no EVM result"

      Debug -> void $ TTY.runFromVM solvers rpcinfo Nothing dapp vm
      --JsonTrace -> void $ execStateT (interpretWithTrace fetcher EVM.Stepper.runFully) vm
      _ -> error "TODO"
     where block = maybe EVM.Fetch.Latest EVM.Fetch.BlockNumber cmd.block
           rpcinfo = (,) block <$> cmd.rpc

-- | Creates a (concrete) VM from command line options
vmFromCommand :: Command Options.Unwrapped -> IO VM
vmFromCommand cmd = do
  withCache <- applyCache (cmd.state, cmd.cache)

  (miner,ts,baseFee,blockNum,prevRan) <- case cmd.rpc of
    Nothing -> return (0,Lit 0,0,0,0)
    Just url -> EVM.Fetch.fetchBlockFrom block url >>= \case
      Nothing -> error "Could not fetch block"
      Just Block{..} -> return ( coinbase
                                   , timestamp
                                   , baseFee
                                   , number
                                   , prevRandao
                                   )

  contract <- case (cmd.rpc, cmd.address, cmd.code) of
    (Just url, Just addr', Just c) -> do
      EVM.Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error $ "contract not found: " <> show address
        Just contract ->
          -- if both code and url is given,
          -- fetch the contract and overwrite the code
          return $
            initialContract  (mkCode $ hexByteString "--code" $ strip0x c)
              & set #balance  (contract.balance)
              & set #nonce    (contract.nonce)
              & set #external (contract.external)

    (Just url, Just addr', Nothing) ->
      EVM.Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error $ "contract not found: " <> show address
        Just contract -> return contract

    (_, _, Just c)  ->
      return $
        initialContract (mkCode $ hexByteString "--code" $ strip0x c)

    (_, _, Nothing) ->
      error "must provide at least (rpc + address) or code"

  let ts' = case maybeLitWord ts of
        Just t -> t
        Nothing -> error "unexpected symbolic timestamp when executing vm test"

  return $ EVM.Transaction.initTx $ withCache (vm0 baseFee miner ts' blockNum prevRan contract)
    where
        block   = maybe EVM.Fetch.Latest EVM.Fetch.BlockNumber cmd.block
        value   = word (.value) 0
        caller  = addr (.caller) 0
        origin  = addr (.origin) 0
        calldata = ConcreteBuf $ bytes (.calldata) ""
        decipher = hexByteString "bytes" . strip0x
        mkCode bs = if cmd.create
                    then InitCode bs mempty
                    else RuntimeCode (ConcreteRuntimeCode bs)
        address = if cmd.create
              then addr (.address) (createAddress origin (word (.nonce) 0))
              else addr (.address) 0xacab

        vm0 baseFee miner ts blockNum prevRan c = makeVm $ VMOpts
          { contract      = c
          , calldata      = (calldata, [])
          , value         = Lit value
          , address       = address
          , caller        = litAddr caller
          , origin        = origin
          , gas           = word64 (.gas) 0xffffffffffffffff
          , baseFee       = baseFee
          , priorityFee   = word (.priorityFee) 0
          , gaslimit      = word64 (.gaslimit) 0xffffffffffffffff
          , coinbase      = addr (.coinbase) miner
          , number        = word (.number) blockNum
          , timestamp     = Lit $ word (.timestamp) ts
          , blockGaslimit = word64 (.gaslimit) 0xffffffffffffffff
          , gasprice      = word (.gasprice) 0
          , maxCodeSize   = word (.maxcodesize) 0xffffffff
          , prevRandao    = word (.prevRandao) prevRan
          , schedule      = FeeSchedule.berlin
          , chainId       = word (.chainid) 1
          , create        = (.create) cmd
          , storageBase   = Types.Concrete
          , txAccessList  = mempty -- TODO: support me soon
          , allowFFI      = False
          }
        word f def = fromMaybe def (f cmd)
        word64 f def = fromMaybe def (f cmd)
        addr f def = fromMaybe def (f cmd)
        bytes f def = maybe def decipher (f cmd)

symvmFromCommand :: Command Options.Unwrapped -> (Expr Buf, [Prop]) -> IO (VM)
symvmFromCommand cmd calldata = do
  (miner,blockNum,baseFee,prevRan) <- case cmd.rpc of
    Nothing -> return (0,0,0,0)
    Just url -> EVM.Fetch.fetchBlockFrom block url >>= \case
      Nothing -> error "Could not fetch block"
      Just Block{..} -> return ( coinbase
                                   , number
                                   , baseFee
                                   , prevRandao
                                   )

  let
    caller = Caller 0
    ts = maybe Timestamp Lit cmd.timestamp
    callvalue = maybe (CallValue 0) Lit cmd.value
  -- TODO: rework this, ConcreteS not needed anymore
  let store = case cmd.storageModel of
                -- InitialS and SymbolicS can read and write to symbolic locations
                -- ConcreteS cannot (instead values can be fetched from rpc!)
                -- Initial defaults to 0 for uninitialized storage slots,
                -- whereas the values of SymbolicS are unconstrained.
                Just InitialS  -> EmptyStore
                Just ConcreteS -> ConcreteStore mempty
                Just SymbolicS -> AbstractStore
                Nothing -> if cmd.create then EmptyStore else AbstractStore

  withCache <- applyCache (cmd.state, cmd.cache)

  contract <- case (cmd.rpc, cmd.address, cmd.code) of
    (Just url, Just addr', _) ->
      EVM.Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error "contract not found."
        Just contract' -> return contract''
          where
            contract'' = case cmd.code of
              Nothing -> contract'
              -- if both code and url is given,
              -- fetch the contract and overwrite the code
              Just c -> initialContract (mkCode $ decipher c)
                        -- TODO: fix this
                        -- & set EVM.origStorage (view EVM.origStorage contract')
                        & set #balance     (contract'.balance)
                        & set #nonce       (contract'.nonce)
                        & set #external    (contract'.external)

    (_, _, Just c)  ->
      return (initialContract . mkCode $ decipher c)
    (_, _, Nothing) ->
      error "must provide at least (rpc + address) or code"

  return $ (EVM.Transaction.initTx $ withCache $ vm0 baseFee miner ts blockNum prevRan calldata callvalue caller contract)
    & set (#env % #storage) store

  where
    decipher = hexByteString "bytes" . strip0x
    block   = maybe EVM.Fetch.Latest EVM.Fetch.BlockNumber cmd.block
    origin  = addr (.origin) 0
    mkCode bs = if cmd.create
                   then InitCode bs mempty
                   else RuntimeCode (ConcreteRuntimeCode bs)
    address = if cmd.create
          then addr (.address) (createAddress origin (word (.nonce) 0))
          else addr (.address) 0xacab
    vm0 baseFee miner ts blockNum prevRan cd callvalue caller c = makeVm $ VMOpts
      { contract      = c
      , calldata      = cd
      , value         = callvalue
      , address       = address
      , caller        = caller
      , origin        = origin
      , gas           = word64 (.gas) 0xffffffffffffffff
      , gaslimit      = word64 (.gaslimit) 0xffffffffffffffff
      , baseFee       = baseFee
      , priorityFee   = word (.priorityFee) 0
      , coinbase      = addr (.coinbase) miner
      , number        = word (.number) blockNum
      , timestamp     = ts
      , blockGaslimit = word64 (.gaslimit) 0xffffffffffffffff
      , gasprice      = word (.gasprice) 0
      , maxCodeSize   = word (.maxcodesize) 0xffffffff
      , prevRandao    = word (.prevRandao) prevRan
      , schedule      = FeeSchedule.berlin
      , chainId       = word (.chainid) 1
      , create        = (.create) cmd
      , storageBase   = Types.Symbolic
      , txAccessList  = mempty
      , allowFFI      = False
      }
    word f def = fromMaybe def (f cmd)
    addr f def = fromMaybe def (f cmd)
    word64 f def = fromMaybe def (f cmd)
