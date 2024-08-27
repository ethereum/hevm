-- Main file of the hevm CLI program

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE TemplateHaskell #-}

module Main where

import Control.Monad (when, forM_, unless)
import Control.Monad.ST (RealWorld, stToIO)
import Control.Monad.IO.Unlift
import Data.ByteString (ByteString)
import Data.DoubleWord (Word256)
import Data.List (intersperse)
import Data.Maybe (fromMaybe, mapMaybe, fromJust)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Version (showVersion)
import Data.Word (Word64)
import GHC.Conc (getNumProcessors)
import Numeric.Natural (Natural)
import Optics.Core ((&), set)
import Witch (unsafeInto)
import Options.Generic as Options
import Paths_hevm qualified as Paths
import System.Directory (withCurrentDirectory, getCurrentDirectory, doesDirectoryExist, makeAbsolute)
import System.FilePath ((</>))
import System.Exit (exitFailure, exitWith, ExitCode(..))
import Main.Utf8 (withUtf8)

import EVM (initialContract, abstractContract, makeVm)
import EVM.ABI (Sig(..))
import EVM.Dapp (dappInfo, DappInfo, emptyDapp)
import EVM.Expr qualified as Expr
import EVM.Concrete qualified as Concrete
import GitHash
import EVM.FeeSchedule (feeSchedule)
import EVM.Fetch qualified as Fetch
import EVM.Format (hexByteString, strip0x, formatExpr)
import EVM.Solidity
import EVM.Solvers
import EVM.Stepper qualified
import EVM.SymExec
import EVM.Transaction qualified
import EVM.Types hiding (word, Env, Symbolic)
import EVM.Types qualified
import EVM.UnitTest
import EVM.Effects

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
      , nonce         :: w ::: Maybe Word64     <?> "Nonce of origin"
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

  -- symbolic execution opts
      , root          :: w ::: Maybe String       <?> "Path to  project root directory (default: . )"
      , projectType   :: w ::: Maybe ProjectType  <?> "Is this a Foundry or DappTools project (default: Foundry)"
      , initialStorage :: w ::: Maybe (InitialStorage) <?> "Starting state for storage: Empty, Abstract (default Abstract)"
      , sig           :: w ::: Maybe Text         <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]           <?> "Values to encode"
      , getModels     :: w ::: Bool               <?> "Print example testcase for each execution path"
      , showTree      :: w ::: Bool               <?> "Print branches explored in tree view"
      , showReachableTree :: w ::: Bool           <?> "Print only reachable branches explored in tree view"
      , smttimeout    :: w ::: Maybe Natural      <?> "Timeout given to SMT solver in seconds (default: 300)"
      , maxIterations :: w ::: Maybe Integer      <?> "Number of times we may revisit a particular branching point"
      , solver        :: w ::: Maybe Text         <?> "Used SMT solver: z3 (default), cvc5, or bitwuzla"
      , smtdebug      :: w ::: Bool               <?> "Print smt queries sent to the solver"
      , debug         :: w ::: Bool               <?> "Debug printing of internal behaviour, and dump internal expressions"
      , trace         :: w ::: Bool               <?> "Dump trace"
      , assertions    :: w ::: Maybe [Word256]    <?> "Comma separated list of solc panic codes to check for (default: user defined assertion violations only)"
      , askSmtIterations :: w ::: Integer         <!> "1" <?> "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability (default: 1)"
      , numCexFuzz    :: w ::: Integer            <!> "3" <?> "Number of fuzzing tries to do to generate a counterexample (default: 3)"
      , numSolvers    :: w ::: Maybe Natural      <?> "Number of solver instances to use (default: number of cpu cores)"
      , loopDetectionHeuristic :: w ::: LoopHeuristic <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      , abstractArithmetic    :: w ::: Bool             <?> "Use abstraction-refinement for complicated arithmetic functions such as MulMod. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , abstractMemory    :: w ::: Bool                      <?> "Use abstraction-refinement for Memory. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , noDecompose   :: w ::: Bool               <?> "Don't decompose storage slots into separate arrays"
      }
  | Equivalence -- prove equivalence between two programs
      { codeA         :: w ::: ByteString       <?> "Bytecode of the first program"
      , codeB         :: w ::: ByteString       <?> "Bytecode of the second program"
      , sig           :: w ::: Maybe Text       <?> "Signature of types to decode / encode"
      , arg           :: w ::: [String]         <?> "Values to encode"
      , calldata      :: w ::: Maybe ByteString <?> "Tx: calldata"
      , smttimeout    :: w ::: Maybe Natural    <?> "Timeout given to SMT solver in seconds (default: 300)"
      , maxIterations :: w ::: Maybe Integer    <?> "Number of times we may revisit a particular branching point"
      , solver        :: w ::: Maybe Text       <?> "Used SMT solver: z3 (default), cvc5, or bitwuzla"
      , smtoutput     :: w ::: Bool             <?> "Print verbose smt output"
      , smtdebug      :: w ::: Bool             <?> "Print smt queries sent to the solver"
      , debug         :: w ::: Bool             <?> "Debug printing of internal behaviour, and dump internal expressions"
      , trace         :: w ::: Bool             <?> "Dump trace"
      , askSmtIterations :: w ::: Integer       <!> "1" <?> "Number of times we may revisit a particular branching point before we consult the smt solver to check reachability (default: 1)"
      , numCexFuzz    :: w ::: Integer          <!> "3" <?> "Number of fuzzing tries to do to generate a counterexample (default: 3)"
      , loopDetectionHeuristic :: w ::: LoopHeuristic <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      , abstractArithmetic    :: w ::: Bool             <?> "Use abstraction-refinement for complicated arithmetic functions such as MulMod. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , abstractMemory    :: w ::: Bool                      <?> "Use abstraction-refinement for Memory. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , noDecompose   :: w ::: Bool             <?> "Don't decompose storage slots into separate arrays"
      }
  | Exec -- Execute a given program with specified env & calldata
      { code        :: w ::: Maybe ByteString  <?> "Program bytecode"
      , calldata    :: w ::: Maybe ByteString  <?> "Tx: calldata"
      , address     :: w ::: Maybe Addr        <?> "Tx: address"
      , caller      :: w ::: Maybe Addr        <?> "Tx: caller"
      , origin      :: w ::: Maybe Addr        <?> "Tx: origin"
      , coinbase    :: w ::: Maybe Addr        <?> "Block: coinbase"
      , value       :: w ::: Maybe W256        <?> "Tx: Eth amount"
      , nonce       :: w ::: Maybe Word64      <?> "Nonce of origin"
      , gas         :: w ::: Maybe Word64      <?> "Tx: gas amount"
      , number      :: w ::: Maybe W256        <?> "Block: number"
      , timestamp   :: w ::: Maybe W256        <?> "Block: timestamp"
      , basefee     :: w ::: Maybe W256        <?> "Block: base fee"
      , priorityFee :: w ::: Maybe W256        <?> "Tx: priority fee"
      , gaslimit    :: w ::: Maybe Word64      <?> "Tx: gas limit"
      , gasprice    :: w ::: Maybe W256        <?> "Tx: gas price"
      , create      :: w ::: Bool              <?> "Tx: creation"
      , maxcodesize :: w ::: Maybe W256        <?> "Block: max code size"
      , prevRandao  :: w ::: Maybe W256        <?> "Block: prevRandao"
      , chainid     :: w ::: Maybe W256        <?> "Env: chainId"
      , debug         :: w ::: Bool            <?> "Debug printing of internal behaviour, and dump internal expressions"
      , trace       :: w ::: Bool              <?> "Dump trace"
      , rpc         :: w ::: Maybe URL         <?> "Fetch state from a remote node"
      , block       :: w ::: Maybe W256        <?> "Block state is be fetched from"
      , root        :: w ::: Maybe String      <?> "Path to  project root directory (default: . )"
      , projectType :: w ::: Maybe ProjectType <?> "Is this a Foundry or DappTools project (default: Foundry)"
      }
  | Test -- Run DSTest unit tests
      { root        :: w ::: Maybe String               <?> "Path to  project root directory (default: . )"
      , projectType   :: w ::: Maybe ProjectType        <?> "Is this a Foundry or DappTools project (default: Foundry)"
      , rpc           :: w ::: Maybe URL                <?> "Fetch state from a remote node"
      , number        :: w ::: Maybe W256               <?> "Block: number"
      , verbose       :: w ::: Maybe Int                <?> "Append call trace: {1} failures {2} all"
      , coverage      :: w ::: Bool                     <?> "Coverage analysis"
      , match         :: w ::: Maybe String             <?> "Test case filter - only run methods matching regex"
      , solver        :: w ::: Maybe Text               <?> "Used SMT solver: z3 (default), cvc5, or bitwuzla"
      , numSolvers    :: w ::: Maybe Natural            <?> "Number of solver instances to use (default: number of cpu cores)"
      , smtdebug      :: w ::: Bool                     <?> "Print smt queries sent to the solver"
      , debug         :: w ::: Bool                     <?> "Debug printing of internal behaviour, and dump internal expressions"
      , trace         :: w ::: Bool                     <?> "Dump trace"
      , ffi           :: w ::: Bool                     <?> "Allow the usage of the hevm.ffi() cheatcode (WARNING: this allows test authors to execute arbitrary code on your machine)"
      , smttimeout    :: w ::: Maybe Natural            <?> "Timeout given to SMT solver in seconds (default: 300)"
      , maxIterations :: w ::: Maybe Integer            <?> "Number of times we may revisit a particular branching point"
      , loopDetectionHeuristic :: w ::: LoopHeuristic   <!> "StackBased" <?> "Which heuristic should be used to determine if we are in a loop: StackBased (default) or Naive"
      , abstractArithmetic    :: w ::: Bool             <?> "Use abstraction-refinement for complicated arithmetic functions such as MulMod. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , abstractMemory    :: w ::: Bool                      <?> "Use abstraction-refinement for Memory. This runs the solver first with abstraction turned on, and if it returns a potential counterexample, the counterexample is refined to make sure it is a counterexample for the actual (not the abstracted) problem"
      , noDecompose   :: w ::: Bool                     <?> "Don't decompose storage slots into separate arrays"
      , numCexFuzz    :: w ::: Integer                  <!> "3" <?> "Number of fuzzing tries to do to generate a counterexample (default: 3)"
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

data InitialStorage
  = Empty
  | Abstract
  deriving (Show, Read, Options.ParseField)

getFullVersion :: [Char]
getFullVersion = showVersion Paths.version <> " [" <> gitVersion <> "]"
  where
    gitInfo = $$tGitInfoCwdTry
    gitVersion = case gitInfo of
      Right val -> "git rev " <> giBranch val <>  "@" <> giHash val
      Left _ -> "no git revision present"

main :: IO ()
main = withUtf8 $ do
  cmd <- Options.unwrapRecord "hevm -- Ethereum evaluator"
  let env = Env { config = defaultConfig
    { dumpQueries = cmd.smtdebug
    , debug = cmd.debug
    , dumpExprs = cmd.debug
    , numCexFuzz = cmd.numCexFuzz
    , abstRefineMem = cmd.abstractMemory
    , abstRefineArith = cmd.abstractArithmetic
    , dumpTrace = cmd.trace
    , decomposeStorage = Prelude.not cmd.noDecompose
    } }
  case cmd of
    Version {} ->putStrLn getFullVersion
    Symbolic {} -> do
      root <- getRoot cmd
      withCurrentDirectory root $ runEnv env $ assert cmd
    Equivalence {} -> runEnv env $ equivalence cmd
    Exec {} -> runEnv env $ launchExec cmd
    Test {} -> do
      root <- getRoot cmd
      solver <- getSolver cmd
      cores <- liftIO $ unsafeInto <$> getNumProcessors
      let solverCount = fromMaybe cores cmd.numSolvers
      runEnv env $ withSolvers solver solverCount cmd.smttimeout $ \solvers -> do
        buildOut <- readBuildOutput root (getProjectType cmd)
        case buildOut of
          Left e -> liftIO $ do
            putStrLn $ "Error: " <> e
            exitFailure
          Right out -> do
            -- TODO: which functions here actually require a BuildOutput, and which can take it as a Maybe?
            testOpts <- liftIO $ unitTestOptions cmd solvers (Just out)
            res <- unitTest testOpts out.contracts
            liftIO $ unless res exitFailure

equivalence :: App m => Command Options.Unwrapped -> m ()
equivalence cmd = do
  let bytecodeA = hexByteString "--code" . strip0x $ cmd.codeA
      bytecodeB = hexByteString "--code" . strip0x $ cmd.codeB
      veriOpts = VeriOpts { simp = True
                          , maxIter = cmd.maxIterations
                          , askSmtIters = cmd.askSmtIterations
                          , loopHeuristic = cmd.loopDetectionHeuristic
                          , rpcInfo = Nothing
                          }
  calldata <- liftIO $ buildCalldata cmd
  solver <- liftIO $ getSolver cmd
  withSolvers solver 3 Nothing $ \s -> do
    res <- equivalenceCheck s bytecodeA bytecodeB veriOpts calldata
    case any isCex res of
      False -> liftIO $ do
        putStrLn "No discrepancies found"
        when (any isTimeout res) $ do
          putStrLn "But timeout(s) occurred"
          exitFailure
      True -> liftIO $ do
        let cexs = mapMaybe getCex res
        T.putStrLn . T.unlines $
          [ "Not equivalent. The following inputs result in differing behaviours:"
          , "" , "-----", ""
          ] <> (intersperse (T.unlines [ "", "-----" ]) $ fmap (formatCex (AbstractBuf "txdata") Nothing) cexs)
        exitFailure

getSolver :: Command Options.Unwrapped -> IO Solver
getSolver cmd = case cmd.solver of
                  Nothing -> pure Z3
                  Just s -> case T.unpack s of
                              "z3" -> pure Z3
                              "cvc5" -> pure CVC5
                              "bitwuzla" -> pure Bitwuzla
                              input -> do
                                putStrLn $ "unrecognised solver: " <> input
                                exitFailure

getSrcInfo :: App m => Command Options.Unwrapped -> m DappInfo
getSrcInfo cmd = do
  root <- liftIO $ getRoot cmd
  conf <- readConfig
  liftIO $ withCurrentDirectory root $ do
    outExists <- doesDirectoryExist (root </> "out")
    if outExists
    then do
      buildOutput <- runEnv Env {config = conf} $ readBuildOutput root (getProjectType cmd)
      case buildOutput of
        Left _ -> pure emptyDapp
        Right o -> pure $ dappInfo root o
    else pure emptyDapp

getProjectType :: Command Options.Unwrapped -> ProjectType
getProjectType cmd = fromMaybe Foundry cmd.projectType

getRoot :: Command Options.Unwrapped -> IO FilePath
getRoot cmd = maybe getCurrentDirectory makeAbsolute (cmd.root)


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
assert :: App m => Command Options.Unwrapped -> m ()
assert cmd = do
  let block'  = maybe Fetch.Latest Fetch.BlockNumber cmd.block
      rpcinfo = (,) block' <$> cmd.rpc
  calldata <- liftIO $ buildCalldata cmd
  preState <- liftIO $ symvmFromCommand cmd calldata
  let errCodes = fromMaybe defaultPanicCodes cmd.assertions
  cores <- liftIO $ unsafeInto <$> getNumProcessors
  let solverCount = fromMaybe cores cmd.numSolvers
  solver <- liftIO $ getSolver cmd
  withSolvers solver solverCount cmd.smttimeout $ \solvers -> do
    let opts = VeriOpts { simp = True
                        , maxIter = cmd.maxIterations
                        , askSmtIters = cmd.askSmtIterations
                        , loopHeuristic = cmd.loopDetectionHeuristic
                        , rpcInfo = rpcinfo
    }
    (expr, res) <- verify solvers opts preState (Just $ checkAssertions errCodes)
    case res of
      [Qed _] -> do
        liftIO $ putStrLn "\nQED: No reachable property violations discovered\n"
        showExtras solvers cmd calldata expr
      _ -> do
        let cexs = snd <$> mapMaybe getCex res
            timeouts = mapMaybe getTimeout res
            counterexamples
              | null cexs = []
              | otherwise =
                 [ ""
                 , ("Discovered the following " <> (T.pack $ show (length cexs)) <> " counterexample(s):")
                 , ""
                 ] <> fmap (formatCex (fst calldata) Nothing) cexs
            unknowns
              | null timeouts = []
              | otherwise =
                 [ ""
                 , "Could not determine reachability of the following end state(s):"
                 , ""
                 ] <> fmap (formatExpr) timeouts
        liftIO $ T.putStrLn $ T.unlines (counterexamples <> unknowns)
        showExtras solvers cmd calldata expr
        liftIO $ exitFailure

showExtras :: App m => SolverGroup -> Command Options.Unwrapped -> (Expr Buf, [Prop]) -> Expr End -> m ()
showExtras solvers cmd calldata expr = do
  when cmd.showTree $ liftIO $ do
    putStrLn "=== Expression ===\n"
    T.putStrLn $ formatExpr expr
    putStrLn ""
  when cmd.showReachableTree $ do
    reached <- reachable solvers expr
    liftIO $ do
      putStrLn "=== Reachable Expression ===\n"
      T.putStrLn (formatExpr . snd $ reached)
      putStrLn ""
  when cmd.getModels $ do
    liftIO $ putStrLn $ "=== Models for " <> show (Expr.numBranches expr) <> " branches ==="
    ms <- produceModels solvers expr
    liftIO $ forM_ ms (showModel (fst calldata))

isTestOrLib :: Text -> Bool
isTestOrLib file = T.isSuffixOf ".t.sol" file || areAnyPrefixOf ["src/test/", "src/tests/", "lib/"] file

areAnyPrefixOf :: [Text] -> Text -> Bool
areAnyPrefixOf prefixes t = any (flip T.isPrefixOf t) prefixes

launchExec :: App m => Command Options.Unwrapped -> m ()
launchExec cmd = do
  dapp <- getSrcInfo cmd
  vm <- liftIO $ vmFromCommand cmd
  let
    block = maybe Fetch.Latest Fetch.BlockNumber cmd.block
    rpcinfo = (,) block <$> cmd.rpc

  -- TODO: we shouldn't need solvers to execute this code
  withSolvers Z3 0 Nothing $ \solvers -> do
    vm' <- EVM.Stepper.interpret (Fetch.oracle solvers rpcinfo) vm EVM.Stepper.runFully
    writeTraceDapp dapp vm'
    case vm'.result of
      Just (VMFailure (Revert msg)) -> liftIO $ do
        let res = case msg of
                    ConcreteBuf bs -> bs
                    _ -> "<symbolic>"
        putStrLn $ "Revert: " <> (show $ ByteStringS res)
        exitWith (ExitFailure 2)
      Just (VMFailure err) -> liftIO $ do
        putStrLn $ "Error: " <> show err
        exitWith (ExitFailure 2)
      Just (VMSuccess buf) -> liftIO $ do
        let msg = case buf of
              ConcreteBuf msg' -> msg'
              _ -> "<symbolic>"
        print $ "Return: " <> (show $ ByteStringS msg)
      _ ->
        internalError "no EVM result"

-- | Creates a (concrete) VM from command line options
vmFromCommand :: Command Options.Unwrapped -> IO (VM Concrete RealWorld)
vmFromCommand cmd = do
  (miner,ts,baseFee,blockNum,prevRan) <- case cmd.rpc of
    Nothing -> pure (LitAddr 0,Lit 0,0,0,0)
    Just url -> Fetch.fetchBlockFrom block url >>= \case
      Nothing -> error "Error: Could not fetch block"
      Just Block{..} -> pure ( coinbase
                             , timestamp
                             , baseFee
                             , number
                             , prevRandao
                             )

  contract <- case (cmd.rpc, cmd.address, cmd.code) of
    (Just url, Just addr', Just c) -> do
      Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error $ "Error: contract not found: " <> show address
        Just contract ->
          -- if both code and url is given,
          -- fetch the contract and overwrite the code
          pure $
            initialContract  (mkCode $ hexByteString "--code" $ strip0x c)
              & set #balance  (contract.balance)
              & set #nonce    (contract.nonce)
              & set #external (contract.external)

    (Just url, Just addr', Nothing) ->
      Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error $ "Error: contract not found: " <> show address
        Just contract -> pure contract

    (_, _, Just c)  ->
      pure $
        initialContract (mkCode $ hexByteString "--code" $ strip0x c)

    (_, _, Nothing) ->
      error "Error: must provide at least (rpc + address) or code"

  let ts' = case maybeLitWord ts of
        Just t -> t
        Nothing -> internalError "unexpected symbolic timestamp when executing vm test"

  vm <- stToIO $ vm0 baseFee miner ts' blockNum prevRan contract
  pure $ EVM.Transaction.initTx vm
    where
        block   = maybe Fetch.Latest Fetch.BlockNumber cmd.block
        value   = word (.value) 0
        caller  = addr (.caller) (LitAddr 0)
        origin  = addr (.origin) (LitAddr 0)
        calldata = ConcreteBuf $ bytes (.calldata) ""
        decipher = hexByteString "bytes" . strip0x
        mkCode bs = if cmd.create
                    then InitCode bs mempty
                    else RuntimeCode (ConcreteRuntimeCode bs)
        address = if cmd.create
                  then addr (.address) (Concrete.createAddress (fromJust $ maybeLitAddr origin) (W64 $ word64 (.nonce) 0))
                  else addr (.address) (LitAddr 0xacab)

        vm0 baseFee miner ts blockNum prevRan c = makeVm $ VMOpts
          { contract       = c
          , otherContracts = []
          , calldata       = (calldata, [])
          , value          = Lit value
          , address        = address
          , caller         = caller
          , origin         = origin
          , gas            = word64 (.gas) 0xffffffffffffffff
          , baseFee        = baseFee
          , priorityFee    = word (.priorityFee) 0
          , gaslimit       = word64 (.gaslimit) 0xffffffffffffffff
          , coinbase       = addr (.coinbase) miner
          , number         = word (.number) blockNum
          , timestamp      = Lit $ word (.timestamp) ts
          , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
          , gasprice       = word (.gasprice) 0
          , maxCodeSize    = word (.maxcodesize) 0xffffffff
          , prevRandao     = word (.prevRandao) prevRan
          , schedule       = feeSchedule
          , chainId        = word (.chainid) 1
          , create         = (.create) cmd
          , baseState      = EmptyBase
          , txAccessList   = mempty -- TODO: support me soon
          , allowFFI       = False
          , freshAddresses = 0
          }
        word f def = fromMaybe def (f cmd)
        word64 f def = fromMaybe def (f cmd)
        addr f def = maybe def LitAddr (f cmd)
        bytes f def = maybe def decipher (f cmd)

symvmFromCommand :: Command Options.Unwrapped -> (Expr Buf, [Prop]) -> IO (VM EVM.Types.Symbolic RealWorld)
symvmFromCommand cmd calldata = do
  (miner,blockNum,baseFee,prevRan) <- case cmd.rpc of
    Nothing -> pure (SymAddr "miner",0,0,0)
    Just url -> Fetch.fetchBlockFrom block url >>= \case
      Nothing -> error "Error: Could not fetch block"
      Just Block{..} -> pure ( coinbase
                             , number
                             , baseFee
                             , prevRandao
                             )

  let
    caller = maybe (SymAddr "caller") LitAddr cmd.caller
    ts = maybe Timestamp Lit cmd.timestamp
    callvalue = maybe TxValue Lit cmd.value
    storageBase = maybe AbstractBase parseInitialStorage (cmd.initialStorage)

  contract <- case (cmd.rpc, cmd.address, cmd.code) of
    (Just url, Just addr', _) ->
      Fetch.fetchContractFrom block url addr' >>= \case
        Nothing ->
          error "Error: contract not found."
        Just contract' -> pure contract''
          where
            contract'' = case cmd.code of
              Nothing -> contract'
              -- if both code and url is given,
              -- fetch the contract and overwrite the code
              Just c -> initialContract (mkCode $ decipher c)
                        & set #origStorage (contract'.origStorage)
                        & set #balance     (contract'.balance)
                        & set #nonce       (contract'.nonce)
                        & set #external    (contract'.external)

    (_, _, Just c)  -> case storageBase of
      EmptyBase -> pure (initialContract . mkCode $ decipher c)
      AbstractBase -> pure ((`abstractContract` address) . mkCode $ decipher c)

    (_, _, Nothing) ->
      error "Error: must provide at least (rpc + address) or code"

  vm <- stToIO $ vm0 baseFee miner ts blockNum prevRan calldata callvalue caller contract storageBase
  pure $ EVM.Transaction.initTx vm

  where
    decipher = hexByteString "bytes" . strip0x
    block = maybe Fetch.Latest Fetch.BlockNumber cmd.block
    origin = eaddr (.origin) (SymAddr "origin")
    mkCode bs = if cmd.create
                   then InitCode bs mempty
                   else RuntimeCode (ConcreteRuntimeCode bs)
    address = eaddr (.address) (SymAddr "entrypoint")
    vm0 baseFee miner ts blockNum prevRan cd callvalue caller c baseState = makeVm $ VMOpts
      { contract       = c
      , otherContracts = []
      , calldata       = cd
      , value          = callvalue
      , address        = address
      , caller         = caller
      , origin         = origin
      , gas            = ()
      , gaslimit       = word64 (.gaslimit) 0xffffffffffffffff
      , baseFee        = baseFee
      , priorityFee    = word (.priorityFee) 0
      , coinbase       = eaddr (.coinbase) miner
      , number         = word (.number) blockNum
      , timestamp      = ts
      , blockGaslimit  = word64 (.gaslimit) 0xffffffffffffffff
      , gasprice       = word (.gasprice) 0
      , maxCodeSize    = word (.maxcodesize) 0xffffffff
      , prevRandao     = word (.prevRandao) prevRan
      , schedule       = feeSchedule
      , chainId        = word (.chainid) 1
      , create         = (.create) cmd
      , baseState      = baseState
      , txAccessList   = mempty
      , allowFFI       = False
      , freshAddresses = 0
      }
    word f def = fromMaybe def (f cmd)
    word64 f def = fromMaybe def (f cmd)
    eaddr f def = maybe def LitAddr (f cmd)

unitTestOptions :: Command Options.Unwrapped -> SolverGroup -> Maybe BuildOutput -> IO (UnitTestOptions RealWorld)
unitTestOptions cmd solvers buildOutput = do
  root <- getRoot cmd
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput

  let rpcinfo = case (cmd.number, cmd.rpc) of
          (Just block, Just url) -> Just (Fetch.BlockNumber block, url)
          (Nothing, Just url) -> Just (Fetch.Latest, url)
          _ -> Nothing
  params <- paramsFromRpc rpcinfo

  let
    testn = params.number
    block' = if 0 == testn
       then Fetch.Latest
       else Fetch.BlockNumber testn

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = case cmd.rpc of
         Just url -> Just (block', url)
         Nothing  -> Nothing
    , maxIter = cmd.maxIterations
    , askSmtIters = cmd.askSmtIterations
    , smtTimeout = cmd.smttimeout
    , solver = cmd.solver
    , verbose = cmd.verbose
    , match = T.pack $ fromMaybe ".*" cmd.match
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = cmd.ffi
    }
parseInitialStorage :: InitialStorage -> BaseState
parseInitialStorage Empty = EmptyBase
parseInitialStorage Abstract = AbstractBase
