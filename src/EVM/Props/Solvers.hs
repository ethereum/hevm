{- |
    Module: EVM.Props.Solvers
    Description: Solver orchestration
-}
module EVM.Props.Solvers where

import Prelude hiding (LT, GT)

import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Monad
import Data.Char (isSpace)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))

import EVM.Props.SMT

-- | Supported solvers
data Solver
  = Z3
  | CVC5
  | Bitwuzla
  | Custom Text

instance Show Solver where
  show Z3 = "z3"
  show CVC5 = "cvc5"
  show Bitwuzla = "bitwuzla"
  show (Custom s) = T.unpack s


-- | A running solver instance
data SolverInstance = SolverInstance
  { solvertype :: Solver
  , stdin      :: Handle
  , stdout     :: Handle
  , stderr     :: Handle
  , process    :: ProcessHandle
  }

-- | A channel representing a group of solvers
newtype SolverGroup vs c = SolverGroup (Chan (Task vs c))

-- | A script to be executed, a list of models to be extracted in the case of a sat result, and a channel where the result should be written
data Task vs c = Task
  { script :: Script
  , cexvars :: vs
  , resultChan :: Chan (CheckSatResult c)
  }

-- | The result of a call to (check-sat)
data CheckSatResult c
  = Sat c
  | Unsat
  | Unknown
  | Error Text
  deriving (Show, Eq)

isSat :: CheckSatResult c -> Bool
isSat (Sat _) = True
isSat _ = False

isErr :: CheckSatResult c -> Bool
isErr (Error _) = True
isErr _ = False

isUnsat :: CheckSatResult c -> Bool
isUnsat Unsat = True
isUnsat _ = False

checkSat :: SolverGroup v c -> Script -> v -> IO (CheckSatResult c)
checkSat (SolverGroup taskQueue) script cexvars = do
  -- prepare result channel
  resChan <- newChan
  -- send task to solver group
  writeChan taskQueue (Task script cexvars resChan)
  -- collect result
  readChan resChan

data SMTConf vs c = SMTConf
  { solver :: Solver
  , count :: Int
  , timeout :: Maybe Int
  , modelfn :: SolverInstance -> vs -> IO c
  }

withSolvers :: SMTConf vs c -> (SolverGroup vs c -> IO a) -> IO a
withSolvers conf cont = do
  -- spawn solvers
  instances <- mapM (const $ spawnSolver conf.solver conf.timeout) [1..conf.count]
  -- spawn orchestration thread
  taskQueue <- newChan
  availableInstances <- newChan
  forM_ instances (writeChan availableInstances)
  orchestrateId <- forkIO $ orchestrate taskQueue availableInstances

  -- run continuation with task queue
  res <- cont (SolverGroup taskQueue)

  -- cleanup and return results
  mapM_ stopSolver instances
  killThread orchestrateId
  pure res
  where
    orchestrate queue avail = do
      task <- readChan queue
      inst <- readChan avail
      _ <- forkIO $ runTask task inst avail
      orchestrate queue avail

    runTask (Task (Script cmds) cexvars r) inst availableInstances = do
      -- reset solver and send all lines of provided script
      out <- sendScript inst (Script (L [A "reset"] : cmds))
      case out of
        -- if we got an error then return it
        Left e -> writeChan r (Error ("error while writing SMT to solver: " <> e))
        -- otherwise call (check-sat), parse the result, and send it down the result channel
        Right () -> do
          sat <- sendLine inst "(check-sat)"
          res <- case sat of
            "sat" -> Sat <$> conf.modelfn inst cexvars
            "unsat" -> pure Unsat
            "timeout" -> pure Unknown
            "unknown" -> pure Unknown
            _ -> pure . Error $ "Unable to parse solver output: " <> sat
          writeChan r res

      -- put the instance back in the list of available instances
      writeChan availableInstances inst

mkTimeout :: Maybe Int -> Text
mkTimeout t = T.pack $ show $ (1000 *)$ case t of
  Nothing -> 300 :: Int
  Just t' -> t'

-- | Arguments used when spawing a solver instance
solverArgs :: Solver -> Maybe Int -> [Text]
solverArgs solver timeout = case solver of
  Bitwuzla -> error "TODO: Bitwuzla args"
  Z3 ->
    [ "-in" ]
  CVC5 ->
    [ "--lang=smt"
    , "--produce-models"
    , "--print-success"
    , "--interactive"
    , "--tlimit-per=" <> mkTimeout timeout
    ]
  Custom _ -> []

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Maybe Int -> IO SolverInstance
spawnSolver solver timeout = do
  let cmd = (proc (show solver) (fmap T.unpack $ solverArgs solver timeout)) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
  (Just stdin, Just stdout, Just stderr, process) <- createProcess cmd
  hSetBuffering stdin (BlockBuffering (Just 1000000))
  let solverInstance = SolverInstance solver stdin stdout stderr process

  case solver of
    CVC5 -> pure solverInstance
    _ -> do
      _ <- sendLine' solverInstance $ "(set-option :timeout " <> mkTimeout timeout <> ")"
      _ <- sendLine solverInstance "(set-option :print-success true)"
      pure solverInstance

-- | Cleanly shutdown a running solver instnace
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> Script -> IO (Either Text ())
sendScript solver (Script cmds) = do
  let sexprs = fmap pprint cmds
  go sexprs
  where
    go [] = pure $ Right ()
    go (c:cs) = do
      out <- sendCommand solver c
      case out of
        "success" -> go cs
        e -> pure $ Left $ "Solver returned an error:\n" <> e <> "\nwhile sending the following line: " <> c

checkCommand :: SolverInstance -> Text -> IO ()
checkCommand inst cmd = do
  res <- sendCommand inst cmd
  case res of
    "success" -> pure ()
    _ -> error $ "Internal Error: Unexpected solver output: " <> (T.unpack res)

-- | Sends a single command to the solver, returns the first available line from the output buffer
sendCommand :: SolverInstance -> Text -> IO Text
sendCommand inst cmd = do
  -- trim leading whitespace
  let cmd' = T.dropWhile isSpace cmd
  case T.unpack cmd' of
    "" -> pure "success"      -- ignore blank lines
    ';' : _ -> pure "success" -- ignore comments
    _ -> sendLine inst cmd'

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
sendLine :: SolverInstance -> Text -> IO Text
sendLine (SolverInstance _ stdin stdout _ _) cmd = do
  T.hPutStr stdin (T.append cmd "\n")
  hFlush stdin
  T.hGetLine stdout

-- | Sends a string to the solver and appends a newline, doesn't return stdout
sendLine' :: SolverInstance -> Text -> IO ()
sendLine' (SolverInstance _ stdin _ _ _) cmd = do
  T.hPutStr stdin (T.append cmd "\n")
  hFlush stdin

-- | Returns a string representation of the model for the requested variable
getValue :: SolverInstance -> Text -> IO Text
getValue (SolverInstance _ stdin stdout _ _) var = do
  T.hPutStr stdin (T.append (T.append "(get-value (" var) "))\n")
  hFlush stdin
  fmap (T.unlines . reverse) (readSExpr stdout)

-- | Reads lines from h until we have a balanced sexpr
readSExpr :: Handle -> IO [Text]
readSExpr h = go 0 0 []
  where
    go 0 0 _ = do
      line <- T.hGetLine h
      let ls = T.length $ T.filter (== '(') line
          rs = T.length $ T.filter (== ')') line
      if ls == rs
         then pure [line]
         else go ls rs [line]
    go ls rs prev = do
      line <- T.hGetLine h
      let ls' = T.length $ T.filter (== '(') line
          rs' = T.length $ T.filter (== ')') line
      if (ls + ls') == (rs + rs')
         then pure $ line : prev
         else go (ls + ls') (rs + rs') (line : prev)
