{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
module EVM.Solvers where

import Control.Concurrent (forkIO, killThread)
import Control.Concurrent.Chan (Chan, newChan, readChan, writeChan)
import Control.Monad
import Data.Char (isSpace)
import Data.Maybe (fromMaybe)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.Builder
import Data.Text.Lazy.IO qualified as T
import EVM.SMT
import GHC.IO.Handle (BufferMode (..), Handle, hFlush, hSetBuffering)
import GHC.Natural
import System.Process (ProcessHandle, StdStream (..), cleanupProcess, createProcess, proc, std_err, std_in, std_out)
import Prelude hiding (GT, LT)


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
  { _type :: Solver
  , _stdin :: Handle
  , _stdout :: Handle
  , _stderr :: Handle
  , _process :: ProcessHandle
  }


-- | A channel representing a group of solvers
newtype SolverGroup = SolverGroup (Chan Task)


-- | A script to be executed, a list of models to be extracted in the case of a sat result, and a channel where the result should be written
data Task = Task
  { script :: SMT2
  , resultChan :: Chan CheckSatResult
  }


-- | The result of a call to (check-sat)
data CheckSatResult
  = Sat SMTCex
  | Unsat
  | Unknown
  | Error TS.Text
  deriving (Show, Eq)


isSat :: CheckSatResult -> Bool
isSat (Sat _) = True
isSat _ = False


isErr :: CheckSatResult -> Bool
isErr (Error _) = True
isErr _ = False


isUnsat :: CheckSatResult -> Bool
isUnsat Unsat = True
isUnsat _ = False


checkSat :: SolverGroup -> SMT2 -> IO CheckSatResult
checkSat (SolverGroup taskQueue) script = do
  -- prepare result channel
  resChan <- newChan

  -- send task to solver group
  writeChan taskQueue (Task script resChan)

  -- collect result
  readChan resChan


withSolvers :: Solver -> Natural -> Maybe Natural -> (SolverGroup -> IO a) -> IO a
withSolvers solver count timeout cont = do
  -- spawn solvers
  instances <- mapM (const $ spawnSolver solver timeout) [1 .. count]

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

  runTask (Task (SMT2 cmds cexvars) r) inst availableInstances = do
    -- reset solver and send all lines of provided script
    out <- sendScript inst (SMT2 ("(reset)" : cmds) cexvars)
    case out of
      -- if we got an error then return it
      Left e -> writeChan r (Error ("error while writing SMT to solver: " <> T.toStrict e))
      -- otherwise call (check-sat), parse the result, and send it down the result channel
      Right () -> do
        sat <- sendLine inst "(check-sat)"
        res <- case sat of
          "sat" -> do
            calldatamodels <- getVars parseVar (getValue inst) (fmap T.toStrict cexvars.calldataV)
            buffermodels <- getBufs (getValue inst) (fmap T.toStrict cexvars.buffersV)
            storagemodels <- getStore (getValue inst) cexvars.storeReads
            blockctxmodels <- getVars parseBlockCtx (getValue inst) (fmap T.toStrict cexvars.blockContextV)
            txctxmodels <- getVars parseFrameCtx (getValue inst) (fmap T.toStrict cexvars.txContextV)
            pure $
              Sat $
                SMTCex
                  { vars = calldatamodels
                  , buffers = buffermodels
                  , store = storagemodels
                  , blockContext = blockctxmodels
                  , txContext = txctxmodels
                  }
          "unsat" -> pure Unsat
          "timeout" -> pure Unknown
          "unknown" -> pure Unknown
          _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat
        writeChan r res

    -- put the instance back in the list of available instances
    writeChan availableInstances inst


-- | Arguments used when spawing a solver instance
solverArgs :: Solver -> Maybe (Natural) -> [Text]
solverArgs solver timeout = case solver of
  Bitwuzla -> error "TODO: Bitwuzla args"
  Z3 ->
    ["-in"]
  CVC5 ->
    [ "--lang=smt"
    , "--no-interactive"
    , "--produce-models"
    , "--tlimit-per=" <> T.pack (show (1000 * fromMaybe 10 timeout))
    ]
  Custom _ -> []


-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Maybe (Natural) -> IO SolverInstance
spawnSolver solver timeout = do
  let cmd = (proc (show solver) (fmap T.unpack $ solverArgs solver timeout)){std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe}
  (Just stdin, Just stdout, Just stderr, process) <- createProcess cmd
  hSetBuffering stdin (BlockBuffering (Just 1000000))
  let solverInstance = SolverInstance solver stdin stdout stderr process
  case timeout of
    Nothing -> pure solverInstance
    Just t -> case solver of
      CVC5 -> pure solverInstance
      _ -> do
        _ <- sendLine' solverInstance $ "(set-option :timeout " <> T.pack (show t) <> ")"
        pure solverInstance


-- | Cleanly shutdown a running solver instnace
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)


-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> SMT2 -> IO (Either Text ())
sendScript solver (SMT2 cmds _) = do
  sendLine' solver (T.unlines $ fmap toLazyText cmds)
  pure $ Right ()


-- | Sends a single command to the solver, returns the first available line from the output buffer
sendCommand :: SolverInstance -> Text -> IO Text
sendCommand inst cmd = do
  -- trim leading whitespace
  let cmd' = T.dropWhile isSpace cmd
  case T.unpack cmd' of
    "" -> pure "success" -- ignore blank lines
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
