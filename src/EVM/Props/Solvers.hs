{- |
    Module: Props.Solvers
    Description: Solver orchestration
-}

{-# LANGUAGE UndecidableInstances #-}

module EVM.Props.Solvers where

import Prelude hiding (LT, GT)

import GHC.Natural
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Monad
import Control.Monad.Except
import Data.HashSet (HashSet)
import Data.HashSet qualified as HashSet
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Text.Lazy.Builder
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))

import EVM.Props.SMT2 (Encoding(..), Propositional(..), Assignment, FreeVar, SMT(..))

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
newtype SolverGroup = SolverGroup (Chan Task)

-- | A script to be executed, a list of models to be extracted in the case of a sat result, and a channel where the result should be written
data Task = forall a . Propositional a => Task
  { script :: HashSet a
  , resultChan :: Chan CheckSatResult
  }

-- | The result of a call to (check-sat)
data CheckSatResult
  = Sat (HashSet Assignment)
  | Unsat
  | Unknown
  | Error TS.Text
  deriving (Eq, Show)

newtype Script = Script [SMT]

isSat :: CheckSatResult -> Bool
isSat (Sat _) = True
isSat _ = False

isErr :: CheckSatResult -> Bool
isErr (Error _) = True
isErr _ = False

isUnsat :: CheckSatResult -> Bool
isUnsat Unsat = True
isUnsat _ = False

checkSat :: Propositional p => SolverGroup -> HashSet p -> IO CheckSatResult
checkSat (SolverGroup taskQueue) props = do
  -- prepare result channel
  resChan <- newChan
  -- send task to solver group
  writeChan taskQueue (Task props resChan)
  -- collect result
  readChan resChan

withSolvers :: Solver -> Natural -> Maybe Natural -> (SolverGroup -> IO a) -> IO a
withSolvers solver count timeout cont = do
  -- spawn solvers
  instances <- mapM (const $ spawnSolver solver timeout) [1..count]
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

    runTask (Task ps r) inst availableInstances = do
      let (Script cmds) = mkScript ps
      -- reset solver and send all lines of provided script
      out <- sendScript inst (Script (L [A "reset"] : cmds))
      case out of
        -- if we got an error then return it
        Left e -> writeChan r (Error e)
        -- otherwise call (check-sat), parse the result, and send it down the result channel
        Right () -> do
          sat <- sendLine inst (L [A "check-sat"])
          res <- case sat of
            "sat" -> do
              getModel inst (fmap frees ps) >>= \case
                Right m -> pure $ Sat m
                Left e -> pure $ Error e
            "unsat" -> pure Unsat
            "timeout" -> pure Unknown
            "unknown" -> pure Unknown
            _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat
          writeChan r res

      -- put the instance back in the list of available instances
      writeChan availableInstances inst

mkScript :: Propositional p => HashSet p -> Script
mkScript = undefined

getModel :: SolverInstance -> HashSet FreeVar -> IO (Either TS.Text (HashSet Assignment))
getModel inst ps = do
  assigns <- mapM (extract (getValue inst)) (HashSet.toList $ frees ps)
  pure $ mapRight HashSet.fromList $ sequence assigns

getValue :: SolverInstance -> SMT -> IO (Either TS.Text SMT)
getValue inst v = do
  value <- sendLine inst (L [A "get-value", L [v]])
  pure (error "TODO")
  -- case parse parseSMT "" value of
  --   Right s -> pure $ Right s
  --   Left e -> pure $ Left $ "Unable to parse model for " <> asText v <> ":\n" <> (TS.pack $ errorBundlePretty e)

mkTimeout :: Maybe Natural -> TS.Text
mkTimeout t = TS.pack $ show $ (1000 *)$ case t of
  Nothing -> 300 :: Natural
  Just t' -> t'

-- | Arguments used when spawing a solver instance
solverArgs :: Solver -> Maybe Natural -> [Text]
solverArgs solver timeout = case solver of
  Bitwuzla -> error "TODO: Bitwuzla args"
  Z3 ->
    [ "-in" ]
  CVC5 ->
    [ "--lang=smt"
    , "--produce-models"
    , "--tlimit-per=" <> T.fromStrict (mkTimeout timeout)
    ]
  Custom _ -> []

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Maybe (Natural) -> IO SolverInstance
spawnSolver solver timeout = do
  let cmd = (proc (show solver) (fmap T.unpack $ solverArgs solver timeout)) { std_in = CreatePipe, std_out = CreatePipe, std_err = CreatePipe }
  (Just stdin, Just stdout, Just stderr, process) <- createProcess cmd
  hSetBuffering stdin (BlockBuffering (Just 1000000))
  let solverInstance = SolverInstance solver stdin stdout stderr process
  case solver of
    CVC5 -> pure solverInstance
    _ -> do
      r <- runExceptT $ do
        ExceptT $ fmap checkSuccess $ sendLine solverInstance $ L [A "set-option", A ":print-success", A "true"]
        ExceptT $ fmap checkSuccess $ sendLine solverInstance $ L [A "set-option", A ":timeout", A (mkTimeout timeout)]
      case r of
        Right () -> pure solverInstance
        Left e -> error $ "Encountered error when spawning solver: " <> T.unpack e

checkSuccess :: Text -> Either Text ()
checkSuccess = \case
  "success" -> Right ()
  e -> Left e

-- | Cleanly shutdown a running solver instnace
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> Script -> IO (Either TS.Text ())
sendScript solver = \case
  Script [] -> pure $ Right ()
  Script (c:cs) -> do
    r <- sendLine solver c
    case r of
      "success" -> sendScript solver (Script cs)
      e -> pure $ Left $ "error: " <> (T.toStrict e) <> ". from: " <> (asText c)

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
sendLine :: SolverInstance -> SMT -> IO Text
sendLine (SolverInstance _ stdin stdout _ _) cmd = do
  T.hPutStr stdin (T.append (toLazyText $ serialize cmd) "\n")
  hFlush stdin
  T.hGetLine stdout

mapRight :: (b -> c) -> Either a b -> Either a c
mapRight f (Right a) = Right (f a)
mapRight _ (Left l) = Left l
