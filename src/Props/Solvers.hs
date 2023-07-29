{- |
    Module: Props.Solvers
    Description: Solver orchestration
-}
module Props.Solvers where

import Prelude hiding (LT, GT)

import GHC.Natural
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Monad
import Control.Monad.Except
import Data.Set (Set)
import Data.SExpresso.SExpr
import Data.SExpresso.Parse
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Text.Lazy.Builder
import Data.Typeable
import Data.Void
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))
import Text.Megaparsec (Parsec, parse, some)
import Text.Megaparsec.Char (letterChar)

import EVM.Props

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
data Task = Task
  { script :: Set Prop
  , resultChan :: Chan CheckSatResult
  }

data Assign where
  Assign :: forall e . (Show (Assignment e), Eq (Assignment e), Typeable e) => Assignment e -> Assign

deriving instance Show Assign
instance Eq Assign where
  Assign (a :: Assignment t0) == Assign (b :: Assignment t1)
    = case eqT @t0 @t1 of
        Just Refl -> a == b
        Nothing -> False

-- | The result of a call to (check-sat)
data CheckSatResult
  = Sat (Set Assign)
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

checkSat :: SolverGroup -> Set Prop -> IO CheckSatResult
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
      out <- sendScript inst (Script (Sexp [A "reset"] : cmds))
      case out of
        -- if we got an error then return it
        Left e -> writeChan r (Error ("error while writing SMT to solver: " <> T.toStrict e))
        -- otherwise call (check-sat), parse the result, and send it down the result channel
        Right () -> do
          sat <- sendLine inst (Sexp [A "check-sat"])
          res <- case sat of
            "sat" -> do
              getModel inst ps >>= \case
                Right m -> pure $ Sat m
                Left e -> pure . Error . T.toStrict $ e
            "unsat" -> pure Unsat
            "timeout" -> pure Unknown
            "unknown" -> pure Unknown
            _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat
          writeChan r res

      -- put the instance back in the list of available instances
      writeChan availableInstances inst

getModel :: SolverInstance -> Set Prop -> IO (Either Text (Set Assign))
getModel inst ps = undefined

getValue :: SolverInstance -> SMT -> IO (Either Text SMT)
getValue inst v = do
  value <- sendLine inst (Sexp [A "get-value", v])
  case parse parseSMT "" value of
    Right s -> pure $ Right s
    Left e -> pure $ Left $ "Unable to parse model for " <> asText v <> ": " <> T.pack (show e)

asText :: SMT -> Text
asText = toLazyText . serialize

parseSMT :: Parsec Void Text SMT
parseSMT = decodeOne $ plainSExprParser (fmap (T.toStrict . T.pack) (some letterChar))

-- getModel :: SolverInstance -> CexVars -> IO SMTCex
-- getModel inst cexvars = do
--   -- get an initial version of the model from the solver
--   initialModel <- getRaw
--   -- get concrete values for each buffers max read index
--   hints <- capHints <$> queryMaxReads (getValue inst) cexvars.buffers
--   -- check the sizes of buffer models and shrink if needed
--   if bufsUsable initialModel
--   then do
--     pure (mkConcrete initialModel)
--   else mkConcrete . snd <$> runStateT (shrinkModel hints) initialModel
--   where
--     getRaw :: IO SMTCex
--     getRaw = do
--       vars <- getVars parseVar (getValue inst) (fmap T.toStrict cexvars.calldata)
--       buffers <- getBufs (getValue inst) (Map.keys cexvars.buffers)
--       storage <- getStore (getValue inst) cexvars.storeReads
--       blockctx <- getVars parseBlockCtx (getValue inst) (fmap T.toStrict cexvars.blockContext)
--       txctx <- getVars parseFrameCtx (getValue inst) (fmap T.toStrict cexvars.txContext)
--       pure $ SMTCex vars buffers storage blockctx txctx
--
--     -- sometimes the solver might give us back a model for the max read index
--     -- that is too high to be a useful cex (e.g. in the case of reads from a
--     -- symbolic index), so we cap the max value of the starting point to be 1024
--     capHints :: Map Text W256 -> Map Text W256
--     capHints = fmap (min 1024)
--
--     -- shrink all the buffers in a model
--     shrinkModel :: Map Text W256 -> StateT SMTCex IO ()
--     shrinkModel hints = do
--       m <- get
--       -- iterate over all the buffers in the model, and shrink each one in turn if needed
--       forM_ (Map.keys m.buffers) $ \case
--         AbstractBuf b -> do
--           let name = T.fromStrict b
--               hint = fromMaybe
--                        (internalError $ "Could not find hint for buffer: " <> T.unpack name)
--                        (Map.lookup name hints)
--           shrinkBuf name hint
--         _ -> internalError "Received model from solver for non AbstractBuf"
--
--     -- starting with some guess at the max useful size for a buffer, cap
--     -- it's size to that value, and ask the solver to check satisfiability. If
--     -- it's still sat with the new constraint, leave that constraint on the
--     -- stack and return a new model, if it's unsat, double the size of the hint
--     -- and try again.
--     shrinkBuf :: Text -> W256 -> StateT SMTCex IO ()
--     shrinkBuf buf hint = do
--       let encBound = "(_ bv" <> (T.pack $ show (into hint :: Integer)) <> " 256)"
--       sat <- liftIO $ do
--         sendLine' inst "(push)"
--         sendLine' inst $ "(assert (bvule " <> buf <> "_length " <> encBound <> "))"
--         sendLine inst "(check-sat)"
--       case sat of
--         "sat" -> do
--           model <- liftIO getRaw
--           put model
--         "unsat" -> do
--           liftIO $ sendLine' inst "(pop)"
--           shrinkBuf buf (if hint == 0 then hint + 1 else hint * 2)
--         _ -> internalError "SMT solver returned unexpected result (neither sat/unsat), which HEVM currently cannot handle"
--
--     -- Collapses the abstract description of a models buffers down to a bytestring
--     mkConcrete :: SMTCex -> SMTCex
--     mkConcrete c = fromMaybe
--       (internalError $ "counterexample contains buffers that are too large to be represented as a ByteString: " <> show c)
--       (flattenBufs c)
--
--     -- we set a pretty arbitrary upper limit (of 1024) to decide if we need to do some shrinking
--     bufsUsable :: SMTCex -> Bool
--     bufsUsable model = any (go . snd) (Map.toList model.buffers)
--       where
--         go (Flat _) = True
--         go (Comp c) = case c of
--           (Base _ sz) -> sz <= 1024
--           -- TODO: do I need to check the write idx here?
--           (Write _ idx next) -> idx <= 1024 && go (Comp next)

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
        ExceptT $ fmap checkSuccess $ sendLine solverInstance $ Sexp [A "set-option", A ":print-success"]
        ExceptT $ fmap checkSuccess $ sendLine solverInstance $ Sexp [A "set-option", A ":timeout", A (mkTimeout timeout)]
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
sendScript :: SolverInstance -> Script -> IO (Either Text ())
sendScript solver = \case
  Script [] -> pure $ Right ()
  Script (c:cs) -> do
    r <- sendLine solver c
    case r of
      "success" -> sendScript solver (Script cs)
      e -> pure $ Left e

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
sendLine :: SolverInstance -> SMT -> IO Text
sendLine (SolverInstance _ stdin stdout _ _) cmd = do
  T.hPutStr stdin (T.append (toLazyText $ serialize cmd) "\n")
  hFlush stdin
  T.hGetLine stdout
