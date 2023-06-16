{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language PolyKinds #-}
{-# Language ScopedTypeVariables #-}

{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
module EVM.Solvers where

import Prelude hiding (LT, GT)

import GHC.Natural
import Control.Monad
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Monad.State.Strict
import Data.Char (isSpace)
import Data.Maybe (fromMaybe)

import Data.Text.Lazy (Text)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as TS
import qualified Data.Text.Lazy as T
import qualified Data.Text.Lazy.IO as T
import Data.Text.Lazy.Builder
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..))

import EVM.SMT
import EVM.Types hiding (Unknown)

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
            "sat" -> Sat <$> getModel inst cexvars
            "unsat" -> pure Unsat
            "timeout" -> pure Unknown
            "unknown" -> pure Unknown
            _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat
          writeChan r res

      -- put the instance back in the list of available instances
      writeChan availableInstances inst

getModel :: SolverInstance -> CexVars -> IO SMTCex
getModel inst cexvars = do
  -- get an initial version of the model from the solver
  initialModel <- getRaw
  -- get concrete values for each buffers max read index
  hints <- capHints <$> queryMaxReads (getValue inst) cexvars.buffers
  -- check the sizes of buffer models and shrink if needed
  if bufsUsable initialModel
  then do
    pure (mkConcrete initialModel)
  else mkConcrete . snd <$> runStateT (shrinkModel hints) initialModel
  where
    getRaw :: IO SMTCex
    getRaw = do
      vars <- getVars parseVar (getValue inst) (fmap T.toStrict cexvars.calldata)
      buffers <- getBufs (getValue inst) (Map.keys cexvars.buffers)
      storage <- getStore (getValue inst) cexvars.storeReads
      blockctx <- getVars parseBlockCtx (getValue inst) (fmap T.toStrict cexvars.blockContext)
      txctx <- getVars parseFrameCtx (getValue inst) (fmap T.toStrict cexvars.txContext)
      pure $ SMTCex vars buffers storage blockctx txctx

    -- sometimes the solver might give us back a model for the max read index
    -- that is too high to be a useful cex (e.g. in the case of reads from a
    -- symbolic index), so we cap the max value of the starting point to be 1024
    capHints :: Map Text W256 -> Map Text W256
    capHints = fmap (min 1024)

    -- shrink all the buffers in a model
    shrinkModel :: Map Text W256 -> StateT SMTCex IO ()
    shrinkModel hints = do
      m <- get
      -- iterate over all the buffers in the model, and shrink each one in turn if needed
      forM_ (Map.keys m.buffers) $ \case
        AbstractBuf b -> do
          let name = T.fromStrict b
              hint = fromMaybe
                       (error $ "Internal Error: Could not find hint for buffer: " <> T.unpack name)
                       (Map.lookup name hints)
          shrinkBuf name hint
        _ -> error "Internal Error: Received model from solver for non AbstractBuf"

    -- starting with some guess at the max useful size for a buffer, cap
    -- it's size to that value, and ask the solver to check satisfiability. If
    -- it's still sat with the new constraint, leave that constraint on the
    -- stack and return a new model, if it's unsat, double the size of the hint
    -- and try again.
    shrinkBuf :: Text -> W256 -> StateT SMTCex IO ()
    shrinkBuf buf hint = do
      let encBound = "(_ bv" <> (T.pack $ show (num hint :: Integer)) <> " 256)"
      sat <- liftIO $ do
        sendLine' inst "(push)"
        sendLine' inst $ "(assert (bvule " <> buf <> "_length " <> encBound <> "))"
        sendLine inst "(check-sat)"
      case sat of
        "sat" -> do
          model <- liftIO getRaw
          put model
        "unsat" -> do
          liftIO $ sendLine' inst "(pop)"
          shrinkBuf buf (if hint == 0 then hint + 1 else hint * 2)
        _ -> error "TODO: HANDLE ERRORS"

    -- Collapses the abstract description of a models buffers down to a bytestring
    mkConcrete :: SMTCex -> SMTCex
    mkConcrete c = fromMaybe
      (error $ "Internal Error: counterexample contains buffers that are too large to be represented as a ByteString: " <> show c)
      (flattenBufs c)

    -- we set a pretty arbitrary upper limit (of 1024) to decide if we need to do some shrinking
    bufsUsable :: SMTCex -> Bool
    bufsUsable model = any (go . snd) (Map.toList model.buffers)
      where
        go (Flat _) = True
        go (Comp c) = case c of
          (Base _ sz) -> sz <= 1024
          -- TODO: do I need to check the write idx here?
          (Write _ idx next) -> idx <= 1024 && go (Comp next)

mkTimeout :: Maybe Natural -> Text
mkTimeout t = T.pack $ show $ (1000 *)$ case t of
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
    , "--no-interactive"
    , "--produce-models"
    , "--tlimit-per=" <> mkTimeout timeout
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
      _ <- sendLine' solverInstance $ "(set-option :timeout " <> mkTimeout timeout <> ")"
      pure solverInstance

-- | Cleanly shutdown a running solver instnace
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout stderr process) = cleanupProcess (Just stdin, Just stdout, Just stderr, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> SMT2 -> IO (Either Text ())
sendScript solver (SMT2 cmds _) = do
  sendLine' solver (splitSExpr $ fmap toLazyText cmds)
  pure $ Right()

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

-- From a list of lines, take each separate SExpression and put it in
-- its own list, after removing comments.
splitSExpr :: [Text] -> Text
splitSExpr ls =
  -- split lines, strip comments, and append everything to a single line
  let text = T.intercalate " " $ T.takeWhile (/= ';') <$> concatMap T.lines ls in
  T.unlines $ filter (/= "") $ go text []
  where
    go "" acc = reverse acc
    go text acc =
      let (sexpr, text') = getSExpr text in
      let (sexpr', rest) = T.breakOnEnd ")" sexpr in
      go text' ((T.strip rest):(T.strip sexpr'):acc)

data Par = LPar | RPar

-- take the first SExpression and return the rest of the text
getSExpr :: Text -> (Text, Text)
getSExpr l = go LPar l 0 []
  where
    go _ text 0 prev@(_:_) = (T.intercalate "" (reverse prev), text)
    go _ _ r _ | r < 0 = error "Internal error: Unbalanced SExpression"
    go _ "" _ _  = error "Internal error: Unbalanced SExpression"
    -- find the next left parenthesis
    go LPar line r prev = -- r is how many right parentheses we are missing
      let (before, after) = T.breakOn "(" line in
      let rp = T.length $ T.filter (== ')') before in
      go RPar after (r - rp) (if before == "" then prev else before : prev)
    -- find the next right parenthesis
    go RPar line r prev =
      let (before, after) = T.breakOn ")" line in
      let lp = T.length $ T.filter (== '(') before in
      go LPar after (r + lp) (if before == "" then prev else before : prev)
