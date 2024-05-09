{- |
    Module: EVM.Solvers
    Description: Solver orchestration
-}
module EVM.Solvers where

import Prelude hiding (LT, GT)

import GHC.Natural
import GHC.IO.Handle (Handle, hFlush, hSetBuffering, BufferMode(..))
import Control.Concurrent.Chan (Chan, newChan, writeChan, readChan)
import Control.Concurrent (forkIO, killThread)
import Control.Monad
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Data.Char (isSpace)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isJust, fromJust)
import Data.Text qualified as TS
import Data.Text.Lazy (Text)
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.IO qualified as T
import Data.Text.Lazy.Builder
import System.Process (createProcess, cleanupProcess, proc, ProcessHandle, std_in, std_out, std_err, StdStream(..), createPipe)
import Witch (into)
import EVM.Effects
import EVM.Fuzz (tryCexFuzz)

import EVM.SMT
import EVM.Types (W256, Expr(AbstractBuf), internalError)

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

writeSMT2File :: SMT2 -> Int -> String -> IO ()
writeSMT2File smt2 count abst =
  do
    let content = formatSMT2 smt2 <> "\n\n(check-sat)"
    T.writeFile ("query-" <> (show count) <> "-" <> abst <> ".smt2") content

withSolvers :: App m => Solver -> Natural -> Maybe Natural -> (SolverGroup -> m a) -> m a
withSolvers solver count timeout cont = do
    -- spawn solvers
    instances <- mapM (const $ liftIO $ spawnSolver solver timeout) [1..count]
    -- spawn orchestration thread
    taskQueue <- liftIO newChan
    availableInstances <- liftIO newChan
    liftIO $ forM_ instances (writeChan availableInstances)
    orchestrate' <- toIO $ orchestrate taskQueue availableInstances 0
    orchestrateId <- liftIO $ forkIO orchestrate'

    -- run continuation with task queue
    res <- cont (SolverGroup taskQueue)

    -- cleanup and return results
    liftIO $ mapM_ (stopSolver) instances
    liftIO $ killThread orchestrateId
    pure res
  where
    orchestrate :: App m => Chan Task -> Chan SolverInstance -> Int -> m b
    orchestrate queue avail fileCounter = do
      task <- liftIO $ readChan queue
      inst <- liftIO $ readChan avail
      runTask' <- toIO $ runTask task inst avail fileCounter
      _ <- liftIO $ forkIO runTask'
      orchestrate queue avail (fileCounter + 1)

    runTask :: (MonadIO m, ReadConfig m) => Task -> SolverInstance -> Chan SolverInstance -> Int -> m ()
    runTask (Task smt2@(SMT2 cmds (RefinementEqs refineEqs refps) cexvars ps) r) inst availableInstances fileCounter = do
      conf <- readConfig
      let fuzzResult = tryCexFuzz ps conf.numCexFuzz
      liftIO $ do
        when (conf.dumpQueries) $ writeSMT2File smt2 fileCounter "abstracted"
        if (isJust fuzzResult)
          then do
            when (conf.debug) $ putStrLn $ "Cex found via fuzzing:" <> (show fuzzResult)
            writeChan r (Sat $ fromJust fuzzResult)
          else if not conf.onlyCexFuzz then do
            when (conf.debug) $ putStrLn "Fuzzing failed to find a Cex"
            -- reset solver and send all lines of provided script
            out <- sendScript inst (SMT2 ("(reset)" : cmds) mempty mempty ps)
            case out of
              -- if we got an error then return it
              Left e -> writeChan r (Error ("error while writing SMT to solver: " <> T.toStrict e))
              -- otherwise call (check-sat), parse the result, and send it down the result channel
              Right () -> do
                sat <- sendLine inst "(check-sat)"
                res <- do
                    case sat of
                      "unsat" -> pure Unsat
                      "timeout" -> pure Unknown
                      "unknown" -> pure Unknown
                      "sat" -> if null refineEqs then Sat <$> getModel inst cexvars
                               else do
                                    let refinedSMT2 = SMT2 refineEqs mempty mempty (ps <> refps)
                                    writeSMT2File refinedSMT2 fileCounter "refined"
                                    _ <- sendScript inst refinedSMT2
                                    sat2 <- sendLine inst "(check-sat)"
                                    case sat2 of
                                      "unsat" -> pure Unsat
                                      "timeout" -> pure Unknown
                                      "unknown" -> pure Unknown
                                      "sat" -> Sat <$> getModel inst cexvars
                                      _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat2
                      _ -> pure . Error $ T.toStrict $ "Unable to parse solver output: " <> sat
                writeChan r res
          else do
            when (conf.debug) $ putStrLn "Fuzzing failed to find a Cex, not trying SMT due to onlyCexFuzz"
            writeChan r Unknown

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
      addrs <- getAddrs parseEAddr (getValue inst) (fmap T.toStrict cexvars.addrs)
      buffers <- getBufs (getValue inst) (Map.keys cexvars.buffers)
      storage <- getStore (getValue inst) cexvars.storeReads
      blockctx <- getVars parseBlockCtx (getValue inst) (fmap T.toStrict cexvars.blockContext)
      txctx <- getVars parseTxCtx (getValue inst) (fmap T.toStrict cexvars.txContext)
      pure $ SMTCex vars addrs buffers storage blockctx txctx

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
                       (internalError $ "Could not find hint for buffer: " <> T.unpack name)
                       (Map.lookup name hints)
          shrinkBuf name hint
        _ -> internalError "Received model from solver for non AbstractBuf"

    -- starting with some guess at the max useful size for a buffer, cap
    -- it's size to that value, and ask the solver to check satisfiability. If
    -- it's still sat with the new constraint, leave that constraint on the
    -- stack and return a new model, if it's unsat, double the size of the hint
    -- and try again.
    shrinkBuf :: Text -> W256 -> StateT SMTCex IO ()
    shrinkBuf buf hint = do
      let encBound = "(_ bv" <> (T.pack $ show (into hint :: Integer)) <> " 256)"
      sat <- liftIO $ do
        checkCommand inst "(push 1)"
        checkCommand inst $ "(assert (bvule " <> buf <> "_length " <> encBound <> "))"
        sendLine inst "(check-sat)"
      case sat of
        "sat" -> do
          model <- liftIO getRaw
          put model
        "unsat" -> do
          liftIO $ checkCommand inst "(pop 1)"
          shrinkBuf buf (if hint == 0 then hint + 1 else hint * 2)
        e -> internalError $ "Unexpected solver output: " <> (T.unpack e)

    -- Collapses the abstract description of a models buffers down to a bytestring
    mkConcrete :: SMTCex -> SMTCex
    mkConcrete c = fromMaybe
      (internalError $ "counterexample contains buffers that are too large to be represented as a ByteString: " <> show c)
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

-- | Arguments used when spawning a solver instance
solverArgs :: Solver -> Maybe Natural -> [Text]
solverArgs solver timeout = case solver of
  Bitwuzla ->
    [ "--lang=smt2"
    , "--produce-models"
    , "--time-limit-per=" <> mkTimeout timeout
    , "--bv-solver=preprop"
    ]
  Z3 ->
    [ "-in" ]
  CVC5 ->
    [ "--lang=smt"
    , "--produce-models"
    , "--print-success"
    , "--interactive"
    , "--incremental"
    , "--tlimit-per=" <> mkTimeout timeout
    ]
  Custom _ -> []

-- | Spawns a solver instance, and sets the various global config options that we use for our queries
spawnSolver :: Solver -> Maybe (Natural) -> IO SolverInstance
spawnSolver solver timeout = do
  (readout, writeout) <- createPipe
  let cmd
        = (proc (show solver) (fmap T.unpack $ solverArgs solver timeout))
            { std_in = CreatePipe
            , std_out = UseHandle writeout
            , std_err = UseHandle writeout
            }
  (Just stdin, Nothing, Nothing, process) <- createProcess cmd
  hSetBuffering stdin (BlockBuffering (Just 1000000))
  let solverInstance = SolverInstance solver stdin readout process

  case solver of
    CVC5 -> pure solverInstance
    Bitwuzla -> do
      _ <- sendLine solverInstance "(set-option :print-success true)"
      pure solverInstance
    Z3 -> do
      _ <- sendLine' solverInstance $ "(set-option :timeout " <> mkTimeout timeout <> ")"
      _ <- sendLine solverInstance "(set-option :print-success true)"
      pure solverInstance
    Custom _ -> pure solverInstance

-- | Cleanly shutdown a running solver instance
stopSolver :: SolverInstance -> IO ()
stopSolver (SolverInstance _ stdin stdout process) = cleanupProcess (Just stdin, Just stdout, Nothing, process)

-- | Sends a list of commands to the solver. Returns the first error, if there was one.
sendScript :: SolverInstance -> SMT2 -> IO (Either Text ())
sendScript solver (SMT2 cmds _ _ _) = do
  let sexprs = splitSExpr $ fmap toLazyText cmds
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
    _ -> internalError $ "Unexpected solver output: " <> T.unpack res

-- | Sends a single command to the solver, returns the first available line from the output buffer
sendCommand :: SolverInstance -> Text -> IO Text
sendCommand inst cmd = do
  -- trim leading whitespace
  let cmd' = T.dropWhile isSpace cmd
  case T.unpack cmd' of
    "" -> pure "success"      -- ignore blank lines
    ';' : _ -> pure "success" -- ignore comments
    _ -> sendLine inst cmd'

-- | Strips trailing \r, if present
stripCarriageReturn :: Text -> Text
stripCarriageReturn t = fromMaybe t $ T.stripSuffix "\r" t

-- | Sends a string to the solver and appends a newline, returns the first available line from the output buffer
sendLine :: SolverInstance -> Text -> IO Text
sendLine (SolverInstance _ stdin stdout _) cmd = do
  T.hPutStrLn stdin cmd
  hFlush stdin
  stripCarriageReturn <$> (T.hGetLine stdout)

-- | Sends a string to the solver and appends a newline, doesn't return stdout
sendLine' :: SolverInstance -> Text -> IO ()
sendLine' (SolverInstance _ stdin _ _) cmd = do
  T.hPutStrLn stdin cmd
  hFlush stdin

-- | Returns a string representation of the model for the requested variable
getValue :: SolverInstance -> Text -> IO Text
getValue (SolverInstance _ stdin stdout _) var = do
  T.hPutStrLn stdin (T.append (T.append "(get-value (" var) "))")
  hFlush stdin
  fmap (T.unlines . reverse) (readSExpr stdout)

-- | Reads lines from h until we have a balanced sexpr
readSExpr :: Handle -> IO [Text]
readSExpr h = go 0 0 []
  where
    go 0 0 _ = do
      line <- T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls = T.length $ T.filter (== '(') cleanLine
          rs = T.length $ T.filter (== ')') cleanLine
      if ls == rs
         then pure [cleanLine]
         else go ls rs [cleanLine]
    go ls rs prev = do
      line <- T.hGetLine h
      let cleanLine = stripCarriageReturn line
          ls' = T.length $ T.filter (== '(') cleanLine
          rs' = T.length $ T.filter (== ')') cleanLine
      if (ls + ls') == (rs + rs')
         then pure $ cleanLine : prev
         else go (ls + ls') (rs + rs') (cleanLine : prev)

-- From a list of lines, take each separate SExpression and put it in
-- its own list, after removing comments.
splitSExpr :: [Text] -> [Text]
splitSExpr ls =
  -- split lines, strip comments, and append everything to a single line
  let text = T.intercalate " " $ T.takeWhile (/= ';') <$> concatMap T.lines ls in
  filter (/= "") $ go text []
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
    go _ _ r _ | r < 0 = internalError "Unbalanced SExpression"
    go _ "" _ _  = internalError "Unbalanced SExpression"
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
