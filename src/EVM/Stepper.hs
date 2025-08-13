{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}

module EVM.Stepper
  ( Action (..)
  , Stepper
  , exec
  , execFully
  , run
  , runFully
  , wait
  , fork
  , evm
  , enter
  , interpret
  , interpretWithTrace
  , execWithTrace
  , vmtrace
  , VMTrace (..)
  )
where

-- This module is an abstract definition of EVM steppers.
-- Steppers can be run as TTY debuggers or as CLI test runners.
--
-- The implementation uses the operational monad pattern
-- as the framework for monadic interpretation.

import Optics.Core
import Optics.State

import Control.Monad.IO.Class
import Control.Monad.Operational (Program, ProgramViewT(..), ProgramView, singleton)
import Control.Monad.ST (stToIO, RealWorld)
import Control.Monad.State.Strict (execStateT, get)
import Data.Text (Text)
import Data.Word (Word8, Word64)
import GHC.Generics (Generic)
import Control.Monad.State.Strict (StateT(..))
import Control.Monad.Operational qualified as Operational
import Control.Monad.Reader (lift)
import Control.Monad.State.Strict qualified as State
import Data.Maybe (fromJust)
import EVM (exec1)
import EVM.Op (intToOpName)
import Witch (into)
import Data.ByteString qualified as BS


import EVM qualified
import EVM.Effects
import EVM.Exec qualified
import EVM.Fetch qualified as Fetch
import EVM.Types

-- | The instruction type of the operational monad
data Action t s a where
  -- | Keep executing until an intermediate result is reached
  Exec :: Action t s (VMResult t s)
  -- | Embed a VM state transformation
  EVM  :: EVM t s a -> Action t s a
  -- | Wait for a query to be resolved
  Wait :: Query t s -> Action t s ()
  -- | Two things can happen
  Fork :: RunBoth s -> Action Symbolic s ()
  -- | Many (>2) things can happen
  ForkMany :: RunAll s -> Action Symbolic s ()

-- | Type alias for an operational monad of @Action@
type Stepper t s a = Program (Action t s) a

-- Singleton actions

exec :: Stepper t s (VMResult t s)
exec = singleton Exec

run :: Stepper t s (VM t s)
run = exec >> evm get

wait :: Query t s -> Stepper t s ()
wait = singleton . Wait

fork :: RunBoth s -> Stepper Symbolic s ()
fork = singleton . Fork

forkMany :: RunAll s -> Stepper Symbolic s ()
forkMany = singleton . ForkMany

evm :: EVM t s a -> Stepper t s a
evm = singleton . EVM

-- | Run the VM until final result, resolving all queries
execFully :: Stepper Concrete s (Either EvmError (Expr Buf))
execFully =
  exec >>= \case
    HandleEffect (Query q) ->
      wait q >> execFully
    VMFailure x ->
      pure (Left x)
    VMSuccess x ->
      pure (Right x)

-- | Run the VM until its final state
runFully :: Stepper t s (VM t s)
runFully = do
  vm <- run
  case vm.result of
    Nothing -> internalError "should not occur"
    Just (HandleEffect (Query q)) ->
      wait q >> runFully
    Just (HandleEffect (RunBoth q)) ->
      fork q >> runFully
    Just (HandleEffect (RunAll q)) ->
      forkMany q >> runFully
    Just _ ->
      pure vm

enter :: Text -> Stepper t s ()
enter t = evm (EVM.pushTrace (EntryTrace t))

interpret
  :: forall m a . (App m)
  => Fetch.Fetcher Concrete m RealWorld
  -> VM Concrete RealWorld
  -> Stepper Concrete RealWorld a
  -> m a
interpret fetcher vm = eval . Operational.view
  where
    eval :: ProgramView (Action Concrete RealWorld) a -> m a
    eval (Return x) = pure x
    eval (action :>>= k) =
      case action of
        Exec -> do
          conf <- readConfig
          (r, vm') <- liftIO $ stToIO $ runStateT (EVM.Exec.exec conf) vm
          interpret fetcher vm' (k r)
        Wait q -> do
          m <- fetcher q
          vm' <- liftIO $ stToIO $ execStateT m vm
          interpret fetcher vm' (k ())
        EVM m -> do
          (r, vm') <- liftIO $ stToIO $ runStateT m vm
          interpret fetcher vm' (k r)

data VMTrace =
  VMTrace
  { tracePc      :: Int
  , traceOp      :: Int
  , traceGas     :: Data.Word.Word64
  , traceMemSize :: Data.Word.Word64
  , traceDepth   :: Int
  , traceStack   :: [W256]
  , traceError   :: Maybe String
  } deriving (Generic)

instance Show VMTrace where
  show (VMTrace pc op gas memSize depth stack err) =
    "VMTrace { "
    ++ "tracePc = " ++ show pc
    ++ ", Op = " ++ show (intToOpName op)
    ++ ", Gas = " ++ show gas
    ++ ", MemSize = " ++ show memSize
    ++ ", Depth = " ++ show depth
    ++ ", Stack = " ++ show stack
    ++ ", Error = " ++ show err
    ++ " }"

type TraceState s = (VM Concrete s, [VMTrace])

execWithTrace :: App m => StateT (TraceState RealWorld) m (VMResult Concrete RealWorld)
execWithTrace = do
  _ <- runWithTrace
  fromJust <$> use (_1 % #result)

runWithTrace :: App m => StateT (TraceState RealWorld) m (VM Concrete RealWorld)
runWithTrace = do
  -- This is just like `exec` except for every instruction evaluated,
  -- we also increment a counter indexed by the current code location.
  conf <- lift readConfig
  vm0 <- use _1
  case vm0.result of
    Nothing -> do
      State.modify' (\(a, b) -> (a, b ++ [vmtrace vm0]))
      vm' <- liftIO $ stToIO $ State.execStateT (exec1 conf) vm0
      assign _1 vm'
      runWithTrace
    Just (VMFailure _) -> do
      -- Update error text for last trace element
      (a, b) <- State.get
      let updatedElem = (last b) {traceError = (vmtrace vm0).traceError}
          updatedTraces = take (length b - 1) b ++ [updatedElem]
      State.put (a, updatedTraces)
      pure vm0
    Just _ -> pure vm0

interpretWithTrace
  :: forall m a . App m
  => Fetch.Fetcher Concrete m RealWorld
  -> Stepper Concrete RealWorld a
  -> StateT (TraceState RealWorld) m a
interpretWithTrace fetcher =
  eval . Operational.view
  where
    eval
      :: App m
      => Operational.ProgramView (Action Concrete RealWorld) a
      -> StateT (TraceState RealWorld) m a
    eval (Operational.Return x) = pure x
    eval (action Operational.:>>= k) =
      case action of
        Exec ->
          execWithTrace >>= interpretWithTrace fetcher . k
        Wait q -> do
          m <- State.lift $ fetcher q
          vm <- use _1
          vm' <- liftIO $ stToIO $ State.execStateT m vm
          assign _1 vm'
          interpretWithTrace fetcher (k ())
        EVM m -> do
          vm <- use _1
          (r, vm') <- liftIO $ stToIO $ State.runStateT m vm
          assign _1 vm'
          interpretWithTrace fetcher (k r)

vmtrace :: VM Concrete s -> VMTrace
vmtrace vm =
  let
    memsize = vm.state.memorySize
  in VMTrace { tracePc = vm.state.pc
             , traceOp = into $ getOpFromVM vm
             , traceGas = vm.state.gas
             , traceMemSize = memsize
             -- increment to match geth format
             , traceDepth = 1 + length (vm.frames)
             -- reverse to match geth format
             , traceStack = reverse $ forceLit <$> vm.state.stack
             , traceError = readoutError vm.result
             }
  where
    readoutError :: Maybe (VMResult t s) -> Maybe String
    readoutError (Just (VMFailure e)) = Just $ evmErrToString e
    readoutError _ = Nothing

getOpFromVM :: VM t s -> Word8
getOpFromVM vm =
  let pcpos  = vm ^. #state % #pc
      code' = vm ^. #state % #code
      xs = case code' of
        UnknownCode _ -> internalError "UnknownCode instead of RuntimeCode"
        InitCode bs _ -> BS.drop pcpos bs
        RuntimeCode (ConcreteRuntimeCode xs') -> BS.drop pcpos xs'
        RuntimeCode (SymbolicRuntimeCode _) -> internalError "RuntimeCode is symbolic"
  in if xs == BS.empty then 0
                       else BS.head xs
