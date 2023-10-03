{-# LANGUAGE DataKinds #-}

module EVM.Stepper
  ( Action (..)
  , Stepper
  , exec
  , execFully
  , run
  , runFully
  , wait
  , ask
  , evm
  , evmIO
  , enter
  , interpret
  )
where

-- This module is an abstract definition of EVM steppers.
-- Steppers can be run as TTY debuggers or as CLI test runners.
--
-- The implementation uses the operational monad pattern
-- as the framework for monadic interpretation.

import Control.Monad.Operational (Program, ProgramViewT(..), ProgramView, singleton, view)
import Control.Monad.State.Strict (execStateT, runStateT, get)
import Data.Text (Text)

import EVM qualified
import EVM.Exec qualified
import EVM.Fetch qualified as Fetch
import EVM.Types
import Control.Monad.ST (stToIO, RealWorld)

-- | The instruction type of the operational monad
data Action gas s a where

  -- | Keep executing until an intermediate result is reached
  Exec :: Action gas s (VMResult gas s)

  -- | Wait for a query to be resolved
  Wait :: Query gas s -> Action gas s ()

  -- | Multiple things can happen
  Ask :: Choose gas s -> Action gas s ()

  -- | Embed a VM state transformation
  EVM  :: EVM gas s a -> Action gas s a

  -- | Perform an IO action
  IOAct :: IO a -> Action gas s a

-- | Type alias for an operational monad of @Action@
type Stepper gas s a = Program (Action gas s) a

-- Singleton actions

exec :: Stepper gas s (VMResult gas s)
exec = singleton Exec

run :: Stepper gas s (VM gas s)
run = exec >> evm get

wait :: Query gas s -> Stepper gas s ()
wait = singleton . Wait

ask :: Choose gas s -> Stepper gas s ()
ask = singleton . Ask

evm :: EVM gas s a -> Stepper gas s a
evm = singleton . EVM

evmIO :: IO a -> Stepper gas s a
evmIO = singleton . IOAct

-- | Run the VM until final result, resolving all queries
execFully :: Stepper gas s (Either EvmError (Expr Buf))
execFully =
  exec >>= \case
    HandleEffect (Query q) ->
      wait q >> execFully
    HandleEffect (Choose q) ->
      ask q >> execFully
    VMFailure x ->
      pure (Left x)
    VMSuccess x ->
      pure (Right x)
    Unfinished x
      -> internalError $ "partial execution encountered during concrete execution: " <> show x

-- | Run the VM until its final state
runFully :: Stepper gas s (VM gas s)
runFully = do
  vm <- run
  case vm.result of
    Nothing -> internalError "should not occur"
    Just (HandleEffect (Query q)) ->
      wait q >> runFully
    Just (HandleEffect (Choose q)) ->
      ask q >> runFully
    Just _ ->
      pure vm

enter :: Text -> Stepper gas s ()
enter t = evm (EVM.pushTrace (EntryTrace t))

interpret
  :: forall gas a
   . EVM.Gas gas
  => Fetch.Fetcher gas RealWorld
  -> VM gas RealWorld
  -> Stepper gas RealWorld a
  -> IO a
interpret fetcher vm = eval . view
  where
    eval :: ProgramView (Action gas RealWorld) a -> IO a
    eval (Return x) = pure x
    eval (action :>>= k) =
      case action of
        Exec -> do
          (r, vm') <- stToIO $ runStateT EVM.Exec.exec vm
          interpret fetcher vm' (k r)
        Wait (PleaseAskSMT (Lit c) _ continue) -> do
          (r, vm') <- stToIO $ runStateT (continue (Case (c > 0))) vm
          interpret fetcher vm' (k r)
        Wait (PleaseAskSMT c _ _) ->
          internalError $ "cannot handle symbolic branch conditions in this interpreter: " <> show c
        Wait q -> do
          m <- fetcher q
          vm' <- stToIO $ execStateT m vm
          interpret fetcher vm' (k ())
        Ask _ ->
          internalError "cannot make choices with this interpreter"
        IOAct m -> do
          r <- m
          interpret fetcher vm (k r)
        EVM m -> do
          (r, vm') <- stToIO $ runStateT m vm
          interpret fetcher vm' (k r)
