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
  , entering
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
import Control.Monad.State.Strict (execState, runState)
import Data.Text (Text)

import EVM qualified
import EVM.Exec qualified
import EVM.Fetch qualified as Fetch
import EVM.Types

-- | The instruction type of the operational monad
data Action a where

  -- | Keep executing until an intermediate result is reached
  Exec :: Action VMResult

  -- | Keep executing until an intermediate state is reached
  Run :: Action VM

  -- | Wait for a query to be resolved
  Wait :: Query -> Action ()

  -- | Multiple things can happen
  Ask :: Choose -> Action ()

  -- | Embed a VM state transformation
  EVM  :: EVM a -> Action a

  -- | Perform an IO action
  IOAct :: IO a -> Action a

-- | Type alias for an operational monad of @Action@
type Stepper a = Program Action a

-- Singleton actions

exec :: Stepper VMResult
exec = singleton Exec

run :: Stepper VM
run = singleton Run

wait :: Query -> Stepper ()
wait = singleton . Wait

ask :: Choose -> Stepper ()
ask = singleton . Ask

evm :: EVM a -> Stepper a
evm = singleton . EVM

evmIO :: IO a -> Stepper a
evmIO = singleton . IOAct

-- | Run the VM until final result, resolving all queries
execFully :: Stepper (Either EvmError (Expr Buf))
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
runFully :: Stepper VM
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

entering :: Text -> Stepper a -> Stepper a
entering t stepper = do
  evm (EVM.pushTrace (EntryTrace t))
  x <- stepper
  evm EVM.popTrace
  pure x

enter :: Text -> Stepper ()
enter t = evm (EVM.pushTrace (EntryTrace t))

interpret :: Fetch.Fetcher -> VM -> Stepper a -> IO a
interpret fetcher vm = eval . view
  where
    eval :: ProgramView Action a -> IO a
    eval (Return x) = pure x
    eval (action :>>= k) =
      case action of
        Exec ->
          let (r, vm') = runState EVM.Exec.exec vm
          in interpret fetcher vm' (k r)
        Run ->
          let vm' = execState EVM.Exec.run vm
          in interpret fetcher vm' (k vm')
        Wait (PleaseAskSMT (Lit c) _ continue) ->
          let (r, vm') = runState (continue (Case (c > 0))) vm
          in interpret fetcher vm' (k r)
        Wait (PleaseAskSMT c _ _) ->
          error $ "cannot handle symbolic branch conditions in this interpreter: " <> show c
        Wait q -> do
          m <- fetcher q
          let vm' = execState m vm
          interpret fetcher vm' (k ())
        Ask _ ->
          internalError "cannot make choices with this interpreter"
        IOAct m -> do
          r <- m
          interpret fetcher vm (k r)
        EVM m ->
          let (r, vm') = runState m vm
          in interpret fetcher vm' (k r)
