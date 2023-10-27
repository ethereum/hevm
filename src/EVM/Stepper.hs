{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}



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
import Control.Monad.IO.Class
import EVM.Effects

-- | The instruction type of the operational monad
data Action s a where

  -- | Keep executing until an intermediate result is reached
  Exec :: Action s (VMResult s)

  -- | Wait for a query to be resolved
  Wait :: Query s -> Action s ()

  -- | Multiple things can happen
  Ask :: Choose s -> Action s ()

  -- | Embed a VM state transformation
  EVM  :: EVM s a -> Action s a

  -- | Perform an IO action
  IOAct :: IO a -> Action s a

-- | Type alias for an operational monad of @Action@
type Stepper s a = Program (Action s) a

-- Singleton actions

exec :: Stepper s (VMResult s)
exec = singleton Exec

run :: Stepper s (VM s)
run = exec >> evm get

wait :: Query s -> Stepper s ()
wait = singleton . Wait

ask :: Choose s -> Stepper s ()
ask = singleton . Ask

evm :: EVM s a -> Stepper s a
evm = singleton . EVM

evmIO :: IO a -> Stepper s a
evmIO = singleton . IOAct

-- | Run the VM until final result, resolving all queries
execFully :: Stepper s (Either EvmError (Expr Buf))
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
runFully :: Stepper s (VM s)
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

enter :: Text -> Stepper s ()
enter t = evm (EVM.pushTrace (EntryTrace t))

interpret :: forall m a . (App m) => Fetch.Fetcher m RealWorld -> VM RealWorld -> Stepper RealWorld a -> m a
interpret fetcher vm = eval . view
  where
    eval :: ProgramView (Action RealWorld) a -> m a
    eval (Return x) = pure x
    eval (action :>>= k) =
      case action of
        Exec -> do
          (r, vm') <- liftIO $ stToIO $ runStateT EVM.Exec.exec vm
          interpret fetcher vm' (k r)
        Wait (PleaseAskSMT (Lit c) _ continue) -> do
          (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case (c > 0))) vm
          interpret fetcher vm' (k r)
        Wait (PleaseAskSMT c _ _) ->
          error $ "cannot handle symbolic branch conditions in this interpreter: " <> show c
        Wait q -> do
          m <- fetcher q
          vm' <- liftIO $ stToIO $ execStateT m vm
          interpret fetcher vm' (k ())
        Ask _ ->
          internalError "cannot make choices with this interpreter"
        IOAct m -> do
          r <- liftIO $ m
          interpret fetcher vm (k r)
        EVM m -> do
          (r, vm') <- liftIO $ stToIO $ runStateT m vm
          interpret fetcher vm' (k r)
