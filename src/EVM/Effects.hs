{-# Language RankNTypes #-}
{-# Language FlexibleInstances #-}
{-# Language KindSignatures #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language DerivingStrategies #-}
{-# Language DuplicateRecordFields #-}
{-# Language NoFieldSelectors #-}

module EVM.Effects where

import Control.Monad.Reader
import Control.Monad.IO.Unlift
import EVM.Dapp (DappInfo)
import EVM.Types (VM(..))
import Control.Monad.ST (RealWorld)
import Data.Text.IO as T
import EVM.Format (showTraceTree)
import EVM (traceForest)

-- Abstract Effects --------------------------------------------------------------------------------
-- Here we define the abstract interface for the effects that we wish to model

-- This is a concrete datatype that contains handlers for the above effects inside the IO monad.
data Config = Config
  { dumpQueries     :: Bool
  , dumpExprs       :: Bool
  , dumpEndStates   :: Bool
  , verbose         :: Bool
  , abstRefineArith :: Bool
  , abstRefineMem   :: Bool
  , dumpTrace       :: Bool
  }
  deriving (Show, Eq)

defaultConfig :: Config
defaultConfig = Config {
  dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , verbose = False
  , abstRefineArith = False
  , abstRefineMem   = False
  , dumpTrace = False
  }

writeTraceDapp
  :: (MonadUnliftIO m, ReadConfig m)
  => DappInfo -> VM RealWorld -> m ()
writeTraceDapp dapp vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ T.writeFile "VM.trace" (showTraceTree dapp vm)

writeTrace
  :: (MonadUnliftIO m, ReadConfig m)
  => VM RealWorld -> m ()
writeTrace vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ Prelude.writeFile "VM.trace" (show $ traceForest vm)


data Env = Env
  { config :: Config
  }

-- forall {r} {m :: Type -> Type} {a}. r -> ReaderT r m a -> m a
runEnv :: Env -> ReaderT Env m a -> m a
runEnv e a = runReaderT a e

class Monad m => ReadConfig m where
  readConfig ::  m Config

instance Monad m => ReadConfig (ReaderT Env m) where
  readConfig = do
    e <- ask
    pure e.config
