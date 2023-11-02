{-|
Module      : Effects
Description : Domain specific effects

This module contains custom app specific mtl style effects for hevm
These are written in the style of the ReaderT over IO pattern [1].
Right now we only have a single `ReadConfig` effect, but over time hope to
migrate most usages of IO into custom effects here.

This framework would allow us to have multiple interpretations for effects
(e.g. a pure version for tests), but for now we interpret everything in IO
only.

[1]: https://www.fpcomplete.com/blog/readert-design-pattern/
-}

{-# Language RankNTypes #-}
{-# Language FlexibleInstances #-}
{-# Language KindSignatures #-}
{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language DerivingStrategies #-}
{-# Language DuplicateRecordFields #-}
{-# Language NoFieldSelectors #-}
{-# Language ConstraintKinds #-}

module EVM.Effects where

import Control.Monad.Reader
import Control.Monad.IO.Unlift
import EVM.Dapp (DappInfo)
import EVM.Types (VM(..))
import Control.Monad.ST (RealWorld)
import Data.Text.IO qualified as T
import EVM.Format (showTraceTree)
import EVM (traceForest)

-- Abstract Effects --------------------------------------------------------------------------------
-- Here we define the abstract interface for the effects that we wish to model

-- Global config
class Monad m => ReadConfig m where
  readConfig ::  m Config

data Config = Config
  { dumpQueries     :: Bool
  , dumpExprs       :: Bool
  , dumpEndStates   :: Bool
  , debug           :: Bool
  , abstRefineArith :: Bool
  , abstRefineMem   :: Bool
  , dumpTrace       :: Bool
  }
  deriving (Show, Eq)

defaultConfig :: Config
defaultConfig = Config
  { dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , abstRefineArith = False
  , abstRefineMem   = False
  , dumpTrace = False
  }

writeTraceDapp :: App m => DappInfo -> VM RealWorld -> m ()
writeTraceDapp dapp vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ T.writeFile "VM.trace" (showTraceTree dapp vm)

writeTrace :: App m => VM RealWorld -> m ()
writeTrace vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ writeFile "VM.trace" (show $ traceForest vm)

-- IO Interpretation -------------------------------------------------------------------------------

newtype Env = Env
  { config :: Config
  }

defaultEnv :: Env
defaultEnv = Env { config = defaultConfig }

instance Monad m => ReadConfig (ReaderT Env m) where
  readConfig = do
    e <- ask
    pure e.config

runEnv :: Env -> ReaderT Env m a -> m a
runEnv e a = runReaderT a e

-- Helpful Aliases ---------------------------------------------------------------------------------

type App m = (MonadUnliftIO m, ReadConfig m)

runApp :: ReaderT Env m a -> m a
runApp = runEnv defaultEnv
