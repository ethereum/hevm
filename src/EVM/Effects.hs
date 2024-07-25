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

module EVM.Effects where

import Control.Monad (when)
import Control.Monad.IO.Unlift (MonadIO(liftIO), MonadUnliftIO)
import Control.Monad.Reader (ReaderT, runReaderT, ask)
import Control.Monad.ST (RealWorld)
import Data.Text (Text)
import Data.Text.IO qualified as T
import System.IO (stderr)

import EVM (traceForest)
import EVM.Dapp (DappInfo)
import EVM.Format (showTraceTree)
import EVM.Types (VM(..))


-- Abstract Effects --------------------------------------------------------------------------------
-- Here we define the abstract interface for the effects that we wish to model


-- Read from global config
class Monad m => ReadConfig m where
  readConfig ::  m Config

data Config = Config
  { dumpQueries      :: Bool
  , dumpExprs        :: Bool
  , dumpEndStates    :: Bool
  , debug            :: Bool
  , abstRefineArith  :: Bool
  , abstRefineMem    :: Bool
  , dumpTrace        :: Bool
  , numCexFuzz       :: Integer
   -- Used to debug fuzzer in test.hs. It disables the SMT solver
   -- and uses the fuzzer ONLY to try to find a counterexample.
   -- Returns Unknown if the Cex cannot be found via fuzzing
  , onlyCexFuzz      :: Bool
  , decomposeStorage :: Bool
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
  , numCexFuzz = 10
  , onlyCexFuzz  = False
  , decomposeStorage = True
  }

-- Write to the console
class Monad m => TTY m where
  writeOutput :: Text -> m ()
  writeErr :: Text -> m ()

writeTraceDapp :: App m => DappInfo -> VM t RealWorld -> m ()
writeTraceDapp dapp vm = do
  conf <- readConfig
  liftIO $ when conf.dumpTrace $ T.writeFile "VM.trace" (showTraceTree dapp vm)

writeTrace :: App m => VM t RealWorld -> m ()
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

instance (Monad m, MonadIO m) => TTY (ReaderT Env m) where
  writeOutput txt = liftIO $ T.putStrLn txt
  writeErr txt = liftIO $ T.hPutStr stderr txt

runEnv :: Env -> ReaderT Env m a -> m a
runEnv e a = runReaderT a e


-- Helpful Aliases ---------------------------------------------------------------------------------


type App m = (MonadUnliftIO m, ReadConfig m, TTY m)

runApp :: ReaderT Env m a -> m a
runApp = runEnv defaultEnv
