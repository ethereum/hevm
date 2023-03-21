module EVM.TestUtils where

import Data.Text
import qualified Paths_hevm as Paths
import System.Directory
import System.IO.Temp
import System.Process
import System.Exit

import EVM.Solidity
import EVM.Solvers
import EVM.Dapp
import EVM.UnitTest
import EVM.Fetch (RpcInfo)
import qualified EVM.TTY as TTY

runDappTestCustom :: FilePath -> Text -> Maybe Integer -> Bool -> RpcInfo -> ProjectType -> IO Bool
runDappTestCustom testFile match maxIter ffiAllowed rpcinfo projectType = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    withCurrentDirectory root $ do
      compile projectType root testFile >>= \case
        Left e -> error e
        Right bo@(BuildOutput contracts _) -> do
          withSolvers Z3 1 Nothing $ \solvers -> do
            opts <- testOpts solvers root (Just bo) match maxIter ffiAllowed rpcinfo
            unitTest opts contracts Nothing

runDappTest :: FilePath -> Text -> IO Bool
runDappTest testFile match = runDappTestCustom testFile match Nothing True Nothing Foundry

debugDappTest :: FilePath -> RpcInfo -> IO ()
debugDappTest testFile rpcinfo = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    withCurrentDirectory root $ do
      compile DappTools root testFile >>= \case
        Left e -> error e
        Right bo -> do
          withSolvers Z3 1 Nothing $ \solvers -> do
            opts <- testOpts solvers root (Just bo) ".*" Nothing True rpcinfo
            TTY.main opts root (Just bo)

testOpts :: SolverGroup -> FilePath -> Maybe BuildOutput -> Text -> Maybe Integer -> Bool -> RpcInfo -> IO UnitTestOptions
testOpts solvers root buildOutput match maxIter allowFFI rpcinfo = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput

  params <- getParametersFromEnvironmentVariables Nothing

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , askSmtIters = Nothing
    , smtDebug = False
    , smtTimeout = Nothing
    , solver = Nothing
    , covMatch = Nothing
    , verbose = Just 1
    , match = match
    , maxDepth = Nothing
    , fuzzRuns = 100
    , replay = Nothing
    , vmModifier = id
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = allowFFI
    }

tool :: ProjectType -> String
tool = \case
  Foundry -> "forge"
  DappTools -> "dapp"

compile :: ProjectType -> FilePath -> FilePath -> IO (Either String BuildOutput)
compile projType root src = do
  createDirectory (root <> "/src")
  writeFile (root <> "/src/unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
  initLib (root <> "/lib/ds-test") "test/contracts/lib/test.sol" "test.sol"
  initLib (root <> "/lib/tokens") "test/contracts/lib/erc20.sol" "erc20.sol"
  withCurrentDirectory root $ do
    r@(res,_,_) <- readProcessWithExitCode (tool projType) ["build"] ""
    case res of
      ExitFailure _ -> pure . Left $ "compilation failed: " <> show r
      ExitSuccess -> readBuildOutput root projType
  where
    initLib :: FilePath -> FilePath -> FilePath -> IO ()
    initLib tld srcFile dstFile = do
      createDirectoryIfMissing True (tld <> "/src")
      writeFile (tld <> "/src/" <> dstFile) =<< readFile =<< Paths.getDataFileName srcFile
      withCurrentDirectory tld $ do
        _ <- readProcessWithExitCode "git" ["init"] ""
        callProcess "git" ["config", "commit.gpgsign", "false"]
        callProcess "git" ["config", "user.name", "'hevm'"]
        callProcess "git" ["config", "user.email", "'hevm@hevm.dev'"]
        callProcess "git" ["add", "."]
        _ <- readProcessWithExitCode "git" ["commit", "-am"] ""
        pure ()
