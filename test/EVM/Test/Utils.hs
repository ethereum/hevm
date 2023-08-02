{-# LANGUAGE QuasiQuotes #-}

module EVM.Test.Utils where

import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import GHC.IO.Handle (hClose)
import GHC.Natural
import Paths_hevm qualified as Paths
import System.Directory
import System.IO.Temp
import System.Process
import System.Exit

import EVM.Dapp (dappInfo, emptyDapp)
import EVM.Fetch (RpcInfo)
import EVM.Solidity
import EVM.Solvers
import EVM.TTY qualified as TTY
import EVM.UnitTest
import Control.Monad.ST (RealWorld)

runSolidityTestCustom :: FilePath -> Text -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> ProjectType -> IO Bool
runSolidityTestCustom testFile match timeout maxIter ffiAllowed rpcinfo projectType = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    compile projectType root testFile >>= \case
      Left e -> error e
      Right bo@(BuildOutput contracts _) -> do
        withSolvers Z3 1 timeout $ \solvers -> do
          opts <- testOpts solvers root (Just bo) match maxIter ffiAllowed rpcinfo
          unitTest opts contracts Nothing

runSolidityTest :: FilePath -> Text -> IO Bool
runSolidityTest testFile match = runSolidityTestCustom testFile match Nothing Nothing True Nothing Foundry

debugSolidityTest :: FilePath -> RpcInfo -> IO ()
debugSolidityTest testFile rpcinfo = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    compile DappTools root testFile >>= \case
      Left e -> error e
      Right bo -> do
        withSolvers Z3 1 Nothing $ \solvers -> do
          opts <- testOpts solvers root (Just bo) ".*" Nothing True rpcinfo
          TTY.main opts root (Just bo)

testOpts :: SolverGroup -> FilePath -> Maybe BuildOutput -> Text -> Maybe Integer -> Bool -> RpcInfo -> IO (UnitTestOptions RealWorld)
testOpts solvers root buildOutput match maxIter allowFFI rpcinfo = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput

  params <- getParametersFromEnvironmentVariables Nothing

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , askSmtIters = 1
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

compile :: ProjectType -> FilePath -> FilePath -> IO (Either String BuildOutput)
compile DappTools root src = do
  json <- compileWithDSTest src
  createDirectory (root <> "/out")
  T.writeFile (root <> "/out/dapp.sol.json") json
  readBuildOutput root DappTools
compile CombinedJSON _root _src = error "unsupported"
compile Foundry root src = do
  createDirectory (root <> "/src")
  writeFile (root <> "/src/unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
  initLib (root <> "/lib/ds-test") "test/contracts/lib/test.sol" "test.sol"
  initLib (root <> "/lib/tokens") "test/contracts/lib/erc20.sol" "erc20.sol"
  r@(res,_,_) <- readProcessWithExitCode "forge" ["build", "--root", root] ""
  case res of
    ExitFailure _ -> pure . Left $ "compilation failed: " <> show r
    ExitSuccess -> readBuildOutput root Foundry
  where
    initLib :: FilePath -> FilePath -> FilePath -> IO ()
    initLib tld srcFile dstFile = do
      createDirectoryIfMissing True (tld <> "/src")
      writeFile (tld <> "/src/" <> dstFile) =<< readFile =<< Paths.getDataFileName srcFile
      _ <- readProcessWithExitCode "git" ["init", tld] ""
      callProcess "git" ["config", "--file", tld <> "/.git/config", "user.name", "'hevm'"]
      callProcess "git" ["config", "--file", tld <> "/.git/config", "user.email", "'hevm@hevm.dev'"]
      callProcess "git" ["--git-dir", tld <> "/.git", "--work-tree", tld, "add", tld]
      _ <- readProcessWithExitCode "git" ["--git-dir", tld <> "/.git", "--work-tree", tld, "--no-gpg-sign", "commit", "-m"] ""
      pure ()

-- We don't want to depend on dapptools here, so we cheat and just call solc with the same options that dapp itself uses
compileWithDSTest :: FilePath -> IO Text
compileWithDSTest src =
  withSystemTempFile "input.json" $ \file handle -> do
    hClose handle
    dsTest <- readFile =<< Paths.getDataFileName "test/contracts/lib/test.sol"
    erc20 <- readFile =<< Paths.getDataFileName "test/contracts/lib/erc20.sol"
    testFilePath <- Paths.getDataFileName src
    testFile <- readFile testFilePath
    T.writeFile file
      [i|
      {
        "language": "Solidity",
        "sources": {
          "ds-test/test.sol": {
            "content": ${dsTest}
          },
          "tokens/erc20.sol": {
            "content": ${erc20}
          },
          "unit-tests.sol": {
            "content": ${testFile}
          }
        },
        "settings": {
          "metadata": {
            "useLiteralContent": true
          },
          "outputSelection": {
            "*": {
              "*": [
                "metadata",
                "evm.bytecode",
                "evm.deployedBytecode",
                "abi",
                "storageLayout",
                "evm.bytecode.sourceMap",
                "evm.bytecode.linkReferences",
                "evm.bytecode.generatedSources",
                "evm.deployedBytecode.sourceMap",
                "evm.deployedBytecode.linkReferences",
                "evm.deployedBytecode.generatedSources"
              ],
              "": [
                "ast"
              ]
            }
          }
        }
      }
      |]
    x <- T.pack <$>
      readProcess
        "solc"
        ["--allow-paths", file, "--standard-json", file]
        ""
    return x

