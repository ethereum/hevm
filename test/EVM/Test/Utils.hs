{-# LANGUAGE QuasiQuotes #-}

module EVM.Test.Utils where

import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import GHC.IO.Exception (IOErrorType(..))
import GHC.Natural
import Paths_hevm qualified as Paths
import System.Directory
import System.FilePath ((</>))
import System.IO.Temp
import System.Process
import System.Exit
import System.IO
import System.IO.Error (mkIOError)

import EVM.Dapp (dappInfo, emptyDapp)
import EVM.Fetch (RpcInfo)
import EVM.Solidity
import EVM.Solvers
import EVM.UnitTest
import Control.Monad.ST (RealWorld)
import Control.Monad.IO.Unlift
import Control.Monad.Catch (MonadMask)
import EVM.Effects
import Data.Maybe (fromMaybe)
import EVM.Types (internalError)
import System.Environment (lookupEnv)

runSolidityTestCustom
  :: (MonadMask m, App m)
  => FilePath -> Text -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> ProjectType -> m Bool
runSolidityTestCustom testFile match timeout maxIter ffiAllowed rpcinfo projectType = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    (compile projectType root testFile) >>= \case
      Left e -> error e
      Right bo@(BuildOutput contracts _) -> do
        withSolvers Z3 1 1 timeout $ \solvers -> do
          opts <- liftIO $ testOpts solvers root (Just bo) match maxIter ffiAllowed rpcinfo
          unitTest opts contracts

runSolidityTest
  :: (MonadMask m, App m)
  => FilePath -> Text -> m Bool
runSolidityTest testFile match = runSolidityTestCustom testFile match Nothing Nothing True Nothing Foundry

testOpts :: SolverGroup -> FilePath -> Maybe BuildOutput -> Text -> Maybe Integer -> Bool -> RpcInfo -> IO (UnitTestOptions RealWorld)
testOpts solvers root buildOutput match maxIter allowFFI rpcinfo = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput

  params <- paramsFromRpc rpcinfo

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , askSmtIters = 1
    , smtTimeout = Nothing
    , solver = Nothing
    , verbose = Just 1
    , match = match
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = allowFFI
    }

processFailedException :: String -> String -> [String] -> Int -> IO a
processFailedException fun cmd args exit_code =
      ioError (mkIOError OtherError (fun ++ ": " ++ cmd ++
                                     concatMap ((' ':) . show) args ++
                                     " (exit " ++ show exit_code ++ ")")
                                 Nothing Nothing)

callProcessCwd :: FilePath -> [String] -> FilePath -> IO ()
callProcessCwd cmd args cwd = do
    exit_code <- withCreateProcess (proc cmd args) { cwd = Just cwd, delegate_ctlc = True } $ \_ _ _ p ->
                 waitForProcess p
    case exit_code of
      ExitSuccess   -> return ()
      ExitFailure r -> processFailedException "callProcess" cmd args r

compile :: App m => ProjectType -> FilePath -> FilePath -> m (Either String BuildOutput)
compile DappTools root src = do
  json <- liftIO $ compileWithDSTest src
  liftIO $ createDirectory (root </> "out")
  liftIO $ T.writeFile (root </> "out" </> "dapp.sol.json") json
  readBuildOutput root DappTools
compile CombinedJSON _root _src = error "unsupported"
compile foundryType root src = do
  liftIO $ createDirectory (root </> "src")
  liftIO $ writeFile (root </> "src" </> "unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
  liftIO $ initLib (root </> "lib" </> "ds-test") ("test" </> "contracts" </> "lib" </> "test.sol") "test.sol"
  liftIO $ initLib (root </> "lib" </> "tokens") ("test" </> "contracts" </> "lib" </> "erc20.sol") "erc20.sol"
  case foundryType of
    FoundryStdLib -> liftIO $ initStdForgeDir (root </> "lib" </> "forge-std")
    Foundry -> pure ()
  (res,out,err) <- liftIO $ readProcessWithExitCode "forge" ["build", "--ast", "--root", root] ""
  case res of
    ExitFailure _ -> pure . Left $ "compilation failed: " <> "exit code: " <> show res <> "\n\nstdout:\n" <> out <> "\n\nstderr:\n" <> err
    ExitSuccess -> readBuildOutput root Foundry
  where
    initStdForgeDir :: FilePath -> IO ()
    initStdForgeDir tld = do
      createDirectoryIfMissing True tld
      forgeStdRepo <- liftIO $ fromMaybe (internalError "cannot find forge-std repo") <$> (lookupEnv "HEVM_FORGE_STD_REPO")
      callProcess "mkdir" ["-p", tld]
      callProcess "cp" ["-r", forgeStdRepo </> "src", tld </> "src"]
    initLib :: FilePath -> FilePath -> FilePath -> IO ()
    initLib tld srcFile dstFile = do
      createDirectoryIfMissing True (tld </> "src")
      writeFile (tld </> "src" </> dstFile) =<< readFile =<< Paths.getDataFileName srcFile
      _ <- readProcessWithExitCode "git" ["init", tld] ""
      callProcess "git" ["config", "--file", tld </> ".git" </> "config", "user.name", "'hevm'"]
      callProcess "git" ["config", "--file", tld </> ".git" </> "config", "user.email", "'hevm@hevm.dev'"]
      callProcessCwd "git" ["add", "."] tld
      callProcessCwd "git" ["commit", "-m", "", "--allow-empty-message", "--no-gpg-sign"] tld
      pure ()

-- We don't want to depend on dapptools here, so we cheat and just call solc with the same options that dapp itself uses
compileWithDSTest :: FilePath -> IO Text
compileWithDSTest src =
  withSystemTempFile "input.json" $ \file handle -> do
    hClose handle
    dsTest <- readFile =<< Paths.getDataFileName ("test" </> "contracts" </> "lib" </> "test.sol")
    erc20 <- readFile =<< Paths.getDataFileName ("test" </> "contracts" </> "lib" </> "erc20.sol")
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

