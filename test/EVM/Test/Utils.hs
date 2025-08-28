module EVM.Test.Utils where

import Data.Text (Text)
import Data.List (isInfixOf)
import GHC.IO.Exception (IOErrorType(..))
import GHC.Natural
import Paths_hevm qualified as Paths
import System.Directory
import System.FilePath ((</>))
import System.IO.Temp
import System.Process
import System.Exit
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

-- Returns tuple of (No cex, No warnings)
runSolidityTestCustom
  :: (MonadMask m, App m)
  => FilePath -> Text -> Maybe Natural -> Maybe Integer -> Bool -> RpcInfo -> ProjectType -> m (Bool, Bool)
runSolidityTestCustom testFile match timeout maxIter ffiAllowed rpcinfo projectType = do
  withSystemTempDirectory "dapp-test" $ \root -> do
    compile projectType root testFile >>= \case
      Left e -> liftIO $ do
        putStrLn e
        internalError $ "Error compiling test file " <> show testFile <> " in directory "
          <> show root <> " using project type " <> show projectType
      Right bo@(BuildOutput contracts _) -> do
        withSolvers Bitwuzla 3 1 timeout $ \solvers -> do
          opts <- testOpts solvers root (Just bo) match maxIter ffiAllowed rpcinfo
          unitTest opts contracts

-- Returns tuple of (No cex, No warnings)
runSolidityTest
  :: (MonadMask m, App m)
  => FilePath -> Text -> m (Bool, Bool)
runSolidityTest testFile match = runSolidityTestCustom testFile match Nothing Nothing True mempty Foundry

testOpts :: App m => SolverGroup -> FilePath -> Maybe BuildOutput -> Text -> Maybe Integer -> Bool -> RpcInfo -> m (UnitTestOptions RealWorld)
testOpts solvers root buildOutput match maxIter allowFFI rpcinfo = do
  let srcInfo = maybe emptyDapp (dappInfo root) buildOutput
  params <- paramsFromRpc rpcinfo

  pure UnitTestOptions
    { solvers = solvers
    , rpcInfo = rpcinfo
    , maxIter = maxIter
    , askSmtIters = 1
    , smtTimeout = Nothing
    , match = match
    , prefix = "prove"
    , testParams = params
    , dapp = srcInfo
    , ffiAllowed = allowFFI
    , checkFailBit = False
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
      ExitSuccess   -> pure ()
      ExitFailure r -> processFailedException "callProcess" cmd args r

compile :: App m => ProjectType -> FilePath -> FilePath -> m (Either String BuildOutput)
compile CombinedJSON _root _src = internalError  "unsupported compile type: CombinedJSON"
compile _ root src = do
  liftIO $ createDirectory (root </> "src")
  liftIO $ writeFile (root </> "src" </> "unit-tests.t.sol") =<< readFile =<< Paths.getDataFileName src
  liftIO $ initLib (root </> "lib" </> "tokens") ("test" </> "contracts" </> "lib" </> "erc20.sol") "erc20.sol"
  liftIO $ initStdForgeDir (root </> "lib" </> "forge-std")
  (res,out,err) <- liftIO $ readProcessWithExitCode "forge" ["build", "--ast", "--root", root] ""
  case res of
    ExitFailure _ -> pure . Left $ "compilation failed: " <> "exit code: " <> show res <> "\n\nstdout:\n" <> out <> "\n\nstderr:\n" <> err
    ExitSuccess -> readFilteredBuildOutput root (\path -> "unit-tests.t.sol" `Data.List.isInfixOf` path) Foundry
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
      pure ()
