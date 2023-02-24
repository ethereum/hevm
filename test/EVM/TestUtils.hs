{-# LANGUAGE QuasiQuotes #-}

module EVM.TestUtils where

import Data.String.Here
import Data.Text
import Data.Text qualified as T
import Data.Text.IO qualified as T
import EVM.Dapp
import EVM.Fetch (RpcInfo)
import EVM.Solidity
import EVM.Solvers
import EVM.TTY qualified as TTY
import EVM.UnitTest
import GHC.IO.Handle (hClose)
import Paths_hevm qualified as Paths
import System.Directory
import System.IO.Temp
import System.Process (readProcess)


runDappTestCustom :: FilePath -> Text -> Maybe Integer -> Bool -> RpcInfo -> IO Bool
runDappTestCustom testFile match maxIter ffiAllowed rpcinfo = do
  root <- Paths.getDataDir
  (json, _) <- compileWithDSTest testFile
  -- T.writeFile "output.json" json
  withCurrentDirectory root $ do
    withSystemTempFile "output.json" $ \file handle -> do
      hClose handle
      T.writeFile file json
      withSolvers Z3 1 Nothing $ \solvers -> do
        opts <- testOpts solvers root json match maxIter ffiAllowed rpcinfo
        dappTest opts file Nothing


runDappTest :: FilePath -> Text -> IO Bool
runDappTest testFile match = runDappTestCustom testFile match Nothing True Nothing


debugDappTest :: FilePath -> RpcInfo -> IO ()
debugDappTest testFile rpcinfo = do
  root <- Paths.getDataDir
  (json, _) <- compileWithDSTest testFile
  -- TIO.writeFile "output.json" json
  withCurrentDirectory root $ do
    withSystemTempFile "output.json" $ \file handle -> do
      hClose handle
      T.writeFile file json
      withSolvers Z3 1 Nothing $ \solvers -> do
        opts <- testOpts solvers root json ".*" Nothing True rpcinfo
        TTY.main opts root file


testOpts :: SolverGroup -> FilePath -> Text -> Text -> Maybe Integer -> Bool -> RpcInfo -> IO UnitTestOptions
testOpts solvers root solcJson match maxIter allowFFI rpcinfo = do
  srcInfo <- case readJSON solcJson of
    Nothing -> error "Could not read solc json"
    Just (contractMap, asts, sources) -> do
      sourceCache <- makeSourceCache sources asts
      pure $ dappInfo root contractMap sourceCache

  params <- getParametersFromEnvironmentVariables Nothing

  pure
    UnitTestOptions
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


compileWithDSTest :: FilePath -> IO (Text, Text)
compileWithDSTest src =
  withSystemTempFile "input.json" $ \file handle -> do
    hClose handle
    dsTest <- readFile =<< Paths.getDataFileName "test/contracts/lib/test.sol"
    erc20 <- readFile =<< Paths.getDataFileName "test/contracts/lib/erc20.sol"
    testFilePath <- Paths.getDataFileName src
    testFile <- readFile testFilePath
    T.writeFile
      file
      [i|
      {
        "language": "Solidity",
        "sources": {
          "ds-test/test.sol": {
            "content": ${dsTest}
          },
          "lib/erc20.sol": {
            "content": ${erc20}
          },
          "test.sol": {
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
    x <-
      T.pack
        <$> readProcess
          "solc"
          ["--allow-paths", file, "--standard-json", file]
          ""
    return (x, T.pack testFilePath)
