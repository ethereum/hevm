module Main where

{-|
Module      : CliSpec
Description : CLI tests

This module contains simple CLI test cases to make sure we don't accidentally
break the hevm CLI interface.

-}

import Test.Hspec
import System.Process (readProcess, readProcessWithExitCode)
import System.FilePath ((</>))
import System.Exit (ExitCode(..))

main :: IO ()
main = do
  hspec $
    describe "CLI" $ do
      it "hevm exists" $ do
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm"] ""
        stderr `shouldContain` "Usage: hevm"
