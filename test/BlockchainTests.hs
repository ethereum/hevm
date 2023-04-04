module Main where

import EVM.Test.BlockchainTests
import Test.Tasty

main :: IO ()
main = do
  tests <- prepareTests
  defaultMain tests
