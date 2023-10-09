module Main where

import EVM.Test.BlockchainTests qualified  as BlockchainTests
import Test.Tasty
import EVM.Effects

testEnv :: Env
testEnv = Env { config = Config { dumpQueries = False } }

main :: IO ()
main = do
  tests <- runEnv testEnv BlockchainTests.prepareTests
  defaultMain tests
