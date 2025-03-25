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
import Data.List.Split (splitOn)

main :: IO ()
main = do
  hspec $
    describe "CLI" $ do
      it "hevm exists" $ do
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm"] ""
        stderr `shouldContain` "Usage: hevm"

      it "hevm symbolic tutorial works -- FAIL" $ do
        let torun = splitOn " " "symbolic --sig simple_symb() --code 6080604052348015600e575f80fd5b50600436106026575f3560e01c8063881fc77c14602a575b5f80fd5b60306032565b005b5f805414604057603f6042565b5b565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52600160045260245ffdfea2646970667358221220cf838a7ff084e553805b9b56decd46ea37363e97e26405b2409d22cb905de0e664736f6c63430008180033"
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Discovered the following"
        exitCode `shouldBe` ExitFailure 1

      it "hevm equivalence tutorial works -- FAIL" $ do
        let torun = splitOn " " "equivalence --code-a 60003560000260005260016000f3 --code-b 7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260016000f3"
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Not equivalent"
        stdout `shouldContain` "FAIL"
        exitCode `shouldBe` ExitFailure 1

      it "hevm equivalence tutorial works -- PASS" $ do
        let a = "608060405234801561000f575f80fd5b5060043610610029575f3560e01c8063afc2c9491461002d575b5f80fd5b61004760048036038101906100429190610252565b610049565b005b6064815f808573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205461009391906102bd565b1061009c575f80fd5b6002816100a9919061031d565b5f808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205f8282546100f391906102bd565b92505081905550600281610107919061031d565b5f808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205f82825461015191906102bd565b925050819055505f600282610166919061034d565b146101bd575f808373ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205f8154809291906101b79061037d565b91905055505b5050565b5f80fd5b5f73ffffffffffffffffffffffffffffffffffffffff82169050919050565b5f6101ee826101c5565b9050919050565b6101fe816101e4565b8114610208575f80fd5b50565b5f81359050610219816101f5565b92915050565b5f819050919050565b6102318161021f565b811461023b575f80fd5b50565b5f8135905061024c81610228565b92915050565b5f8060408385031215610268576102676101c1565b5b5f6102758582860161020b565b92505060206102868582860161023e565b9150509250929050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601160045260245ffd5b5f6102c78261021f565b91506102d28361021f565b92508282019050808211156102ea576102e9610290565b5b92915050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601260045260245ffd5b5f6103278261021f565b91506103328361021f565b925082610342576103416102f0565b5b828204905092915050565b5f6103578261021f565b91506103628361021f565b925082610372576103716102f0565b5b828206905092915050565b5f6103878261021f565b91507fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff82036103b9576103b8610290565b5b60018201905091905056fea2646970667358221220372ec8252df2174861b11dd9a2e3a4ef42f4a324c96520aabd6bfa8d16a8391e64736f6c634300081a0033"
        let b = "608060405234801561000f575f80fd5b5060043610610029575f3560e01c8063afc2c9491461002d575b5f80fd5b61004760048036038101906100429190610183565b610049565b005b6064815f808573ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205461009391906101ee565b1061009c575f80fd5b805f808473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1681526020019081526020015f205f8282546100e791906101ee565b925050819055505050565b5f80fd5b5f73ffffffffffffffffffffffffffffffffffffffff82169050919050565b5f61011f826100f6565b9050919050565b61012f81610115565b8114610139575f80fd5b50565b5f8135905061014a81610126565b92915050565b5f819050919050565b61016281610150565b811461016c575f80fd5b50565b5f8135905061017d81610159565b92915050565b5f8060408385031215610199576101986100f2565b5b5f6101a68582860161013c565b92505060206101b78582860161016f565b9150509250929050565b7f4e487b71000000000000000000000000000000000000000000000000000000005f52601160045260245ffd5b5f6101f882610150565b915061020383610150565b925082820190508082111561021b5761021a6101c1565b5b9291505056fea2646970667358221220a9c263cc9bf4c539ec2bcf875f744e89f364ed1511c1e72f1aec6d7980169c5264736f6c634300081a0033"
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--", "equivalence" , "--code-a", a, "--code-b", b ]) ""
        stdout `shouldContain` "No discrepancies found"
        stdout `shouldContain` "PASS"
        exitCode `shouldBe` ExitSuccess
