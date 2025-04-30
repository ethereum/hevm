{-# LANGUAGE QuasiQuotes #-}

module Main where

{-|
Description : CLI tests

This module contains simple CLI test cases to make sure we don't accidentally
break the hevm CLI interface.

-}

import Test.Hspec
import System.Process (readProcess, readProcessWithExitCode)
import System.FilePath ((</>))
import System.Exit (ExitCode(..))
import Data.List.Split (splitOn)
import Data.Text qualified as T
import Data.String.Here

import EVM.Solidity
import EVM.Effects
import EVM.Types


main :: IO ()
main = do
  hspec $
    describe "CLI" $ do
      it "hevm help works" $ do
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "--help"] ""
        stdout `shouldContain` "Usage: hevm"
        stdout `shouldContain` "test"
        stdout `shouldContain` "equivalence"
        stdout `shouldContain` "symbolic"
        stdout `shouldContain` "exec"
        stdout `shouldContain` "version"

      it "hevm symbolic tutorial works -- FAIL" $ do
        Just symbBin <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            function simple_symb() public pure {
              uint i;
              i = 1;
              assert(i == 2);
            }
          }
        |])
        let symbHex = bsToHex symbBin
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", symbHex] ""
        stdout `shouldContain` "Discovered the following"
        exitCode `shouldBe` ExitFailure 1

        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", symbHex, "--sig", "nonexistent()"] ""
        stdout `shouldContain` "QED"
        exitCode `shouldBe` ExitSuccess

      it "hevm equivalence tutorial works -- FAIL" $ do
        let torun = splitOn " " "equivalence --code-a 60003560000260005260016000f3 --code-b 7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff60005260016000f3"
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Not equivalent"
        stdout `shouldContain` "FAIL"
        exitCode `shouldBe` ExitFailure 1

      it "hevm equivalence tutorial works -- PASS" $ do
        Just a <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            mapping (address => uint) balances;
            function my_adder(address recv, uint amt) public {
              if (balances[recv] + amt >= 100) { revert(); }
              balances[recv] += amt;
            }
          }
        |])
        let aHex = bsToHex a
        Just b <- runApp $ solcRuntime (T.pack "MyContract") (T.pack [i|
          contract MyContract {
            mapping (address => uint) balances;
            function my_adder(address recv, uint amt) public {
              if (balances[recv] + amt >= 100) { revert(); }
              balances[recv] += amt/2;
              balances[recv] += amt/2;
              if (amt % 2 != 0) balances[recv]++;
            }
          }
        |])
        let bHex = bsToHex b
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--", "equivalence" , "--code-a", aHex, "--code-b", bHex ]) ""
        stdout `shouldContain` "No discrepancies found"
        stdout `shouldContain` "PASS"
        exitCode `shouldBe` ExitSuccess

      it "hevm concrete tutorial works" $ do
        let torun = splitOn " " "exec --code 0x647175696e6550383480393834f3 --gas 0xff"
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" (["run", "exe:hevm", "--" ] ++ torun) ""
        stdout `shouldContain` "Return: 0x64"
        exitCode `shouldBe` ExitSuccess

      it "warning on zero address" $ do
        Just c <- runApp $ solcRuntime (T.pack "C") (T.pack [i|
           contract Target {
             function get() external view returns (uint256) {
                 return 55;
             }
           }
           contract C {
             Target mm;
             function retFor() public returns (uint256) {
                 Target target = Target(address(0));
                 uint256 ret = target.get();
                 assert(ret == 4);
                 return ret;
             }
           }
          |])
        let hexStr = bsToHex c
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "symbolic", "--code", hexStr] ""
        stdout `shouldContain` "Warning: fetching contract at address 0"

      -- file "devcon_example.yul" from "eq-all-yul-optimization-tests" in test.hs
      -- we check that at least one UNSAT cache hit happens, i.e. the unsat cache is not
      -- completely broken
      it "unsat-cache" $ do
        let a = [i| {
          calldatacopy(0,0,1024)
              sstore(0, array_sum(calldataload(0)))
              function array_sum(x) -> sum {
                  let length := calldataload(x)
                  for { let i := 0 } lt(i, length) { i := add(i, 1) } {
                      sum := add(sum, array_load(x, i))
                  }
              }
              function array_load(x, i) -> v {
                  let len := calldataload(x)
                  if iszero(lt(i, len)) { revert(0, 0) }
                  let data := add(x, 0x20)
                  v := calldataload(add(data, mul(i, 0x20)))
              }
          } |]
        let b = [i| {
          calldatacopy(0,0,1024)
               {
                   let _1 := calldataload(0)
                   let sum := 0
                   let length := calldataload(_1)
                   let i := 0
                   for { } true { i := add(i, 1) }
                   {
                       let _2 := iszero(lt(i, length))
                       if _2 { break }
                       _2 := 0
                       sum := add(sum, calldataload(add(add(_1, shl(5, i)), 0x20)))
                   }
                   sstore(0, sum)
               }
           } |]
        Just aPrgm <- yul (T.pack "") $ T.pack a
        Just bPrgm <- yul (T.pack "") $ T.pack b
        let hexStrA = bsToHex aPrgm
            hexStrB = bsToHex bPrgm
        (exitCode, stdout, stderr) <- readProcessWithExitCode "cabal" ["run", "exe:hevm", "--", "equivalence", "--num-solvers", "1", "--debug", "--code-a", hexStrA, "--code-b", hexStrB] ""
        stdout `shouldContain` "Qed found via cache"

