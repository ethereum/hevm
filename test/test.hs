{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Prelude hiding (LT, GT)

import GHC.TypeLits
import Data.Proxy
import Control.Monad
import Control.Monad.ST (RealWorld, stToIO)
import Control.Monad.State.Strict
import Control.Monad.IO.Unlift
import Control.Monad.Reader (ReaderT)
import Data.Bits hiding (And, Xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)
import Data.DoubleWord
import Data.Either
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Time (diffUTCTime, getCurrentTime)
import Data.Tuple.Extra
import Data.Typeable
import Data.Vector qualified as V
import Data.Word (Word8)
import GHC.Conc (getNumProcessors)
import System.Directory
import System.Environment
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty.HUnit
import Test.Tasty.Runners hiding (Failure, Success)
import Test.Tasty.ExpectedFailure
import Text.RE.TDFA.String
import Text.RE.Replace
import Witch (unsafeInto, into)
import Data.Containers.ListUtils (nubOrd)

import Optics.Core hiding (pre, re, elements)
import Optics.State

import EVM hiding (choose)
import EVM.ABI
import EVM.Assembler
import EVM.Exec
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexText, formatExpr)
import EVM.Precompiled
import EVM.RLP
import EVM.SMT hiding (one)
import EVM.Solidity
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Test.Tracing qualified as Tracing
import EVM.Test.Utils
import EVM.Traversals
import EVM.Types hiding (Env)
import EVM.Effects
import EVM.UnitTest (writeTrace)

testEnv :: Env
testEnv = Env { config = defaultConfig {
  dumpQueries = False
  , dumpExprs = False
  , dumpEndStates = False
  , debug = False
  , abstRefineArith = False
  , abstRefineMem   = False
  , dumpTrace = False
  , decomposeStorage = True
  } }

putStrLnM :: (MonadUnliftIO m) => String -> m ()
putStrLnM a = liftIO $ putStrLn a

assertEqualM :: (App m, Eq a, Show a, HasCallStack) => String -> a -> a -> m ()
assertEqualM a b c = liftIO $ assertEqual a b c

assertBoolM
  :: (MonadUnliftIO m, HasCallStack)
  => String -> Bool -> m ()
assertBoolM a b = liftIO $ assertBool a b

test :: TestName -> ReaderT Env IO () -> TestTree
test a b = testCase a $ runEnv testEnv b

testFuzz :: TestName -> ReaderT Env IO () -> TestTree
testFuzz a b = testCase a $ runEnv (testEnv {config = testEnv.config {numCexFuzz = 100, onlyCexFuzz = True}}) b

prop :: Testable prop => ReaderT Env IO prop -> Property
prop a = ioProperty $ runEnv testEnv a

main :: IO ()
main = defaultMain tests

-- | run a subset of tests in the repl. p is a tasty pattern:
-- https://github.com/UnkindPartition/tasty/tree/ee6fe7136fbcc6312da51d7f1b396e1a2d16b98a#patterns
runSubSet :: String -> IO ()
runSubSet p = defaultMain . applyPattern p $ tests

tests :: TestTree
tests = testGroup "hevm"
  [ Tracing.tests
  , testGroup "simplify-storage"
    [ test "simplify-storage-array-only-static" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              a[0] = val1 + 1;
              a[1] = val2 + 2;
              assert(a[0]+a[1] == val1 + val2 + 3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    -- This case is somewhat artificial. We can't simplify this using only
    -- static rewrite rules, because acct is totally abstract and acct + 1
    -- could overflow back to zero. we may be able to do better if we have some
    -- smt assisted simplification that can take branch conditions into account.
    , expectFail $ test "simplify-storage-array-symbolic-index" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint b;
          uint[] a;
          function transfer(uint acct, uint val1) public {
            unchecked {
              a[acct] = val1;
              assert(a[acct] == val1);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- T.writeFile "symbolic-index.expr" $ formatExpr expr
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , expectFail $ test "simplify-storage-array-of-struct-symbolic-index" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          MyStruct[] arr;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              arr[acct].a = val1+1;
              arr[acct].b = val1+2;
              assert(arr[acct].a + arr[acct].b == val1+val2+3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "simplify-storage-array-loop-nonstruct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function transfer(uint v) public {
            for (uint i = 0; i < a.length; i++) {
              a[i] = v;
              assert(a[i] == v);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256)" [AbiUIntType 256])) [] (defaultVeriOpts { maxIter = Just 5 })
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "simplify-storage-map-newtest1" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (uint => uint) a;
          mapping (uint => uint) b;
          function fun(uint v, uint i) public {
            require(i < 1000);
            require(v < 1000);
            b[i+v] = v+1;
            a[i] = v;
            b[i+1] = v+1;
            assert(a[i] == v);
            assert(b[i+1] == v+1);
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
       (_, [(Qed _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       liftIO $ putStrLn "OK"
    , ignoreTest $ test "simplify-storage-map-todo" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (uint => uint) a;
          mapping (uint => uint) b;
          function fun(uint v, uint i) public {
            require(i < 1000);
            require(v < 1000);
            a[i] = v;
            b[i+1] = v+1;
            b[i+v] = 55; // note: this can overwrite b[i+1], hence assert below can fail
            assert(a[i] == v);
            assert(b[i+1] == v+1);
          }
        }
        |]
       -- TODO: expression below contains (load idx1 (store idx1 (store idx1 (store idx0)))), and the idx0
       --       is not stripped. This is due to us not doing all we can in this case, see
       --       note above readStorage. Decompose remedies this (when it can be decomposed)
       -- expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr expr
       (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       liftIO $ putStrLn "OK"
    , test "simplify-storage-array-loop-struct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          MyStruct[] arr;
          function transfer(uint v1, uint v2) public {
            for (uint i = 0; i < arr.length; i++) {
              arr[i].a = v1+1;
              arr[i].b = v2+2;
              assert(arr[i].a + arr[i].b == v1 + v2 + 3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] (defaultVeriOpts { maxIter = Just 5 })
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "decompose-1" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          function prove_mapping_access(address x, address y) public {
              require(x != y);
              balances[x] = 1;
              balances[y] = 2;
              assert(balances[x] != balances[y]);
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_mapping_access(address,address)" [AbiAddressType, AbiAddressType])) [] defaultVeriOpts
      putStrLnM $ T.unpack $ formatExpr expr
      let simpExpr = mapExprM Expr.decomposeStorage expr
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    , test "decompose-2" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          function prove_mixed_symoblic_concrete_writes(address x, uint v) public {
              balances[x] = v;
              balances[address(0)] = balances[x];
              assert(balances[address(0)] == v);
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_mixed_symoblic_concrete_writes(address,uint256)" [AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = mapExprM Expr.decomposeStorage expr
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    , test "decompose-3" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          function prove_array(uint x, uint v1, uint y, uint v2) public {
              require(v1 != v2);
              a[x] = v1;
              a[y] = v2;
              assert(a[x] == a[y]);
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = mapExprM Expr.decomposeStorage expr
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    , test "decompose-4-mixed" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          mapping( uint => uint) balances;
          function prove_array(uint x, uint v1, uint y, uint v2) public {
              require(v1 != v2);
              balances[x] = v1+1;
              balances[y] = v1+2;
              a[x] = v1;
              assert(balances[x] != balances[y]);
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_array(uint256,uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = mapExprM Expr.decomposeStorage expr
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    , test "decompose-5-mixed" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping (address => uint) balances;
          mapping (uint => bool) auth;
          uint[] arr;
          uint a;
          uint b;
          function prove_mixed(address x, address y, uint val) public {
            b = val+1;
            require(x != y);
            balances[x] = val;
            a = val;
            arr[val] = 5;
            auth[val+1] = true;
            balances[y] = val+2;
            if (balances[y] == balances[y]) {
                assert(balances[y] == val);
            }
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_mixed(address,address,uint256)" [AbiAddressType, AbiAddressType, AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = mapExprM Expr.decomposeStorage expr
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    -- TODO check what's going on here. Likely the "arbitrary write through array" is the reason why we fail
    , expectFail $ test "decompose-6-fail" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] arr;
          function prove_mixed(uint val) public {
            arr[val] = 5;
            arr[val+1] = val+5;
            assert(arr[val] == arr[val+1]);
          }
        }
        |]
      expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "prove_mixed(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
      let simpExpr = mapExprM Expr.decomposeStorage expr
      -- putStrLnM $ T.unpack $ formatExpr (fromJust simpExpr)
      assertEqualM "Decompose did not succeed." (isJust simpExpr) True
    , test "simplify-storage-map-only-static" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[0] = val1+1;
              items1[1] = val2+2;
              assert(items1[0]+items1[1] == val1 + val2 + 3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "simplify-storage-map-only-2" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[acct] = val1+1;
              items1[acct+1] = val2+2;
              assert(items1[acct]+items1[acct+1] == val1 + val2 + 3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr expr
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "simplify-storage-map-with-struct" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          struct MyStruct {
            uint a;
            uint b;
          }
          mapping(uint => MyStruct) items1;
          function transfer(uint acct, uint val1, uint val2) public {
            unchecked {
              items1[acct].a = val1+1;
              items1[acct].b = val2+2;
              assert(items1[acct].a+items1[acct].b == val1 + val2 + 3);
            }
          }
        }
        |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    , test "simplify-storage-map-and-array" $ do
       Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          uint[] a;
          mapping(uint => uint) items1;
          mapping(uint => uint) items2;
          function transfer(uint acct, uint val1, uint val2) public {
            uint beforeVal1 = items1[acct];
            uint beforeVal2 = items2[acct];
            unchecked {
              items1[acct] = val1+1;
              items2[acct] = val2+2;
              a[0] = val1 + val2 + 1;
              a[1] = val1 + val2 + 2;
              assert(items1[acct]+items2[acct]+a[0]+a[1] > beforeVal1 + beforeVal2);
            }
          }
        }
       |]
       expr <- withSolvers Z3 1 Nothing $ \s -> getExpr s c (Just (Sig "transfer(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
       -- putStrLnM $ T.unpack $ formatExpr expr
       assertEqualM "Expression is not clean." (badStoresInExpr expr) False
    ]
  , testGroup "StorageTests"
    [ test "read-from-sstore" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x0) (Lit 0xab) (AbstractStore (LitAddr 0x0) Nothing)))
    , test "read-from-concrete" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, 0xab)]))
    , test "read-past-write" $ assertEqualM ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x1) (Var "b") (ConcreteStore $ Map.fromList [(0x0, 0xab)])))
    , test "accessStorage uses fetchedStorage" $ do
        let dummyContract =
              (initialContract (RuntimeCode (ConcreteRuntimeCode mempty)))
                { external = True }
        vm :: VM Concrete RealWorld <- liftIO $ stToIO $ vmForEthrunCreation ""
            -- perform the initial access
        vm1 <- liftIO $ stToIO $ execStateT (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm
        -- it should fetch the contract first
        vm2 <- case vm1.result of
                Just (HandleEffect (Query (PleaseFetchContract _addr _ continue))) ->
                  liftIO $ stToIO $ execStateT (continue dummyContract) vm1
                _ -> internalError "unexpected result"
            -- then it should fetch the slow
        vm3 <- case vm2.result of
                    Just (HandleEffect (Query (PleaseFetchSlot _addr _slot continue))) ->
                      liftIO $ stToIO $ execStateT (continue 1337) vm2
                    _ -> internalError "unexpected result"
            -- perform the same access as for vm1
        vm4 <- liftIO $ stToIO $ execStateT (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm3

        -- there won't be query now as accessStorage uses fetch cache
        assertBoolM (show vm4.result) (isNothing vm4.result)
    ]
  , testGroup "SimplifierUnitTests"
    -- common overflow cases that the simplifier was getting wrong
    [ test "writeWord-overflow" $ do
        let e = ReadByte (Lit 0x0) (WriteWord (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd) (Lit 0x0) (ConcreteBuf "\255\255\255\255"))
        b <- checkEquiv e (Expr.simplify e)
        assertBoolM "Simplifier failed" b
    , test "simp-max-buflength" $ do
      let simp = Expr.simplify $ Max (Lit 0) (BufLength (AbstractBuf "txdata"))
      assertEqualM "max-buflength rules" simp $ BufLength (AbstractBuf "txdata")
    , test "simp-PLT-max" $ do
      let simp = Expr.simplifyProp $ PLT (Max (Lit 5) (BufLength (AbstractBuf "txdata"))) (Lit 99)
      assertEqualM "max-buflength rules" simp $ PLT (BufLength (AbstractBuf "txdata")) (Lit 99)
    , test "simp-assoc-add1" $ do
      let simp = Expr.simplify $        Add (Var "a") (Add (Var "b") (Var "c"))
      assertEqualM "assoc rules" simp $ Add (Add (Var "a") (Var "b")) (Var "c")
    , test "simp-assoc-add2" $ do
      let simp = Expr.simplify $        Add (Lit 1) (Add (Var "b") (Var "c"))
      assertEqualM "assoc rules" simp $ Add (Add (Lit 1) (Var "b")) (Var "c")
    , test "simp-assoc-add3" $ do
      let simp = Expr.simplify $        Add (Lit 1) (Add (Lit 2) (Var "c"))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "c")
    , test "simp-assoc-add4" $ do
      let simp = Expr.simplify $        Add (Lit 1) (Add (Var "b") (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "b")
    , test "simp-assoc-add5" $ do
      let simp = Expr.simplify $        Add (Var "a") (Add (Lit 1) (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Lit 3) (Var "a")
    , test "simp-assoc-add6" $ do
      let simp = Expr.simplify $        Add (Lit 7) (Add (Lit 1) (Lit 2))
      assertEqualM "assoc rules" simp $ Lit 10
    , test "simp-assoc-add-7" $ do
      let simp = Expr.simplify $        Add (Var "a") (Add (Var "b") (Lit 2))
      assertEqualM "assoc rules" simp $ Add (Add (Lit 2) (Var "a")) (Var "b")
    , test "simp-assoc-add8" $ do
      let simp = Expr.simplify $        Add (Add (Var "a") (Add (Lit 0x2) (Var "b"))) (Add (Var "c") (Add (Lit 0x2) (Var "d")))
      assertEqualM "assoc rules" simp $ Add (Add (Add (Add (Lit 0x4) (Var "a")) (Var "b")) (Var "c")) (Var "d")
    , test "simp-assoc-mul1" $ do
      let simp = Expr.simplify $        Mul (Var "a") (Mul (Var "b") (Var "c"))
      assertEqualM "assoc rules" simp $ Mul (Mul (Var "a") (Var "b")) (Var "c")
    , test "simp-assoc-mul2" $ do
      let simp = Expr.simplify       $  Mul (Lit 2) (Mul (Var "a") (Lit 3))
      assertEqualM "assoc rules" simp $ Mul (Lit 6) (Var "a")
    , test "bufLength-simp" $ do
      let
        a = BufLength (ConcreteBuf "ab")
        simp = Expr.simplify a
      assertEqualM "Must be simplified down to a Lit" simp (Lit 2)
    , test "CopySlice-overflow" $ do
        let e = ReadWord (Lit 0x0) (CopySlice (Lit 0x0) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc) (Lit 0x6) (ConcreteBuf "\255\255\255\255\255\255") (ConcreteBuf ""))
        b <- checkEquiv e (Expr.simplify e)
        assertBoolM "Simplifier failed" b
    , test "stripWrites-overflow" $ do
        -- below eventually boils down to
        -- unsafeInto (0xf0000000000000000000000000000000000000000000000000000000000000+1) :: Int
        -- which failed before
        let
          a = ReadByte (Lit 0xf0000000000000000000000000000000000000000000000000000000000000) (WriteByte (And (SHA256 (ConcreteBuf "")) (Lit 0x1)) (LitByte 0) (ConcreteBuf ""))
          b = Expr.simplify a
        ret <- checkEquiv a b
        assertBoolM "must be equivalent" ret
    ]
  -- These tests fuzz the simplifier by generating a random expression,
  -- applying some simplification rules, and then using the smt encoding to
  -- check that the simplified version is semantically equivalent to the
  -- unsimplified one
  , adjustOption (\(Test.Tasty.QuickCheck.QuickCheckTests n) -> Test.Tasty.QuickCheck.QuickCheckTests (min n 50)) $ testGroup "SimplifierTests"
    [ testProperty  "buffer-simplification" $ \(expr :: Expr Buf) -> prop $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "store-simplification" $ \(expr :: Expr Storage) -> prop $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "load-simplification" $ \(GenWriteStorageLoad expr) -> prop $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , ignoreTest $ testProperty "load-decompose" $ \(GenWriteStorageLoad expr) -> prop $ do
        putStrLnM $ T.unpack $ formatExpr expr
        let simp = Expr.simplify expr
        let decomposed = fromMaybe simp $ mapExprM Expr.decomposeStorage simp
        -- putStrLnM $ "-----------------------------------------"
        -- putStrLnM $ T.unpack $ formatExpr decomposed
        -- putStrLnM $ "\n\n\n\n"
        checkEquiv expr decomposed
    , testProperty "byte-simplification" $ \(expr :: Expr Byte) -> prop $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "word-simplification" $ \(ZeroDepthWord expr) -> prop $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "readStorage-equivalance" $ \(store, slot) -> prop $ do
        let simplified = Expr.readStorage' slot store
            full = SLoad slot store
        checkEquiv simplified full
    , testProperty "writeStorage-equivalance" $ \(val, GenWriteStorageExpr (slot, store)) -> prop $ do
        let simplified = Expr.writeStorage slot val store
            full = SStore slot val store
        checkEquiv simplified full
    , testProperty "readWord-equivalance" $ \(buf, idx) -> prop $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        checkEquiv simplified full
    , testProperty "writeWord-equivalance" $ \(idx, val, WriteWordBuf buf) -> prop $ do
        let simplified = Expr.writeWord idx val buf
            full = WriteWord idx val buf
        checkEquiv simplified full
    , testProperty "arith-simplification" $ \(_ :: Int) -> prop $ do
        expr <- liftIO $ generate . sized $ genWordArith 15
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "readByte-equivalance" $ \(buf, idx) -> prop $ do
        let simplified = Expr.readByte idx buf
            full = ReadByte idx buf
        checkEquiv simplified full
    -- we currently only simplify concrete writes over concrete buffers so that's what we test here
    , testProperty "writeByte-equivalance" $ \(LitOnly val, LitOnly buf, GenWriteByteIdx idx) -> prop $ do
        let simplified = Expr.writeByte idx val buf
            full = WriteByte idx val buf
        checkEquiv simplified full
    , testProperty "copySlice-equivalance" $ \(srcOff, GenCopySliceBuf src, GenCopySliceBuf dst, LitWord @300 size) -> prop $ do
        -- we bias buffers to be concrete more often than not
        dstOff <- liftIO $ generate (maybeBoundedLit 100_000)
        let simplified = Expr.copySlice srcOff dstOff size src dst
            full = CopySlice srcOff dstOff size src dst
        checkEquiv simplified full
    , testProperty "indexWord-equivalence" $ \(src, LitWord @50 idx) -> prop $ do
        let simplified = Expr.indexWord idx src
            full = IndexWord idx src
        checkEquiv simplified full
    , testProperty "indexWord-mask-equivalence" $ \(src :: Expr EWord, LitWord @35 idx) -> prop $ do
        mask <- liftIO $ generate $ do
          pow <- arbitrary :: Gen Int
          frequency
           [ (1, pure $ Lit $ (shiftL 1 (pow `mod` 256)) - 1)        -- potentially non byte aligned
           , (1, pure $ Lit $ (shiftL 1 ((pow * 8) `mod` 256)) - 1)  -- byte aligned
           ]
        let
          input = And mask src
          simplified = Expr.indexWord idx input
          full = IndexWord idx input
        checkEquiv simplified full
    , testProperty "toList-equivalance" $ \buf -> prop $ do
        let
          -- transforms the input buffer to give it a known length
          fixLength :: Expr Buf -> Gen (Expr Buf)
          fixLength = mapExprM go
            where
              go :: Expr a -> Gen (Expr a)
              go = \case
                WriteWord _ val b -> liftM3 WriteWord idx (pure val) (pure b)
                WriteByte _ val b -> liftM3 WriteByte idx (pure val) (pure b)
                CopySlice so _ sz src dst -> liftM5 CopySlice (pure so) idx (pure sz) (pure src) (pure dst)
                AbstractBuf _ -> cbuf
                e -> pure e
              cbuf = do
                bs <- arbitrary
                pure $ ConcreteBuf bs
              idx = do
                w <- arbitrary
                -- we use 100_000 as an upper bound for indices to keep tests reasonably fast here
                pure $ Lit (w `mod` 100_000)

        input <- liftIO $ generate $ fixLength buf
        case Expr.toList input of
          Nothing -> do
            putStrLnM "skip"
            pure True -- ignore cases where the buf cannot be represented as a list
          Just asList -> do
            let asBuf = Expr.fromList asList
            checkEquiv asBuf input
    , testProperty "simplifyProp-equivalence-lit" $ \(LitProp p) -> prop $ do
        let simplified = Expr.simplifyProps [p]
        case simplified of
          [] -> checkEquivProp (PBool True) p
          [val@(PBool _)] -> checkEquivProp val p
          _ -> liftIO $ assertFailure "must evaluate down to a literal bool"
    , testProperty "simplifyProp-equivalence-sym" $ \(p) -> prop $ do
        let simplified = Expr.simplifyProp p
        checkEquivProp simplified p
    , testProperty "simpProp-equivalence-sym-Prop" $ \(ps :: [Prop]) -> prop $ do
        let simplified = pand (Expr.simplifyProps ps)
        checkEquivProp simplified (pand ps)
    , testProperty "simpProp-equivalence-sym-LitProp" $ \(LitProp p) -> prop $ do
        let simplified = pand (Expr.simplifyProps [p])
        checkEquivProp simplified p
    , testProperty "storage-slot-simp-property" $ \(StorageExp s) -> prop $ do
        -- we have to run `Expr.structureArraySlots` on the unsimplified system, or
        -- we'd need some form of minimal simplifier for things to work out. As long as
        -- we trust the structureArraySlots, this is fine, as that function is standalone,
        -- and quite minimal
        let s2 = Expr.structureArraySlots s
        let simplified = Expr.simplify s2
        checkEquiv simplified s2
    ]
  , testGroup "isUnsat-concrete-tests" [
      test "disjunction-left-false" $ do
        let
          t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 0)) (PEq (Var "y") (Lit 1)), PEq (Var "y") (Lit 2)]
          cannotBeSat = Expr.isUnsat t
        assertEqualM "Must be equal" cannotBeSat True
    , test "disjunction-right-false" $ do
        let
          t = [PEq (Var "x") (Lit 1), POr (PEq (Var "y") (Lit 1)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
          cannotBeSat = Expr.isUnsat t
        assertEqualM "Must be equal" cannotBeSat True
    , test "disjunction-both-false" $ do
        let
          t = [PEq (Var "x") (Lit 1), POr (PEq (Var "x") (Lit 2)) (PEq (Var "x") (Lit 0)), PEq (Var "y") (Lit 2)]
          cannotBeSat = Expr.isUnsat t
        assertEqualM "Must be equal" cannotBeSat True
    , ignoreTest $ test "disequality-and-equality" $ do
        let
          t = [PNeg (PEq (Lit 1) (Var "arg1")), PEq (Lit 1) (Var "arg1")]
          cannotBeSat = Expr.isUnsat t
        assertEqualM "Must be equal" cannotBeSat True
    , test "equality-and-disequality" $ do
        let
          t = [PEq (Lit 1) (Var "arg1"), PNeg (PEq (Lit 1) (Var "arg1"))]
          cannotBeSat = Expr.isUnsat t
        assertEqualM "Must be equal" cannotBeSat True
  ]
  , testGroup "simpProp-concrete-tests" [
      test "simpProp-concrete-trues" $ do
        let
          t = [PBool True, PBool True]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
    , test "simpProp-concrete-false1" $ do
        let
          t = [PBool True, PBool False]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-false2" $ do
        let
          t = [PBool False, PBool False]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-or-1" $ do
        let
          -- a = 5 && (a=4 || a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , ignoreTest $ test "simpProp-concrete-or-2" $ do
        let
          -- Currently does not work, because we don't do simplification inside
          --   POr/PAnd using canBeSat
          -- a = 5 && (a=4 || a=5)  -> a=5
          t = [PEq (Lit 5) (Var "a"), POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 5))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
    , test "simpProp-concrete-and-1" $ do
        let
          -- a = 5 && (a=4 && a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), PAnd (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-concrete-or-of-or" $ do
        let
          -- a = 5 && ((a=4 || a=6) || a=3)  -> False
          t = [PEq (Lit 5) (Var "a"), POr (POr (PEq (Var "a") (Lit 4)) (PEq (Var "a") (Lit 6))) (PEq (Var "a") (Lit 3))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-simp" $ do
        let
          -- 5+1 = 6
          t = [PEq (Add (Lit 5) (Lit 1)) (Var "a")]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PEq (Lit 6) (Var "a")] simplified
    , test "simpProp-inner-expr-simp-with-canBeSat" $ do
        let
          -- 5+1 = 6, 6 != 7
          t = [PAnd (PEq (Add (Lit 5) (Lit 1)) (Var "a")) (PEq (Var "a") (Lit 7))]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-bitwise-and" $ do
        let
          -- 1 & 2 != 2
          t = [PEq (And (Lit 1) (Lit 2)) (Lit 2)]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [PBool False] simplified
    , test "simpProp-inner-expr-bitwise-or" $ do
        let
          -- 2 | 4 == 6
          t = [PEq (Or (Lit 2) (Lit 4)) (Lit 6)]
          simplified = Expr.simplifyProps t
        assertEqualM "Must be equal" [] simplified
  ]
  , testGroup "MemoryTests"
    [ test "read-write-same-byte"  $ assertEqualM ""
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteByte (Lit 0x20) (LitByte 0x12) mempty))
    , test "read-write-same-word"  $ assertEqualM ""
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , test "read-byte-write-word"  $ assertEqualM ""
        -- reading at byte 31 a word that's been written should return LSB
        (LitByte 0x12)
        (Expr.readByte (Lit 0x1f) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , test "read-byte-write-word2"  $ assertEqualM ""
        -- Same as above, but offset not 0
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteWord (Lit 0x1) (Lit 0x12) mempty))
    ,test "read-write-with-offset"  $ assertEqualM ""
        -- 0x3F = 63 decimal, 0x20 = 32. 0x12 = 18
        --    We write 128bits (32 Bytes), representing 18 at offset 32.
        --    Hence, when reading out the 63rd byte, we should read out the LSB 8 bits
        --           which is 0x12
        (LitByte 0x12)
        (Expr.readByte (Lit 0x3F) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    ,test "read-write-with-offset2"  $ assertEqualM ""
        --  0x20 = 32, 0x3D = 61
        --  we write 128 bits (32 Bytes) representing 0x10012, at offset 32.
        --  we then read out a byte at offset 61.
        --  So, at 63 we'd read 0x12, at 62 we'd read 0x00, at 61 we should read 0x1
        (LitByte 0x1)
        (Expr.readByte (Lit 0x3D) (WriteWord (Lit 0x20) (Lit 0x10012) mempty))
    , test "read-write-with-extension-to-zero" $ assertEqualM ""
        -- write word and read it at the same place (i.e. 0 offset)
        (Lit 0x12)
        (Expr.readWord (Lit 0x0) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , test "read-write-with-extension-to-zero-with-offset" $ assertEqualM ""
        -- write word and read it at the same offset of 4
        (Lit 0x12)
        (Expr.readWord (Lit 0x4) (WriteWord (Lit 0x4) (Lit 0x12) mempty))
    , test "read-write-with-extension-to-zero-with-offset2" $ assertEqualM ""
        -- write word and read it at the same offset of 16
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , test "read-word-copySlice-overlap" $ assertEqualM ""
        -- we should not recurse into a copySlice if the read index + 32 overlaps the sliced region
        (ReadWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
        (Expr.readWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
    , test "indexword-MSB" $ assertEqualM ""
        -- 31st is the LSB byte (of 32)
        (LitByte 0x78)
        (Expr.indexWord (Lit 31) (Lit 0x12345678))
    , test "indexword-LSB" $ assertEqualM ""
        -- 0th is the MSB byte (of 32), Lit 0xff22bb... is exactly 32 Bytes.
        (LitByte 0xff)
        (Expr.indexWord (Lit 0) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , test "indexword-LSB2" $ assertEqualM ""
        -- same as above, but with offset 2
        (LitByte 0xbb)
        (Expr.indexWord (Lit 2) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , test "encodeConcreteStore-overwrite" $
      assertEqualM ""
        "(store (store ((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000) (_ bv1 256) (_ bv2 256)) (_ bv3 256) (_ bv4 256))"
        (EVM.SMT.encodeConcreteStore $
          Map.fromList [(W256 1, W256 2), (W256 3, W256 4)])
    , test "indexword-oob-sym" $ assertEqualM ""
        -- indexWord should return 0 for oob access
        (LitByte 0x0)
        (Expr.indexWord (Lit 100) (JoinBytes
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)))
    , test "stripbytes-concrete-bug" $ assertEqualM ""
        (Expr.simplifyReads (ReadByte (Lit 0) (ConcreteBuf "5")))
        (LitByte 53)
    ]
  , testGroup "ABI"
    [ testProperty "Put/get inverse" $ \x ->
        case runGetOrFail (getAbi (abiValueType x)) (runPut (putAbi x)) of
          Right ("", _, x') -> x' == x
          _ -> False
    ]
  , testGroup "Solidity-Expressions"
    [ test "Trivial" $
        SolidityCall "x = 3;" []
          ===> AbiUInt 256 3
    , test "Arithmetic" $ do
        SolidityCall "x = a + 1;"
          [AbiUInt 256 1] ===> AbiUInt 256 2
        SolidityCall "unchecked { x = a - 1; }"
          [AbiUInt 8 0] ===> AbiUInt 8 255

    , test "keccak256()" $
        SolidityCall "x = uint(keccak256(abi.encodePacked(a)));"
          [AbiString ""] ===> AbiUInt 256 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    , testProperty "symbolic-abi-enc-vs-solidity" $ \(SymbolicAbiVal y) -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a);|] [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let
              frag = [symAbiArg "y" (AbiTupleType $ V.fromList [abiValueType y])]
              (hevmEncoded, _) = first (Expr.drop 4) $ combineFragments frag (ConcreteBuf "")
              expectedVals = expectedConcVals "y" (AbiTuple . V.fromList $ [y])
              hevmConcretePre = subModel expectedVals hevmEncoded
              hevmConcrete = case Expr.simplify hevmConcretePre of
                               ConcreteBuf b -> b
                               buf -> internalError ("valMap: " <> show expectedVals <> "\ny:" <> show y <> "\n" <> "buf: " <> show buf)
          -- putStrLnM $ "frag: " <> show frag
          -- putStrLnM $ "expectedVals: " <> show expectedVals
          -- putStrLnM $ "frag: " <> show frag
          -- putStrLnM $ "hevmEncoded: " <> show hevmEncoded
          -- putStrLnM $ "solidity encoded: " <> show solidityEncoded
          -- putStrLnM $ "our encoded     : " <> show (AbiBytesDynamic hevmConcrete)
          -- putStrLnM $ "y     : " <> show y
          -- putStrLnM $ "y type: " <> showAlter y
          -- putStrLnM $ "hevmConcretePre: " <> show hevmConcretePre
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmConcrete)
    , testProperty "symbolic-abi encoding-vs-solidity-2-args" $ \(SymbolicAbiVal x', SymbolicAbiVal y') -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a, b);|] [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [x',y'])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)
    , testProperty "abi-encoding-vs-solidity" $ forAll (arbitrary >>= genAbiValue) $
      \y -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a);|]
            [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [y])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    , testProperty "abi-encoding-vs-solidity-2-args" $ forAll (arbitrary >>= bothM genAbiValue) $
      \(x', y') -> prop $ do
          Just encoded <- runStatements [i| x = abi.encode(a, b);|]
            [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [x',y'])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    -- we need a separate test for this because the type of a function is "function() external" in solidity but just "function" in the abi:
    , testProperty "abi-encoding-vs-solidity-function-pointer" $ withMaxSuccess 20 $ forAll (genAbiValue AbiFunctionType) $
      \y -> prop $ do
          Just encoded <- runFunction [i|
              function foo(function() external a) public pure returns (bytes memory x) {
                x = abi.encode(a);
              }
            |] (abiMethod "foo(function)" (AbiTuple (V.singleton y)))
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ V.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (V.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ V.fromList [y])
          assertEqualM "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)
    ]

  , testGroup "Precompiled contracts"
      [ testGroup "Example (reverse)"
          [ test "success" $
              assertEqualM "example contract reverses"
                (execute 0xdeadbeef "foobar" 6) (Just "raboof")
          , test "failure" $
              assertEqualM "example contract fails on length mismatch"
                (execute 0xdeadbeef "foobar" 5) Nothing
          ]

      , testGroup "ECRECOVER"
          [ test "success" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
                a = hex "0000000000000000000000002d5e56d45c63150d937f2182538a0f18510cb11f"
              assertEqualM "successful recovery"
                (Just a)
                (execute 1 (h <> v <> r <> s) 32)
          , test "fail on made up values" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4731"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
              assertEqualM "fail because bit flip"
                Nothing
                (execute 1 (h <> v <> r <> s) 32)
          ]
      ]
  , testGroup "Byte/word manipulations"
    [ testProperty "padLeft length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padLeft identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padRight length" $ \n (Bytes bs) ->
        BS.length (padLeft n bs) == max n (BS.length bs)
    , testProperty "padRight identity" $ \(Bytes bs) ->
        padLeft (BS.length bs) bs == bs
    , testProperty "padLeft zeroing" $ \(NonNegative n) (Bytes bs) ->
        let x = BS.take n (padLeft (BS.length bs + n) bs)
            y = BS.replicate n 0
        in x == y
    ]

  , testGroup "Unresolved link detection"
    [ test "holes detected" $ do
        let code' = "608060405234801561001057600080fd5b5060405161040f38038061040f83398181016040528101906100329190610172565b73__$f3cbc3eb14e5bd0705af404abcf6f741ec$__63ab5c1ffe826040518263ffffffff1660e01b81526004016100699190610217565b60206040518083038186803b15801561008157600080fd5b505af4158015610095573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906100b99190610145565b50506103c2565b60006100d36100ce84610271565b61024c565b9050828152602081018484840111156100ef576100ee610362565b5b6100fa8482856102ca565b509392505050565b600081519050610111816103ab565b92915050565b600082601f83011261012c5761012b61035d565b5b815161013c8482602086016100c0565b91505092915050565b60006020828403121561015b5761015a61036c565b5b600061016984828501610102565b91505092915050565b6000602082840312156101885761018761036c565b5b600082015167ffffffffffffffff8111156101a6576101a5610367565b5b6101b284828501610117565b91505092915050565b60006101c6826102a2565b6101d081856102ad565b93506101e08185602086016102ca565b6101e981610371565b840191505092915050565b60006102016003836102ad565b915061020c82610382565b602082019050919050565b6000604082019050818103600083015261023181846101bb565b90508181036020830152610244816101f4565b905092915050565b6000610256610267565b905061026282826102fd565b919050565b6000604051905090565b600067ffffffffffffffff82111561028c5761028b61032e565b5b61029582610371565b9050602081019050919050565b600081519050919050565b600082825260208201905092915050565b60008115159050919050565b60005b838110156102e85780820151818401526020810190506102cd565b838111156102f7576000848401525b50505050565b61030682610371565b810181811067ffffffffffffffff821117156103255761032461032e565b5b80604052505050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b600080fd5b600080fd5b600080fd5b600080fd5b6000601f19601f8301169050919050565b7f6261720000000000000000000000000000000000000000000000000000000000600082015250565b6103b4816102be565b81146103bf57600080fd5b50565b603f806103d06000396000f3fe6080604052600080fdfea26469706673582212207d03b26e43dc3d116b0021ddc9817bde3762a3b14315351f11fc4be384fd14a664736f6c63430008060033"
        assertBoolM "linker hole not detected" (containsLinkerHole code'),
      test "no false positives" $ do
        let code' = "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
        assertBoolM "false positive" (not . containsLinkerHole $ code')
    ]

  , testGroup "metadata stripper"
    [ test "it strips the metadata for solc => 0.6" $ do
        let code' = hexText "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
            stripped = stripBytecodeMetadata code'
        assertEqualM "failed to strip metadata" (show (ByteStringS stripped)) "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fe"
    ,
      testCase "it strips the metadata and constructor args" $ do
        let srccode =
              [i|
                contract A {
                  uint y;
                  constructor(uint x) public {
                    y = x;
                  }
                }
                |]

        Just initCode <- solidity "A" srccode
        assertEqual "constructor args screwed up metadata stripping" (stripBytecodeMetadata (initCode <> encodeAbiValue (AbiUInt 256 1))) (stripBytecodeMetadata initCode)
    ]

  , testGroup "RLP encodings"
    [ testProperty "rlp decode is a retraction (bytes)" $ \(Bytes bs) ->
      rlpdecode (rlpencode (BS bs)) == Just (BS bs)
    , testProperty "rlp encode is a partial inverse (bytes)" $ \(Bytes bs) ->
        case rlpdecode bs of
          Just r -> rlpencode r == bs
          Nothing -> True
    ,  testProperty "rlp decode is a retraction (RLP)" $ \(RLPData r) ->
       rlpdecode (rlpencode r) == Just r
    ]
 , testGroup "Panic code tests via symbolic execution"
  [
     test "assert-fail" $ do
       Just c <- solcRuntime "MyContract"
           [i|
           contract MyContract {
             function fun(uint256 a) external pure {
               assert(a != 0);
             }
            }
           |]
       (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       assertEqualM "Must be 0" 0 $ getVar ctr "arg1"
       putStrLnM  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
     ,
     test "safeAdd-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a+b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x11] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        let x = getVar ctr "arg1"
        let y = getVar ctr "arg2"

        let maxUint = 2 ^ (256 :: Integer) :: Integer
        assertBoolM "Overflow must occur" (toInteger x + toInteger y >= maxUint)
        putStrLnM "expected counterexample found"
     ,
     test "div-by-zero-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a/b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Bitwuzla 1 Nothing $ \s -> checkAssert s [0x12] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        assertEqualM "Division by 0 needs b=0" (getVar ctr "arg2") 0
        putStrLnM "expected counterexample found"
     ,
      test "unused-args-fail" $ do
         Just c <- solcRuntime "C"
             [i|
             contract C {
               function fun(uint256 a) public pure {
                 assert(false);
               }
             }
             |]
         (_, [Cex _]) <- withSolvers Bitwuzla 1 Nothing $ \s -> checkAssert s [0x1] c Nothing [] defaultVeriOpts
         putStrLnM "expected counterexample found"
      ,
     test "enum-conversion-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              enum MyEnum { ONE, TWO }
              function fun(uint256 a) external pure returns (MyEnum b) {
                b = MyEnum(a);
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Bitwuzla 1 Nothing $ \s -> checkAssert s [0x21] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        assertBoolM "Enum is only defined for 0 and 1" $ (getVar ctr "arg1") > 1
        putStrLnM "expected counterexample found"
     ,
     -- TODO 0x22 is missing: "0x22: If you access a storage byte array that is incorrectly encoded."
     -- TODO below should NOT fail
     -- TODO this has a loop that depends on a symbolic value and currently causes interpret to loop
     ignoreTest $ test "pop-empty-array" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              uint[] private arr;
              function fun(uint8 a) external {
                arr.push(1);
                arr.push(2);
                for (uint i = 0; i < a; i++) {
                  arr.pop();
                }
              }
             }
            |]
        a <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x31] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        liftIO $ do
          print $ length a
          print $ show a
          putStrLnM "expected counterexample found"
     ,
     test "access-out-of-bounds-array" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              uint[] private arr;
              function fun(uint8 a) external returns (uint x){
                arr.push(1);
                arr.push(2);
                x = arr[a];
              }
             }
            |]
        (_, [Cex (_, _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x32] c (Just (Sig "fun(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
        -- assertBoolM "Access must be beyond element 2" $ (getVar ctr "arg1") > 1
        putStrLnM "expected counterexample found"
      ,
      -- Note: we catch the assertion here, even though we are only able to explore partially
      test "alloc-too-much" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a) external {
                uint[] memory arr = new uint[](a);
              }
             }
            |]
        (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s ->
          checkAssert s [0x41] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "expected counterexample found"
      ,
      test "vm.deal unknown address" $ do
        Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function deal(address,uint256) external;
            }
            contract C {
              // this is not supported yet due to restrictions around symbolic address aliasing...
              function f(address e, uint val) external {
                  Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                  vm.deal(e, val);
                  assert(e.balance == val);
              }
            }
          |]
        Right e <- reachableUserAsserts c (Just $ Sig "f(address,uint256)" [AbiAddressType, AbiUIntType 256])
        assertBoolM "The expression is not partial" $ Expr.containsNode isPartial e
      ,
      test "vm.prank underflow" $ do
        Just c <- solcRuntime "C"
            [i|
              interface Vm {
                function prank(address) external;
              }
              contract Payable {
                  function hi() public payable {}
              }
              contract C {
                function f() external {
                  Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

                  uint amt = 10;
                  address from = address(0xacab);
                  require(from.balance < amt);

                  Payable target = new Payable();
                  vm.prank(from);
                  target.hi{value : amt}();
                }
              }
            |]
        r <- allBranchesFail c Nothing
        assertBoolM "all branches must fail" (isRight r)
      ,
      test "call ffi when disabled" $ do
        Just c <- solcRuntime "C"
            [i|
              interface Vm {
                function ffi(string[] calldata) external;
              }
              contract C {
                function f() external {
                  Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);

                  string[] memory inputs = new string[](2);
                  inputs[0] = "echo";
                  inputs[1] = "acab";

                  // should fail to explore this branch
                  vm.ffi(inputs);
                }
              }
            |]
        Right e <- reachableUserAsserts c Nothing
        liftIO $ T.putStrLn $ formatExpr e
        assertBoolM "The expression is not partial" $ Expr.containsNode isPartial e
      ,
      -- TODO: we can't deal with symbolic jump conditions
      expectFail $ test "call-zero-inited-var-thats-a-function" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function (uint256) internal returns (uint) funvar;
              function fun2(uint256 a) internal returns (uint){
                return a;
              }
              function fun(uint256 a) external returns (uint) {
                if (a != 44) {
                  funvar = fun2;
                }
                return funvar(a);
              }
             }
            |]
        (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s [0x51] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        let a = fromJust $ Map.lookup (Var "arg1") cex.vars
        assertEqualM "unexpected cex value" a 44
        putStrLnM "expected counterexample found"
  ]
  , testGroup "Symbolic-Constructor-Args"
    -- this produced some hard to debug failures. keeping it around since it seemed to exercise the contract creation code in interesting ways...
    [ test "multiple-symbolic-constructor-calls" $ do
        Just initCode <- solidity "C"
          [i|
            contract A {
                uint public x;
                constructor (uint z)  {}
            }

            contract B {
                constructor (uint i)  {}

            }

            contract C {
                constructor(uint u) {
                  new A(u);
                  new B(u);
                }
            }
          |]
        withSolvers Bitwuzla 1 Nothing $ \s -> do
          let calldata = (WriteWord (Lit 0x0) (Var "u") (ConcreteBuf ""), [])
          initVM <- liftIO $ stToIO $ abstractVM calldata initCode Nothing True
          expr <- Expr.simplify <$> interpret (Fetch.oracle s Nothing) Nothing 1 StackBased initVM runExpr
          assertBoolM "unexptected partial execution" (not $ Expr.containsNode isPartial expr)
    , test "mixed-concrete-symbolic-args" $ do
        Just c <- solcRuntime "C"
          [i|
            contract B {
                uint public x;
                uint public y;
                constructor (uint i, uint j)  {
                  x = i;
                  y = j;
                }

            }

            contract C {
                function foo(uint i) public {
                  B b = new B(10, i);
                  assert(b.x() == 10);
                  assert(b.y() == i);
                }
            }
          |]
        Right expr <- reachableUserAsserts c (Just $ Sig "foo(uint256)" [AbiUIntType 256])
        assertBoolM "unexptected partial execution" (not $ Expr.containsNode isPartial expr)
    , test "jump-into-symbolic-region" $ do
        let
          -- our initCode just jumps directly to the end
          code = BS.pack . mapMaybe maybeLitByte $ V.toList $ assemble
              [ OpPush (Lit 0x85)
              , OpJump
              , OpPush (Lit 1)
              , OpPush (Lit 1)
              , OpPush (Lit 1)
              , OpJumpdest
              ]
          -- we write a symbolic word to the middle, so the jump above should
          -- fail since the target is not in the concrete region
          initCode = (WriteWord (Lit 0x43) (Var "HI") (ConcreteBuf code), [])

          -- we pass in the above initCode buffer as calldata, and then copy
          -- it into memory before calling Create
          runtimecode = RuntimeCode (SymbolicRuntimeCode $ assemble
              [ OpPush (Lit 0x85)
              , OpPush (Lit 0x0)
              , OpPush (Lit 0x0)
              , OpCalldatacopy
              , OpPush (Lit 0x85)
              , OpPush (Lit 0x0)
              , OpPush (Lit 0x0)
              , OpCreate
              ])
        withSolvers Z3 1 Nothing $ \s -> do
          vm <- liftIO $ stToIO $ loadSymVM runtimecode (Lit 0) initCode False
          expr <- Expr.simplify <$> interpret (Fetch.oracle s Nothing) Nothing 1 StackBased vm runExpr
          case expr of
            Partial _ _ (JumpIntoSymbolicCode _ _) -> assertBoolM "" True
            _ -> assertBoolM "did not encounter expected partial node" False
    ]
  , testGroup "Dapp-Tests"
    [ test "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "DappTools" $ do
        -- quick smokecheck to make sure that we can parse dapptools style build outputs
        let cases =
              [ ("test/contracts/pass/trivial.sol", ".*", True)
              , ("test/contracts/pass/dsProvePass.sol", "proveEasy", True)
              , ("test/contracts/fail/trivial.sol", ".*", False)
              , ("test/contracts/fail/dsProveFail.sol", "prove_add", False)
              ]
        results <- forM cases $ \(testFile, match, expected) -> do
          actual <- runSolidityTestCustom testFile match Nothing Nothing False Nothing DappTools
          pure (actual == expected)
        assertBoolM "test result" (and results)
    , test "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        runSolidityTest testFile "prove_false" >>= assertEqualM "test result" False
    , test "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "ConstantinopleMin" $ do
        let testFile = "test/contracts/pass/constantinople_min.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "prefix-check-for-dapp" $ do
        let testFile = "test/contracts/fail/check-prefix.sol"
        runSolidityTest testFile "check_trivial" >>= assertEqualM "test result" False
    , test "transfer-dapp" $ do
        let testFile = "test/contracts/pass/transfer.sol"
        runSolidityTest testFile "prove_transfer" >>= assertEqualM "should prove transfer" True
    , test "badvault-sym-branch" $ do
        let testFile = "test/contracts/fail/10_BadVault.sol"
        runSolidityTestCustom testFile "prove_BadVault_usingExploitLaunchPad"  Nothing Nothing True Nothing FoundryStdLib >>= assertEqualM "Must find counterexample" False
    , test "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        runSolidityTest testFile "prove_trivial" >>= assertEqualM "test result" False
        runSolidityTest testFile "prove_trivial_dstest" >>= assertEqualM "test result" False
        runSolidityTest testFile "prove_add" >>= assertEqualM "test result" False
        runSolidityTestCustom testFile "prove_smtTimeout" (Just 1) Nothing False Nothing Foundry >>= assertEqualM "test result" False
        runSolidityTest testFile "prove_multi" >>= assertEqualM "test result" False
        -- TODO: implement overflow checking optimizations and enable, currently this runs forever
        --runSolidityTest testFile "prove_distributivity" >>= assertEqualM "test result" False
    , test "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runSolidityTestCustom testFile "prove_loop" Nothing (Just 10) False Nothing Foundry >>= assertEqualM "test result" True
        runSolidityTestCustom testFile "prove_loop" Nothing (Just 100) False Nothing Foundry >>= assertEqualM "test result" False
    , test "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "Cheat-Codes-Fork-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodesFork.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    , test "Unwind" $ do
        let testFile = "test/contracts/pass/unwind.sol"
        runSolidityTest testFile ".*" >>= assertEqualM "test result" True
    ]
  , testGroup "max-iterations"
    [ test "concrete-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun()" []
            opts = defaultVeriOpts{ maxIter = Just 3 }
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is not partial" $ isPartial e
    , test "concrete-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun() external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < 5; i++) count++;
                return count;
              }
            }
            |]

        let sig = Just $ Sig "fun()" []
            opts = defaultVeriOpts{ maxIter = Just 6 }
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is partial" $ not $ isPartial e
    , test "symbolic-loops-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] (defaultVeriOpts{ maxIter = Just 5 })
        assertBoolM "The expression is not partial" $ Expr.containsNode isPartial e
    , test "inconsistent-paths" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- we don't ask the solver about the loop condition until we're
            -- already in an inconsistent path (i == 5, j <= 3, i < j), so we
            -- will continue looping here until we hit max iterations
            opts = defaultVeriOpts{ maxIter = Just 10, askSmtIters = 5 }
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is not partial" $ Expr.containsNode isPartial e
    , test "symbolic-loops-not-reached" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint j) external payable returns (uint) {
                require(j <= 3);
                uint count = 0;
                for (uint i = 0; i < j; i++) count++;
                return count;
              }
            }
            |]
        let sig = Just $ Sig "fun(uint256)" [AbiUIntType 256]
            -- askSmtIters is low enough here to avoid the inconsistent path
            -- conditions, so we never hit maxIters
            opts = defaultVeriOpts{ maxIter = Just 5, askSmtIters = 1 }
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBoolM "The expression is partial" $ not (Expr.containsNode isPartial e)
    ]
  , testGroup "Symbolic Addresses"
    [ test "symbolic-address-create" $ do
        let src = [i|
                  contract A {
                    constructor() payable {}
                  }
                  contract C {
                    function fun(uint256 a) external{
                      require(address(this).balance > a);
                      new A{value:a}();
                    }
                  }
                  |]
        Just a <- solcRuntime "A" src
        Just c <- solcRuntime "C" src
        let sig = Sig "fun(uint256)" [AbiUIntType 256]
        (expr, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s c (Just sig) [] defaultVeriOpts Nothing Nothing
        let isSuc (Success {}) = True
            isSuc _ = False
        case filter isSuc (flattenExpr expr) of
          [Success _ _ _ store] -> do
            let ca = fromJust (Map.lookup (SymAddr "freshSymAddr1") store)
            let code = case ca.code of
                  RuntimeCode (ConcreteRuntimeCode c') -> c'
                  _ -> internalError "expected concrete code"
            assertEqualM "balance mismatch" (Var "arg1") ca.balance
            assertEqualM "code mismatch" (stripBytecodeMetadata a) (stripBytecodeMetadata code)
            assertEqualM "nonce mismatch" (Just 1) ca.nonce
          _ -> assertBoolM "too many success nodes!" False
    , test "symbolic-balance-call" $ do
        let src = [i|
                  contract A {
                    function f() public payable returns (uint) {
                      return msg.value;
                    }
                  }
                  contract C {
                    function fun(uint256 x) external {
                      require(address(this).balance > x);
                      A a = new A();
                      uint res = a.f{value:x}();
                      assert(res == x);
                    }
                  }
                  |]
        Just c <- solcRuntime "C" src
        res <- reachableUserAsserts c Nothing
        assertBoolM "unexpected cex" (isRight res)
    -- TODO: implement missing aliasing rules
    , expectFail $ test "deployed-contract-addresses-cannot-alias" $ do
        Just c <- solcRuntime "C"
          [i|
            contract A {}
            contract C {
              function f() external {
                A a = new A();
                if (address(a) == address(this)) assert(false);
              }
            }
          |]
        res <- reachableUserAsserts c Nothing
        assertBoolM "should not be able to alias" (isRight res)
    , test "addresses-in-args-can-alias-anything" $ do
        let addrs :: [Text]
            addrs = ["address(this)", "tx.origin", "block.coinbase", "msg.sender"]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract C {
                             function f(address a) external {
                               if (${vs} == a) assert(false);
                             }
                           }
                         |]

        [self, origin, coinbase, caller] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a = (Map.lookup (SymAddr "arg1") as) @?= (Map.lookup a as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check coinbase (SymAddr "coinbase")
          check caller (SymAddr "caller")
    , test "addresses-in-args-can-alias-themselves" $ do
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function f(address a, address b) external {
                if (a == b) assert(false);
              }
            }
          |]
        let sig = Just $ Sig "f(address,address)" [AbiAddressType,AbiAddressType]
        Left [cex] <- reachableUserAsserts c sig
        let arg1 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
            arg2 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
        assertEqualM "should match" arg1 arg2
    -- TODO: fails due to missing aliasing rules
    , expectFail $ test "tx.origin cannot alias deployed contracts" $ do
        Just c <- solcRuntime "C"
          [i|
            contract A {}
            contract C {
              function f() external {
                address a = address(new A());
                if (tx.origin == a) assert(false);
              }
            }
          |]
        cexs <- reachableUserAsserts c Nothing
        assertBoolM "unexpected cex" (isRight cexs)
    , test "tx.origin can alias everything else" $ do
        let addrs = ["address(this)", "block.coinbase", "msg.sender", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract C {
                             function f(address arg) external {
                               if (${vs} == tx.origin) assert(false);
                             }
                           }
                         |]

        [self, coinbase, caller, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a = (Map.lookup (SymAddr "origin") as) @?= (Map.lookup a as)
          check self (SymAddr "entrypoint")
          check coinbase (SymAddr "coinbase")
          check caller (SymAddr "caller")
          check arg (SymAddr "arg1")
    , test "coinbase can alias anything" $ do
        let addrs = ["address(this)", "tx.origin", "msg.sender", "a", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract A {}
                           contract C {
                             function f(address arg) external {
                               address a = address(new A());
                               if (${vs} == block.coinbase) assert(false);
                             }
                           }
                         |]

        [self, origin, caller, a, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a' = (Map.lookup (SymAddr "coinbase") as) @?= (Map.lookup a' as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check caller (SymAddr "caller")
          check a (SymAddr "freshSymAddr1")
          check arg (SymAddr "arg1")
    , test "caller can alias anything" $ do
        let addrs = ["address(this)", "tx.origin", "block.coinbase", "a", "arg"] :: [Text]
            sig = Just $ Sig "f(address)" [AbiAddressType]
            checkVs vs = [i|
                           contract A {}
                           contract C {
                             function f(address arg) external {
                               address a = address(new A());
                               if (${vs} == msg.sender) assert(false);
                             }
                           }
                         |]

        [self, origin, coinbase, a, arg] <- forM addrs $ \addr -> do
          Just c <- solcRuntime "C" (checkVs addr)
          Left [cex] <- reachableUserAsserts c sig
          pure cex.addrs

        liftIO $ do
          let check as a' = (Map.lookup (SymAddr "caller") as) @?= (Map.lookup a' as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check coinbase (SymAddr "coinbase")
          check a (SymAddr "freshSymAddr1")
          check arg (SymAddr "arg1")
    , test "vm.load fails for a potentially aliased address" $ do
        Just c <- solcRuntime "C"
          [i|
            interface Vm {
              function load(address,bytes32) external;
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.load(msg.sender, 0x0);
              }
            }
          |]
        (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (Just $ checkBadCheatCode "load(address,bytes32)")
        pure ()
    , test "vm.store fails for a potentially aliased address" $ do
        Just c <- solcRuntime "C"
          [i|
            interface Vm {
                function store(address,bytes32,bytes32) external;
            }
            contract C {
              function f() external {
                Vm vm = Vm(0x7109709ECfa91a80626fF3989D68f67F5b1DD12D);
                vm.store(msg.sender, 0x0, 0x0);
              }
            }
          |]
        (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s c Nothing [] defaultVeriOpts Nothing (Just $ checkBadCheatCode "store(address,bytes32,bytes32)")
        pure ()
    -- TODO: make this work properly
    , test "transfering-eth-does-not-dealias" $ do
        Just c <- solcRuntime "C"
          [i|
            // we can't do calls to unknown code yet so we use selfdestruct
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }
            contract C {
              function f() external {
                uint preSender = msg.sender.balance;
                uint preOrigin = tx.origin.balance;

                new Send{value:10}(payable(msg.sender));
                new Send{value:5}(payable(tx.origin));

                if (msg.sender == tx.origin) {
                  assert(preSender == preOrigin
                      && msg.sender.balance == preOrigin + 15
                      && tx.origin.balance == preSender + 15);
                } else {
                  assert(msg.sender.balance == preSender + 10
                      && tx.origin.balance == preOrigin + 5);
                }
              }
            }
          |]
        Right e <- reachableUserAsserts c Nothing
        -- TODO: this should work one day
        assertBoolM "should be partial" (Expr.containsNode isPartial e)
    , test "addresses-in-context-are-symbolic" $ do
        Just a <- solcRuntime "A"
          [i|
            contract A {
              function f() external {
                assert(msg.sender != address(0x0));
              }
            }
          |]
        Just b <- solcRuntime "B"
          [i|
            contract B {
              function f() external {
                assert(block.coinbase != address(0x1));
              }
            }
          |]
        Just c <- solcRuntime "C"
          [i|
            contract C {
              function f() external {
                assert(tx.origin != address(0x2));
              }
            }
          |]
        Just d <- solcRuntime "D"
          [i|
            contract D {
              function f() external {
                assert(address(this) != address(0x3));
              }
            }
          |]
        [acex,bcex,ccex,dcex] <- forM [a,b,c,d] $ \con -> do
          Left [cex] <- reachableUserAsserts con Nothing
          assertEqualM "wrong number of addresses" 1 (length (Map.keys cex.addrs))
          pure cex

        assertEqualM "wrong model for a" (Addr 0) (fromJust $ Map.lookup (SymAddr "caller") acex.addrs)
        assertEqualM "wrong model for b" (Addr 1) (fromJust $ Map.lookup (SymAddr "coinbase") bcex.addrs)
        assertEqualM "wrong model for c" (Addr 2) (fromJust $ Map.lookup (SymAddr "origin") ccex.addrs)
        assertEqualM "wrong model for d" (Addr 3) (fromJust $ Map.lookup (SymAddr "entrypoint") dcex.addrs)
    ]
  , testGroup "Symbolic execution"
      [
     test "require-test" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 a) external pure {
              require(a <= 0);
              assert (a <= 0);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256)" [AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "Require works as expected"
     ,
     -- here test
     test "ITE-with-bitwise-AND" $ do
       Just c <- solcRuntime "C"
         [i|
         contract C {
           function f(uint256 x) public pure {
             require(x > 0);
             uint256 a = (x & 8);
             bool w;
             // assembly is needed here, because solidity doesn't allow uint->bool conversion
             assembly {
                 w:=a
             }
             if (!w) assert(false); //we should get a CEX: when x has a 0 at bit 3
           }
         }
         |]
       -- should find a counterexample
       (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       putStrLnM "expected counterexample found"
     ,
     test "ITE-with-bitwise-OR" $ do
       Just c <- solcRuntime "C"
         [i|
         contract C {
           function f(uint256 x) public pure {
             uint256 a = (x | 8);
             bool w;
             // assembly is needed here, because solidity doesn't allow uint->bool conversion
             assembly {
                 w:=a
             }
             assert(w); // due to bitwise OR with positive value, this must always be true
           }
         }
         |]
       (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       putStrLnM "this should always be true, due to bitwise OR with positive value"
    ,
    -- CopySlice check
    -- uses identity precompiled contract (0x4) to copy memory
    -- checks 9af114613075a2cd350633940475f8b6699064de (readByte + CopySlice had src/dest mixed up)
    -- without 9af114613 it dies with: `Exception: UnexpectedSymbolicArg 296 "MSTORE index"`
    --       TODO: check  9e734b9da90e3e0765128b1f20ce1371f3a66085 (bufLength + copySlice was off by 1)
    test "copyslice-check" $ do
      Just c <- solcRuntime "C"
        [i|
        contract C {
          function checkval(uint8 a) public {
            bytes memory data = new bytes(5);
            for(uint i = 0; i < 5; i++) data[i] = bytes1(a);
            bytes memory ret = new bytes(data.length);
            assembly {
                let len := mload(data)
                if iszero(call(0xff, 0x04, 0, add(data, 0x20), len, add(ret,0x20), len)) {
                    invalid()
                }
            }
            for(uint i = 0; i < 5; i++) assert(ret[i] == data[i]);
          }
        }
        |]
      let sig = Just (Sig "checkval(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
        checkAssert s defaultPanicCodes c sig [] defaultVeriOpts
      putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
     ,
     test "opcode-mul-assoc" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 a, int256 b, int256 c) external pure {
              int256 tmp1;
              int256 out1;
              int256 tmp2;
              int256 out2;
              assembly {
                tmp1 := mul(a, b)
                out1 := mul(tmp1,c)
                tmp2 := mul(b, c)
                out2 := mul(a, tmp2)
              }
              assert (out1 == out2);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256,int256)" [AbiIntType 256, AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "MUL is associative"
     ,
     -- TODO look at tests here for SAR: https://github.com/dapphub/dapptools/blob/01ef8ea418c3fe49089a44d56013d8fcc34a1ec2/src/dapp-tests/pass/constantinople.sol#L250
     test "opcode-sar-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by >= 0);
              require(val <= 0);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out <= 0);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-pos" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by >= 0);
              require(val >= 0);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out >= 0);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-fixedval-pos" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
              require(shift_by == 1);
              require(val == 64);
              assembly {
                out := sar(shift_by,val)
              }
              assert (out == 32);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-sar-fixedval-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(int256 shift_by, int256 val) external pure returns (int256 out) {
                require(shift_by == 1);
                require(val == -64);
                assembly {
                  out := sar(shift_by,val)
                }
                assert (out == -32);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(int256,int256)" [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-div-zero-1" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := div(val, 0)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "opcode-sdiv-zero-1" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := sdiv(val, 0)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "opcode-sdiv-zero-2" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := sdiv(0, val)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [Qed _])  <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "sdiv works as expected"
      ,
     test "signed-overflow-checks" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(int256 a) external returns (int256) {
                  return a + a;
              }
            }
            |]
        (_, [Cex (_, _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x11] c (Just (Sig "fun(int256)" [AbiIntType 256])) [] defaultVeriOpts
        putStrLnM "expected cex discovered"
      ,
     test "opcode-signextend-neg" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b <= 31);
                require(b >= 0);
                require(val < (1 <<(b*8)));
                require(val & (1 <<(b*8-1)) != 0); // MSbit set, i.e. negative
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                if (b == 31) assert(out == val);
                else assert(out > val);
                assert(out & (1<<254) != 0); // MSbit set, i.e. negative
              }
            }
            |]
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
     test "opcode-signextend-pos-nochop" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(val < (1 <<(b*8)));
                require(val & (1 <<(b*8-1)) == 0); // MSbit not set, i.e. positive
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == val);
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
      test "opcode-signextend-pos-chopped" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b == 0); // 1-byte
                require(val == 514); // but we set higher bits
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == 2); // chopped
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
      ,
      -- when b is too large, value is unchanged
      test "opcode-signextend-pos-b-toolarge" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val, uint8 b) external pure {
                require(b >= 31);
                uint256 out;
                assembly {
                  out := signextend(b, val)
                }
                assert (out == val);
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint8)" [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
        putStrLnM "signextend works as expected"
     ,
     test "opcode-shl" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 shift_by, uint256 val) external pure {
              require(val < (1<<16));
              require(shift_by < 16);
              uint256 out;
              assembly {
                out := shl(shift_by,val)
              }
              assert (out >= val);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "SAR works as expected"
     ,
     test "opcode-xor-cancel" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
              require(a == b);
              uint256 c;
              assembly {
                c := xor(a,b)
              }
              assert (c == 0);
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "XOR works as expected"
      ,
      test "opcode-xor-reimplement" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
              uint256 c;
              assembly {
                c := xor(a,b)
              }
              assert (c == (~(a & b)) & (a | b));
              }
             }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLnM "XOR works as expected"
      ,
      test "opcode-add-commutative" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure {
                uint256 res1;
                uint256 res2;
                assembly {
                  res1 := add(a,b)
                  res2 := add(b,a)
                }
                assert (res1 == res2);
              }
            }
            |]
        a <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        case a of
          (_, [Cex (_, ctr)]) -> do
            let x = getVar ctr "arg1"
            let y = getVar ctr "arg2"
            putStrLnM $ "y:" <> show y
            putStrLnM $ "x:" <> show x
            assertEqualM "Addition is not commutative... that's wrong" False True
          (_, [Qed _]) -> do
            putStrLnM "adding is commutative"
          _ -> internalError "Unexpected"
      ,
      test "opcode-div-res-zero-on-div-by-zero" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint16 a) external pure {
                uint16 b = 0;
                uint16 res;
                assembly {
                  res := div(a,b)
                }
                assert (res == 0);
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint16)" [AbiUIntType 16])) [] defaultVeriOpts
        putStrLnM "DIV by zero is zero"
      ,
      -- Somewhat tautological since we are asserting the precondition
      -- on the same form as the actual "requires" clause.
      test "SafeAdd success case" $ do
        Just safeAdd <- solcRuntime "SafeAdd"
          [i|
          contract SafeAdd {
            function add(uint x, uint y) public pure returns (uint z) {
                 require((z = x + y) >= x);
            }
          }
          |]
        let pre preVM = let (x, y) = case getStaticAbiArgs 2 preVM of
                                       [x', y'] -> (x', y')
                                       _ -> internalError "expected 2 args"
                        in (x .<= Expr.add x y)
                        -- TODO check if it's needed
                           .&& preVM.state.callvalue .== Lit 0
            post prestate leaf =
              let (x, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> internalError "expected 2 args"
              in case leaf of
                   Success _ _ b _ -> (ReadWord (Lit 0) b) .== (Add x y)
                   _ -> PBool True
            sig = Just (Sig "add(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s safeAdd sig [] defaultVeriOpts (Just pre) (Just post)
        putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
     ,

      test "x == y => x + y == 2 * y" $ do
        Just safeAdd <- solcRuntime "SafeAdd"
          [i|
          contract SafeAdd {
            function add(uint x, uint y) public pure returns (uint z) {
                 require((z = x + y) >= x);
            }
          }
          |]
        let pre preVM = let (x, y) = case getStaticAbiArgs 2 preVM of
                                       [x', y'] -> (x', y')
                                       _ -> internalError "expected 2 args"
                        in (x .<= Expr.add x y)
                           .&& (x .== y)
                           .&& preVM.state.callvalue .== Lit 0
            post prestate leaf =
              let (_, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> internalError "expected 2 args"
              in case leaf of
                   Success _ _ b _ -> (ReadWord (Lit 0) b) .== (Mul (Lit 2) y)
                   _ -> PBool True
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s safeAdd (Just (Sig "add(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts (Just pre) (Just post)
        putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
      ,
      test "summary storage writes" $ do
        Just c <- solcRuntime "A"
          [i|
          contract A {
            uint x;
            function f(uint256 y) public {
               unchecked {
                 x += y;
                 x += y;
               }
            }
          }
          |]
        let pre vm = Lit 0 .== vm.state.callvalue
            post prestate leaf =
              let y = case getStaticAbiArgs 1 prestate of
                        [y'] -> y'
                        _ -> error "expected 1 arg"
                  this = prestate.state.codeContract
                  prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                  prex = Expr.readStorage' (Lit 0) prestore
              in case leaf of
                Success _ _ _ postState -> let
                    poststore = (fromJust (Map.lookup this postState)).storage
                  in Expr.add prex (Expr.mul (Lit 2) y) .== (Expr.readStorage' (Lit 0) poststore)
                _ -> PBool True
            sig = Just (Sig "f(uint256)" [AbiUIntType 256])
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s c sig [] defaultVeriOpts (Just pre) (Just post)
        putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- tests how whiffValue handles Neg via application of the triple IsZero simplification rule
        -- regression test for: https://github.com/dapphub/dapptools/pull/698
        test "Neg" $ do
            let src =
                  [i|
                    object "Neg" {
                      code {
                        // Deploy the contract
                        datacopy(0, dataoffset("runtime"), datasize("runtime"))
                        return(0, datasize("runtime"))
                      }
                      object "runtime" {
                        code {
                          let v := calldataload(4)
                          if iszero(iszero(and(v, not(0xffffffffffffffffffffffffffffffffffffffff)))) {
                            invalid()
                          }
                        }
                      }
                    }
                    |]
            Just c <- liftIO $ yulRuntime "Neg" src
            (res, [Qed _]) <- withSolvers Z3 4 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "hello(address)" [AbiAddressType])) [] defaultVeriOpts
            putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "catch-storage-collisions-noproblem" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public {
                 if (x != y) {
                   assembly {
                     let newx := sub(sload(x), 1)
                     let newy := add(sload(y), 1)
                     sstore(x,newx)
                     sstore(y,newy)
                   }
                 }
              }
            }
            |]
          let pre vm = (Lit 0) .== vm.state.callvalue
              post prestate poststate =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = prestate.state.codeContract
                    prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                    prex = Expr.readStorage' x prestore
                    prey = Expr.readStorage' y prestore
                in case poststate of
                     Success _ _ _ postcs -> let
                           poststore = (fromJust (Map.lookup this postcs)).storage
                           postx = Expr.readStorage' x poststore
                           posty = Expr.readStorage' y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
              sig = Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c sig [] defaultVeriOpts (Just pre) (Just post)
          putStrLnM "Correct, this can never fail"
        ,
        -- Inspired by these `msg.sender == to` token bugs
        -- which break linearity of totalSupply.
        test "catch-storage-collisions-good" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public {
                 assembly {
                   let newx := sub(sload(x), 1)
                   let newy := add(sload(y), 1)
                   sstore(x,newx)
                   sstore(y,newy)
                 }
              }
            }
            |]
          let pre vm = (Lit 0) .== vm.state.callvalue
              post prestate leaf =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = prestate.state.codeContract
                    prestore = (fromJust (Map.lookup this prestate.env.contracts)).storage
                    prex = Expr.readStorage' x prestore
                    prey = Expr.readStorage' y prestore
                in case leaf of
                     Success _ _ _ poststate -> let
                           poststore = (fromJust (Map.lookup this poststate)).storage
                           postx = Expr.readStorage' x poststore
                           posty = Expr.readStorage' y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
              sig = Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c sig [] defaultVeriOpts (Just pre) (Just post)
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          putStrLnM $ "y:" <> show y
          putStrLnM $ "x:" <> show x
          assertEqualM "Catch storage collisions" x y
          putStrLnM "expected counterexample found"
        ,
        test "simple-assert" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo() external pure {
                assert(false);
              }
             }
            |]
          (_, [Cex (Failure _ _ (Revert msg), _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo()" [])) [] defaultVeriOpts
          assertEqualM "incorrect revert msg" msg (ConcreteBuf $ panicMsg 0x01)
        ,
        test "simple-assert-2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                assert(x != 10);
              }
             }
            |]
          (_, [(Cex (_, ctr))]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertEqualM "Must be 10" 10 $ getVar ctr "arg1"
          putStrLnM "Got 10 Cex, as expected"
        ,
        test "assert-fail-equal" $ do
          Just c <- solcRuntime "AssertFailEqual"
            [i|
            contract AssertFailEqual {
              function fun(uint256 deposit_count) external pure {
                assert(deposit_count == 0);
                assert(deposit_count == 11);
              }
             }
            |]
          (_, [Cex (_, a), Cex (_, b)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let ints = map (flip getVar "arg1") [a,b]
          assertBoolM "0 must be one of the Cex-es" $ isJust $ List.elemIndex 0 ints
          putStrLnM "expected 2 counterexamples found, one Cex is the 0 value"
        ,
        test "assert-fail-notequal" $ do
          Just c <- solcRuntime "AssertFailNotEqual"
            [i|
            contract AssertFailNotEqual {
              function fun(uint256 deposit_count) external pure {
                assert(deposit_count != 0);
                assert(deposit_count != 11);
              }
             }
            |]
          (_, [Cex (_, a), Cex (_, b)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let x = getVar a "arg1"
          let y = getVar b "arg1"
          assertBoolM "At least one has to be 0, to go through the first assert" (x == 0 || y == 0)
          putStrLnM "expected 2 counterexamples found."
        ,
        test "assert-fail-twoargs" $ do
          Just c <- solcRuntime "AssertFailTwoParams"
            [i|
            contract AssertFailTwoParams {
              function fun(uint256 deposit_count1, uint256 deposit_count2) external pure {
                assert(deposit_count1 != 0);
                assert(deposit_count2 != 11);
              }
             }
            |]
          (_, [Cex _, Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "expected 2 counterexamples found"
        ,
        test "assert-2nd-arg" $ do
          Just c <- solcRuntime "AssertFailTwoParams"
            [i|
            contract AssertFailTwoParams {
              function fun(uint256 deposit_count1, uint256 deposit_count2) external pure {
                assert(deposit_count2 != 666);
              }
             }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          assertEqualM "Must be 666" 666 $ getVar ctr "arg2"
          putStrLnM "Found arg2 Ctx to be 666"
        ,
        -- LSB is zeroed out, byte(31,x) takes LSB, so y==0 always holds
        test "check-lsb-msb1" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00;
                uint8 y;
                assembly { y := byte(31,x) }
                assert(y == 0);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- We zero out everything but the LSB byte. However, byte(31,x) takes the LSB byte
        -- so there is a counterexamle, where LSB of x is not zero
        test "check-lsb-msb2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0x00000000000000000000000000000000000000000000000000000000000000ff;
                uint8 y;
                assembly { y := byte(31,x) }
                assert(y == 0);
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertBoolM "last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff) > 0
          putStrLnM "Expected counterexample found"
        ,
        -- We zero out everything but the 2nd LSB byte. However, byte(31,x) takes the 2nd LSB byte
        -- so there is a counterexamle, where 2nd LSB of x is not zero
        test "check-lsb-msb3 -- 2nd byte" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0x000000000000000000000000000000000000000000000000000000000000ff00;
                uint8 y;
                assembly { y := byte(30,x) }
                assert(y == 0);
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertBoolM "second to last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff00) > 0
          putStrLnM "Expected counterexample found"
        ,
        -- Reverse of test above
        test "check-lsb-msb4 2nd byte rev" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                x &= 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff;
                uint8 y;
                assembly {
                    y := byte(30,x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- Bitwise OR operation test
        test "opcode-bitwise-or-full-1s" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                uint256 y;
                uint256 z = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff;
                assembly { y := or(x, z) }
                assert(y == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff);
              }
            }
            |]
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "When OR-ing with full 1's we should get back full 1's"
        ,
        -- Bitwise OR operation test
        test "opcode-bitwise-or-byte-of-1s" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                uint256 y;
                uint256 z = 0x000000000000000000000000000000000000000000000000000000000000ff00;
                assembly { y := or(x, z) }
                assert((y & 0x000000000000000000000000000000000000000000000000000000000000ff00) ==
                  0x000000000000000000000000000000000000000000000000000000000000ff00);
              }
            }
            |]
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "When OR-ing with a byte of 1's, we should get 1's back there"
        ,
        test "Deposit contract loop (z3)" $ do
          Just c <- solcRuntime "Deposit"
            [i|
            contract Deposit {
              function deposit(uint256 deposit_count) external pure {
                require(deposit_count < 2**32 - 1);
                ++deposit_count;
                bool found = false;
                for (uint height = 0; height < 32; height++) {
                  if ((deposit_count & 1) == 1) {
                    found = true;
                    break;
                  }
                 deposit_count = deposit_count >> 1;
                 }
                assert(found);
              }
             }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "deposit(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "Deposit-contract-loop-error-version" $ do
          Just c <- solcRuntime "Deposit"
            [i|
            contract Deposit {
              function deposit(uint8 deposit_count) external pure {
                require(deposit_count < 2**32 - 1);
                ++deposit_count;
                bool found = false;
                for (uint height = 0; height < 32; height++) {
                  if ((deposit_count & 1) == 1) {
                    found = true;
                    break;
                  }
                 deposit_count = deposit_count >> 1;
                 }
                assert(found);
              }
             }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s allPanicCodes c (Just (Sig "deposit(uint8)" [AbiUIntType 8])) [] defaultVeriOpts
          assertEqualM "Must be 255" 255 $ getVar ctr "arg1"
          putStrLnM  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
        ,
        test "explore function dispatch" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x) public pure returns (uint) {
                return x;
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "check-asm-byte-in-bounds" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 idx, uint256 val) external pure {
                uint256 actual;
                uint256 expected;
                require(idx < 32);
                assembly {
                  actual := byte(idx,val)
                  expected := shr(248, shl(mul(idx, 8), val))
                }
                assert(actual == expected);
              }
            }
            |]
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM "in bounds byte reads return the expected value"
        ,
        test "check-div-mod-sdiv-smod-by-zero-constant-prop" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 e) external pure {
                uint x = 0;
                uint y = 55;
                uint z;
                assembly { z := div(y,x) }
                assert(z == 0);
                assembly { z := div(x,y) }
                assert(z == 0);
                assembly { z := sdiv(y,x) }
                assert(z == 0);
                assembly { z := sdiv(x,y) }
                assert(z == 0);
                assembly { z := mod(y,x) }
                assert(z == 0);
                assembly { z := mod(x,y) }
                assert(z == 0);
                assembly { z := smod(y,x) }
                assert(z == 0);
                assembly { z := smod(x,y) }
                assert(z == 0);
              }
            }
            |]
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "div/mod/sdiv/smod by zero works as expected during constant propagation"
        ,
        test "check-asm-byte-oob" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x, uint256 y) external pure {
                uint256 z;
                require(x >= 32);
                assembly { z := byte(x,y) }
                assert(z == 0);
              }
            }
            |]
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM "oob byte reads always return 0"
        ,
        test "injectivity of keccak (diff sizes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint128 x, uint256 y) external pure {
                assert(
                    keccak256(abi.encodePacked(x)) !=
                    keccak256(abi.encodePacked(y))
                );
              }
            }
            |]
          Right _ <- reachableUserAsserts c (Just $ Sig "f(uint128,uint256)" [AbiUIntType 128, AbiUIntType 256])
          pure ()
        ,
        test "injectivity of keccak (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public pure {
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))) assert(x == y);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "injectivity of keccak contrapositive (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public pure {
                require (x != y);
                assert (keccak256(abi.encodePacked(x)) != keccak256(abi.encodePacked(y)));
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "injectivity of keccak (64 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y, uint w, uint z) public pure {
                assert (keccak256(abi.encodePacked(x,y)) != keccak256(abi.encodePacked(w,z)));
              }
            }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256,uint256,uint256)" (replicate 4 (AbiUIntType 256)))) [] defaultVeriOpts
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          let w = getVar ctr "arg3"
          let z = getVar ctr "arg4"
          assertEqualM "x==y for hash collision" x y
          assertEqualM "w==z for hash collision" w z
          putStrLnM "expected counterexample found"
        ,
        test "calldata beyond calldatasize is 0 (symbolic calldata)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f() public pure {
                uint y;
                assembly {
                  let x := calldatasize()
                  y := calldataload(x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "calldata beyond calldatasize is 0 (concrete dalldata prefix)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint256 z) public pure {
                uint y;
                assembly {
                  let x := calldatasize()
                  y := calldataload(x)
                }
                assert(y == 0);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "calldata symbolic access" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint256 z) public pure {
                uint x; uint y;
                assembly {
                  y := calldatasize()
                }
                require(z >= y);
                assembly {
                  x := calldataload(z)
                }
                assert(x == 0);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "multiple-contracts" $ do
          let code =
                [i|
                  contract C {
                    uint x;
                    A constant a = A(0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B);

                    function call_A() public view {
                      // should fail since x can be anything
                      assert(a.x() == x);
                    }
                  }
                  contract A {
                    uint public x;
                  }
                |]
              aAddr = LitAddr (Addr 0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B)
              cAddr = SymAddr "entrypoint"
          Just c <- solcRuntime "C" code
          Just a <- solcRuntime "A" code
          (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $ \s -> do
            vm <- liftIO $ stToIO $ abstractVM (mkCalldata (Just (Sig "call_A()" [])) []) c Nothing False
                    <&> set (#state % #callvalue) (Lit 0)
                    <&> over (#env % #contracts)
                       (Map.insert aAddr (initialContract (RuntimeCode (ConcreteRuntimeCode a))))
            verify s defaultVeriOpts vm (Just $ checkAssertions defaultPanicCodes)

          let storeCex = cex.store
              testCex = case (Map.lookup cAddr storeCex, Map.lookup aAddr storeCex) of
                          (Just sC, Just sA) -> case (Map.lookup 0 sC, Map.lookup 0 sA) of
                              (Just x, Just y) -> x /= y
                              (Just x, Nothing) -> x /= 0
                              _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "expected counterexample found"
        ,
        expectFail $ test "calling unique contracts (read from storage)" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                uint x;
                A a;

                function call_A() public {
                  a = new A();
                  // should fail since x can be anything
                  assert(a.x() == x);
                }
              }
              contract A {
                uint public x;
              }
            |]
          (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "call_A()" [])) [] defaultVeriOpts
          putStrLnM "expected counterexample found"
        ,
        test "keccak-concrete-and-sym-agree" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function kecc(uint x) public pure {
                  if (x == 0) {
                    assert(keccak256(abi.encode(x)) == keccak256(abi.encode(0)));
                  }
                }
              }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "keccak-concrete-and-sym-agree-nonzero" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function kecc(uint x) public pure {
                  if (x == 55) {
                    // Note: 3014... is the encode & keccak & uint256 conversion of 55
                    assert(uint256(keccak256(abi.encode(x))) == 30148980456718914367279254941528755963179627010946392082519497346671089299886);
                  }
                }
              }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "kecc(uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "keccak concrete and sym injectivity" $ do
          Just c <- solcRuntime "A"
            [i|
              contract A {
                function f(uint x) public pure {
                  if (x !=3) assert(keccak256(abi.encode(x)) != keccak256(abi.encode(3)));
                }
              }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        test "safemath-distributivity-yul" $ do
          let yulsafeDistributivity = hex "6355a79a6260003560e01c14156016576015601f565b5b60006000fd60a1565b603d602d604435600435607c565b6039602435600435607c565b605d565b6052604b604435602435605d565b600435607c565b141515605a57fe5b5b565b6000828201821115151560705760006000fd5b82820190505b92915050565b6000818384048302146000841417151560955760006000fd5b82820290505b92915050565b"
          vm <- liftIO $ stToIO $ abstractVM (mkCalldata (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) []) yulsafeDistributivity Nothing False
          (_, [Qed _]) <-  withSolvers Z3 1 Nothing $ \s -> verify s defaultVeriOpts vm (Just $ checkAssertions defaultPanicCodes)
          putStrLnM "Proven"
        ,
        test "safemath-distributivity-sol" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function distributivity(uint x, uint y, uint z) public {
                  assert(mul(x, add(y, z)) == add(mul(x, y), mul(x, z)));
                }

                function add(uint x, uint y) internal pure returns (uint z) {
                  unchecked {
                    require((z = x + y) >= x, "ds-math-add-overflow");
                    }
                }

                function mul(uint x, uint y) internal pure returns (uint z) {
                  unchecked {
                    require(y == 0 || (z = x * y) / y == x, "ds-math-mul-overflow");
                  }
                }
              }
            |]

          (_, [Qed _]) <- withSolvers Bitwuzla 1 (Just 99999999) $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLnM "Proven"
        ,
        test "storage-cex-1" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
                require(x != 0);
                require(y != 0);
                assert (x == y);
              }
            }
            |]
          (_, [(Cex (_, cex))]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let addr = SymAddr "entrypoint"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> Map.size s == 2 &&
                                    case (Map.lookup 0 s, Map.lookup 1 s) of
                                      (Just x, Just y) -> x /= y
                                      _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
        ,
        test "storage-cex-2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint[10] arr1;
              uint[10] arr2;
              function fun(uint256 a) external{
                assert (arr1[0] < arr2[a]);
              }
            }
            |]
          (_, [(Cex (_, cex))]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          let addr = SymAddr "entrypoint"
              a = getVar cex "arg1"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> case (Map.lookup 0 s, Map.lookup (10 + a) s) of
                                      (Just x, Just y) -> x >= y
                                      (Just x, Nothing) -> x > 0 -- arr1 can be Nothing, it'll then be zero
                                      _ -> False
                          Nothing -> False -- arr2 must contain an element, or it'll be 0
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
        ,
        test "storage-cex-concrete" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
                require (x != 0);
                require (y != 0);
                assert (x != y);
              }
            }
            |]
          let sig = Just (Sig "fun(uint256)" [AbiUIntType 256])
          (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $
            \s -> verifyContract s c sig [] defaultVeriOpts Nothing (Just $ checkAssertions [0x01])
          let addr = SymAddr "entrypoint"
              testCex = Map.size cex.store == 1 &&
                        case Map.lookup addr cex.store of
                          Just s -> Map.size s == 2 &&
                                    case (Map.lookup 0 s, Map.lookup 1 s) of
                                      (Just x, Just y) -> x == y
                                      _ -> False
                          _ -> False
          assertBoolM "Did not find expected storage cex" testCex
          putStrLnM "Expected counterexample found"
  ]
  , testGroup "concr-fuzz"
    [ testFuzz "fuzz-complicated-mul" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function complicated(uint x, uint y, uint z) public {
            uint a;
            uint b;
            unchecked {
              a = x * x * x * y * y * y * z;
              b = x * x * x * x * y * y * z * z;
            }
            assert(a == b);
          }
        }
        |]
      let sig = (Sig "complicated(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr)]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      let
        x = getVar ctr "arg1"
        y = getVar ctr "arg2"
        z = getVar ctr "arg3"
        a = x * x * x * y * y * y * z;
        b = x * x * x * x * y * y * z * z;
        val = a == b
      assertBoolM "Must fail" (not val)
      putStrLnM  $ "expected counterexample found, x:  " <> (show x) <> " y: " <> (show y) <> " z: " <> (show z)
      putStrLnM  $ "cex a: " <> (show a) <> " b: " <> (show b)
    , testFuzz "fuzz-stores" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items;
          function func() public {
            assert(items[5] == 0);
          }
        }
        |]
      let sig = (Sig "func()" [])
      (_, [Cex (_, ctr)]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , testFuzz "fuzz-simple-fixed-value" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items;
          function func(uint a) public {
            assert(a != 1337);
          }
        }
        |]
      let sig = (Sig "func(uint256)" [AbiUIntType 256])
      (_, [Cex (_, ctr)]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , testFuzz "fuzz-simple-fixed-value2" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function func(uint a, uint b) public {
            assert(!((a == 1337) && (b == 99)));
          }
        }
        |]
      let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr)]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexample found.  ctr: " <> (show ctr)
    , testFuzz "fuzz-simple-fixed-value3" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          function func(uint a, uint b) public {
            assert(((a != 1337) && (b != 99)));
          }
        }
        |]
      let sig = (Sig "func(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr1), Cex (_, ctr2)]) <- withSolvers Bitwuzla 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexamples found.  ctr1: " <> (show ctr1) <> " ctr2: " <> (show ctr2)
    , testFuzz "fuzz-simple-fixed-value-store1" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items;
          function func(uint a) public {
            uint f = items[2];
            assert(a != f);
          }
        }
        |]
      let sig = (Sig "func(uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex _]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexamples found"
    , testFuzz "fuzz-simple-fixed-value-store2" $ do
      Just c <- solcRuntime "MyContract"
        [i|
        contract MyContract {
          mapping(uint => uint) items;
          function func(uint a) public {
            items[0] = 1337;
            assert(a != items[0]);
          }
        }
        |]
      let sig = (Sig "func(uint256)" [AbiUIntType 256, AbiUIntType 256])
      (_, [Cex (_, ctr1)]) <- withSolvers CVC5 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just sig) [] defaultVeriOpts
      putStrLnM  $ "expected counterexamples found: " <> show ctr1
  ]
  , testGroup "simplification-working"
  [
    test "PEq-and-PNot-PEq-1" $ do
      let a = [PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "PEq-and-PNot-PEq-2" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Lit 0x539) (Var "arg1"))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "PEq-and-PNot-PEq-3" $ do
      let a = [PEq (Var "arg1") (Lit 0x539),PNeg (PEq (Var "arg1") (Lit 0x539))]
      assertEqualM "Must simplify to PBool False" (Expr.simplifyProps a) ([PBool False])
    , test "prop-simp-bool1" $ do
      let
        a = successGen [PAnd (PBool True) (PBool False)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-bool2" $ do
      let
        a = successGen [POr (PBool True) (PBool False)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-LT" $ do
      let
        a = successGen [PLT (Lit 1) (Lit 2)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-GEq" $ do
      let
        a = successGen [PGEq (Lit 1) (Lit 2)]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-multiple" $ do
      let
        a = successGen [PBool False, PBool True]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen [PBool False]) b
    , test "prop-simp-expr" $ do
      let
        a = successGen [PEq (Add (Lit 1) (Lit 2)) (Sub (Lit 4) (Lit 1))]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "prop-simp-impl" $ do
      let
        a = successGen [PImpl (PBool False) (PEq (Var "abc") (Var "bcd"))]
        b = Expr.simplify a
      assertEqualM "Must simplify down" (successGen []) b
    , test "propSimp-no-duplicate1" $ do
      let a = [PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)), PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0)]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
    , test "propSimp-no-duplicate2" $ do
      let a = [PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1")),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0)),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "must not duplicate" (length simp) (length $ List.nub simp)
    , test "full-order-prop1" $ do
      let a = [PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x539) (Var "arg1"),PNeg (PEq (Lit 0x539) (Var "arg1")),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0)),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
    , test "full-order-prop2" $ do
      let a =[PNeg (PBool False),PAnd (PGEq (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x44)) (PLT (Max (Lit 0x44) (BufLength (AbstractBuf "txdata"))) (Lit 0x10000000000000000)),PAnd (PGEq (Var "arg2") (Lit 0x0)) (PLEq (Var "arg2") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PAnd (PGEq (Var "arg1") (Lit 0x0)) (PLEq (Var "arg1") (Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),PEq (Lit 0x63) (Var "arg2"),PEq (Lit 0x539) (Var "arg1"),PEq TxValue (Lit 0x0),PLT (BufLength (AbstractBuf "txdata")) (Lit 0x10000000000000000),PEq (IsZero (Eq (Lit 0x63) (Var "arg2"))) (Lit 0x0),PEq (IsZero (Eq (Lit 0x539) (Var "arg1"))) (Lit 0x0),PNeg (PEq (IsZero TxValue) (Lit 0x0))]
      let simp = Expr.simplifyProps a
      assertEqualM "must not duplicate" simp (nubOrd simp)
      assertEqualM "We must be able to remove all duplicates" (length $ nubOrd simp) (length $ List.nub simp)
  ]
  , testGroup "equivalence-checking"
    [
      test "eq-yul-simple-cex" $ do
        Just aPrgm <- liftIO $ yul ""
          [i|
          {
            calldatacopy(0, 0, 32)
            switch mload(0)
            case 0 { }
            case 1 { }
            default { invalid() }
          }
          |]
        Just bPrgm <- liftIO $ yul ""
          [i|
          {
            calldatacopy(0, 0, 32)
            switch mload(0)
            case 0 { }
            case 2 { }
            default { invalid() }
          }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertBoolM "Must have a difference" (any isCex a)
      ,
      test "eq-sol-exp-qed" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              function a(uint8 x) public returns (uint8 b) {
                unchecked {
                  b = x*2;
                }
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              function a(uint8 x) public returns (uint8 b) {
                unchecked {
                  b = x<<1;
                }
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertEqualM "Must have no difference" [Qed ()] a
      ,
      test "eq-balance-differs" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }
            contract C {
              function f() public {
                new Send{value:2}(payable(address(0x0)));
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }
            contract C {
              function f() public {
                new Send{value:1}(payable(address(0x0)));
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertBoolM "Must differ" (all isCex a)
      ,
      -- TODO: this fails because we don't check equivalence of deployed contracts
      expectFail $ test "eq-handles-contract-deployment" $ do
        Just aPrgm <- solcRuntime "B"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }

            contract A {
              address parent;
              constructor(address p) {
                parent = p;
              }
              function evil() public {
                parent.call(abi.encode(B.drain.selector));
              }
            }

            contract B {
              address child;
              function a() public {
                child = address(new A(address(this)));
              }
              function drain() public {
                require(msg.sender == child);
                new Send{value: address(this).balance}(payable(address(0x0)));
              }
            }
          |]
        Just bPrgm <- solcRuntime "D"
          [i|
            contract Send {
              constructor(address payable dst) payable {
                selfdestruct(dst);
              }
            }

            contract C {
              address parent;
              constructor(address p) {
                  parent = p;
              }
            }

            contract D {
              address child;
              function a() public {
                child = address(new C(address(this)));
              }
              function drain() public {
                require(msg.sender == child);
                new Send{value: address(this).balance}(payable(address(0x0)));
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertBoolM "Must differ" (all isCex a)
      ,
      test "eq-unknown-addr" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              address addr;
              function a(address a, address b) public {
                addr = a;
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              address addr;
              function a(address a, address b) public {
                addr = b;
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          let cd = mkCalldata (Just (Sig "a(address,address)" [AbiAddressType, AbiAddressType])) []
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts cd
          assertEqualM "Must be different" (any isCex a) True
      ,
      test "eq-sol-exp-cex" $ do
        Just aPrgm <- solcRuntime "C"
            [i|
              contract C {
                function a(uint8 x) public returns (uint8 b) {
                  unchecked {
                    b = x*2+1;
                  }
                }
              }
            |]
        Just bPrgm <- solcRuntime "C"
          [i|
              contract C {
                function a(uint8 x) public returns (uint8 b) {
                  unchecked {
                    b =  x<<1;
                  }
                }
              }
          |]
        withSolvers Bitwuzla 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertEqualM "Must be different" (any isCex a) True
      , test "eq-all-yul-optimization-tests" $ do
        let opts = defaultVeriOpts{ maxIter = Just 5, askSmtIters = 20, loopHeuristic = Naive }
            ignoredTests =
                    -- unbounded loop --
                    [ "commonSubexpressionEliminator/branches_for.yul"
                    , "conditionalSimplifier/no_opt_if_break_is_not_last.yul"
                    , "conditionalUnsimplifier/no_opt_if_break_is_not_last.yul"
                    , "expressionSimplifier/inside_for.yul"
                    , "forLoopConditionIntoBody/cond_types.yul"
                    , "forLoopConditionIntoBody/simple.yul"
                    , "fullSimplify/inside_for.yul"
                    , "fullSuite/no_move_loop_orig.yul"
                    , "loopInvariantCodeMotion/multi.yul"
                    , "redundantAssignEliminator/for_deep_simple.yul"
                    , "unusedAssignEliminator/for_deep_noremove.yul"
                    , "unusedAssignEliminator/for_deep_simple.yul"
                    , "ssaTransform/for_def_in_init.yul"
                    , "loopInvariantCodeMotion/simple_state.yul"
                    , "loopInvariantCodeMotion/simple.yul"
                    , "loopInvariantCodeMotion/recursive.yul"
                    , "loopInvariantCodeMotion/no_move_staticall_returndatasize.yul"
                    , "loopInvariantCodeMotion/no_move_state_loop.yul"
                    , "loopInvariantCodeMotion/no_move_state.yul" -- not infinite, but rollaround on a large int
                    , "loopInvariantCodeMotion/no_move_loop.yul"

                    -- infinite recursion
                    , "unusedStoreEliminator/function_side_effects_2.yul"
                    , "unusedStoreEliminator/write_before_recursion.yul"
                    , "fullInliner/multi_fun_callback.yul"
                    , "conditionalUnsimplifier/side_effects_of_functions.yul"
                    , "expressionInliner/double_recursive_calls.yul"
                    , "conditionalSimplifier/side_effects_of_functions.yul"

                    -- unexpected symbolic arg --

                    -- OpCreate2
                    , "expressionSimplifier/create2_and_mask.yul"

                    -- OpCreate
                    , "expressionSimplifier/create_and_mask.yul"
                    , "expressionSimplifier/large_byte_access.yul"

                    -- OpMload
                    , "yulOptimizerTests/expressionSplitter/inside_function.yul"
                    , "fullInliner/double_inline.yul"
                    , "fullInliner/inside_condition.yul"
                    , "fullInliner/large_function_multi_use.yul"
                    , "fullInliner/large_function_single_use.yul"
                    , "fullInliner/no_inline_into_big_global_context.yul"
                    , "fullSimplify/invariant.yul"
                    , "fullSuite/abi_example1.yul"
                    , "ssaAndBack/for_loop.yul"
                    , "ssaAndBack/multi_assign_multi_var_if.yul"
                    , "ssaAndBack/multi_assign_multi_var_switch.yul"
                    , "ssaAndBack/two_vars.yul"
                    , "ssaTransform/multi_assign.yul"
                    , "ssaTransform/multi_decl.yul"
                    , "expressionSplitter/inside_function.yul"
                    , "fullSuite/ssaReverseComplex.yul"

                    -- OpMstore
                    , "commonSubexpressionEliminator/function_scopes.yul"
                    , "commonSubexpressionEliminator/variable_for_variable.yul"
                    , "expressionSplitter/trivial.yul"
                    , "fullInliner/multi_return.yul"
                    , "fullSimplify/constant_propagation.yul"
                    , "fullSimplify/identity_rules_complex.yul"
                    , "fullSuite/medium.yul"
                    , "loadResolver/memory_with_msize.yul"
                    , "loadResolver/merge_known_write.yul"
                    , "loadResolver/merge_known_write_with_distance.yul"
                    , "loadResolver/merge_unknown_write.yul"
                    , "loadResolver/reassign_value_expression.yul"
                    , "loadResolver/second_mstore_with_delta.yul"
                    , "loadResolver/second_store_with_delta.yul"
                    , "loadResolver/simple.yul"
                    , "loadResolver/simple_memory.yul"
                    , "fullSuite/ssaReverse.yul"
                    , "rematerialiser/cheap_caller.yul"
                    , "rematerialiser/non_movable_instruction.yul"
                    , "rematerialiser/for_break.yul"
                    , "rematerialiser/for_continue.yul"
                    , "rematerialiser/for_continue_2.yul"
                    , "ssaAndBack/multi_assign.yul"
                    , "ssaAndBack/multi_assign_if.yul"
                    , "ssaAndBack/multi_assign_switch.yul"
                    , "ssaAndBack/simple.yul"
                    , "ssaReverser/simple.yul"
                    , "loopInvariantCodeMotion/simple_storage.yul"

                    -- OpMstore8
                    , "loadResolver/memory_with_different_kinds_of_invalidation.yul"

                    -- OpRevert
                    , "ssaAndBack/ssaReverse.yul"
                    , "redundantAssignEliminator/for_continue_3.yul"
                    , "controlFlowSimplifier/terminating_for_revert.yul"

                    -- invalid test --
                    -- https://github.com/ethereum/solidity/issues/9500
                    , "commonSubexpressionEliminator/object_access.yul"
                    , "expressionSplitter/object_access.yul"
                    , "fullSuite/stack_compressor_msize.yul"

                    -- stack too deep --
                    , "fullSuite/abi2.yul"
                    , "fullSuite/aztec.yul"
                    , "stackCompressor/inlineInBlock.yul"
                    , "stackCompressor/inlineInFunction.yul"
                    , "stackCompressor/unusedPrunerWithMSize.yul"
                    , "wordSizeTransform/function_call.yul"
                    , "fullInliner/no_inline_into_big_function.yul"
                    , "controlFlowSimplifier/switch_only_default.yul"
                    , "stackLimitEvader" -- all that are in this subdirectory

                    -- wrong number of args --
                    , "wordSizeTransform/functional_instruction.yul"
                    , "wordSizeTransform/if.yul"
                    , "wordSizeTransform/or_bool_renamed.yul"
                    , "wordSizeTransform/switch_1.yul"
                    , "wordSizeTransform/switch_2.yul"
                    , "wordSizeTransform/switch_3.yul"
                    , "wordSizeTransform/switch_4.yul"
                    , "wordSizeTransform/switch_5.yul"
                    , "unusedFunctionParameterPruner/too_many_arguments.yul"

                    -- typed yul --
                    , "conditionalSimplifier/add_correct_type_wasm.yul"
                    , "conditionalSimplifier/add_correct_type.yul"
                    , "disambiguator/for_statement.yul"
                    , "disambiguator/funtion_call.yul"
                    , "disambiguator/if_statement.yul"
                    , "disambiguator/long_names.yul"
                    , "disambiguator/switch_statement.yul"
                    , "disambiguator/variables_clash.yul"
                    , "disambiguator/variables_inside_functions.yul"
                    , "disambiguator/variables.yul"
                    , "expressionInliner/simple.yul"
                    , "expressionInliner/with_args.yul"
                    , "expressionSplitter/typed.yul"
                    , "fullInliner/multi_return_typed.yul"
                    , "functionGrouper/empty_block.yul"
                    , "functionGrouper/multi_fun_mixed.yul"
                    , "functionGrouper/nested_fun.yul"
                    , "functionGrouper/single_fun.yul"
                    , "functionHoister/empty_block.yul"
                    , "functionHoister/multi_mixed.yul"
                    , "functionHoister/nested.yul"
                    , "functionHoister/single.yul"
                    , "mainFunction/empty_block.yul"
                    , "mainFunction/multi_fun_mixed.yul"
                    , "mainFunction/nested_fun.yul"
                    , "mainFunction/single_fun.yul"
                    , "ssaTransform/typed_for.yul"
                    , "ssaTransform/typed_switch.yul"
                    , "ssaTransform/typed.yul"
                    , "varDeclInitializer/typed.yul"

                    -- New: symbolic index on MSTORE/MLOAD/CopySlice/CallDataCopy/ExtCodeCopy/Revert,
                    --      or exponent is symbolic (requires symbolic gas)
                    --      or SHA3 offset symbolic
                    , "blockFlattener/basic.yul"
                    , "commonSubexpressionEliminator/case2.yul"
                    , "equalStoreEliminator/indirect_inferrence.yul"
                    , "expressionJoiner/reassignment.yul"
                    , "expressionSimplifier/exp_simplifications.yul"
                    , "expressionSimplifier/zero_length_read.yul"
                    , "expressionSimplifier/side_effects_in_for_condition.yul"
                    , "fullSuite/create_and_mask.yul"
                    , "fullSuite/unusedFunctionParameterPruner_return.yul"
                    , "fullSuite/unusedFunctionParameterPruner_simple.yul"
                    , "fullSuite/unusedFunctionParameterPruner.yul"
                    , "loadResolver/double_mload_with_other_reassignment.yul"
                    , "loadResolver/double_mload_with_reassignment.yul"
                    , "loadResolver/double_mload.yul"
                    , "loadResolver/keccak_reuse_basic.yul"
                    , "loadResolver/keccak_reuse_expr_mstore.yul"
                    , "loadResolver/keccak_reuse_msize.yul"
                    , "loadResolver/keccak_reuse_mstore.yul"
                    , "loadResolver/keccak_reuse_reassigned_branch.yul"
                    , "loadResolver/keccak_reuse_reassigned_value.yul"
                    , "loadResolver/keccak_symbolic_memory.yul"
                    , "loadResolver/merge_mload_with_known_distance.yul"
                    , "loadResolver/mload_self.yul"
                    , "loadResolver/keccak_reuse_in_expression.yul"
                    , "loopInvariantCodeMotion/complex_move.yul"
                    , "loopInvariantCodeMotion/move_memory_function.yul"
                    , "loopInvariantCodeMotion/move_state_function.yul"
                    , "loopInvariantCodeMotion/no_move_memory.yul"
                    , "loopInvariantCodeMotion/no_move_storage.yul"
                    , "loopInvariantCodeMotion/not_first.yul"
                    , "ssaAndBack/single_assign_if.yul"
                    , "ssaAndBack/single_assign_switch.yul"
                    , "structuralSimplifier/switch_inline_no_match.yul"
                    , "unusedFunctionParameterPruner/simple.yul"
                    , "unusedStoreEliminator/covering_calldatacopy.yul"
                    , "unusedStoreEliminator/remove_before_revert.yul"
                    , "unusedStoreEliminator/unknown_length2.yul"
                    , "unusedStoreEliminator/unrelated_relative.yul"
                    , "fullSuite/extcodelength.yul"
                    , "unusedStoreEliminator/create_inside_function.yul"-- "trying to reset symbolic storage with writes in create"

                    -- Takes too long, would timeout on most test setups.
                    -- We could probably fix these by "bunching together" queries
                    , "reasoningBasedSimplifier/mulmod.yul"
                    , "loadResolver/multi_sload_loop.yul"
                    , "reasoningBasedSimplifier/mulcheck.yul"
                    , "reasoningBasedSimplifier/smod.yul"

                    -- TODO check what's wrong with these!
                    , "loadResolver/keccak_short.yul" -- ACTUAL bug -- keccak
                    , "reasoningBasedSimplifier/signed_division.yul" -- ACTUAL bug, SDIV

                    -- started failing with 9.6 update
                    , "fullInliner/multi_fun_callback.yul"
                    , "unusedStoreEliminator/write_before_recursion.yul"
                    , "unusedStoreEliminator/function_side_effects_2.yul"
                    , "expressionInliner/double_recursive_calls.yul"
                    , "conditionalUnsimplifier/side_effects_of_functions.yul"
                    , "conditionalSimplifier/side_effects_of_functions.yul"
                    ]

        solcRepo <- liftIO $ fromMaybe (internalError "cannot find solidity repo") <$> (lookupEnv "HEVM_SOLIDITY_REPO")
        let testDir = solcRepo <> "/test/libyul/yulOptimizerTests"
        dircontents <- liftIO $ System.Directory.listDirectory testDir
        let
          fullpaths = map ((testDir ++ "/") ++) dircontents
          recursiveList :: [FilePath] -> [FilePath] -> IO [FilePath]
          recursiveList (a:ax) b =  do
              isdir <- doesDirectoryExist a
              case isdir of
                True  -> do
                    fs <- System.Directory.listDirectory a
                    let fs2 = map ((a ++ "/") ++) fs
                    recursiveList (ax++fs2) b
                False -> recursiveList ax (a:b)
          recursiveList [] b = pure b
        files <- liftIO $ recursiveList fullpaths []
        let filesFiltered = filter (\file -> not $ any (`List.isSubsequenceOf` file) ignoredTests) files

        -- Takes one file which follows the Solidity Yul optimizer unit tests format,
        -- extracts both the nonoptimized and the optimized versions, and checks equivalence.
        forM_ filesFiltered (\f-> do
          liftIO $ print f
          origcont <- liftIO $ readFile f
          let
            onlyAfter pattern (a:ax) = if a =~ pattern then (a:ax) else onlyAfter pattern ax
            onlyAfter _ [] = []
            replaceOnce pat repl inp = go inp [] where
              go (a:ax) b = if a =~ pat then let a2 = replaceAll repl $ a *=~ pat in b ++ a2:ax
                                        else go ax (b ++ [a])
              go [] b = b

            -- takes a yul program and ensures memory is symbolic by prepending
            -- `calldatacopy(0,0,1024)`. (calldata is symbolic, but memory starts empty).
            -- This forces the exploration of more branches, and makes the test vectors a
            -- little more thorough.
            symbolicMem (a:ax) = if a =~ [re|"^ *object"|] then
                                      let a2 = replaceAll "a calldatacopy(0,0,1024)" $ a *=~ [re|code {|]
                                      in (a2:ax)
                                    else replaceOnce [re|^ *{|] "{\ncalldatacopy(0,0,1024)" $ onlyAfter [re|^ *{|] (a:ax)
            symbolicMem _ = internalError "Program too short"

            unfiltered = lines origcont
            filteredASym = symbolicMem [ x | x <- unfiltered, (not $ x =~ [re|^//|]) && (not $ x =~ [re|^$|]) ]
            filteredBSym = symbolicMem [ replaceAll "" $ x *=~[re|^//|] | x <- onlyAfter [re|^// step:|] unfiltered, not $ x =~ [re|^$|] ]
          start <- liftIO $ getCurrentTime
          putStrLnM $ "Checking file: " <> f
          conf <- readConfig
          when conf.debug $ liftIO $ do
            putStrLnM "-------------Original Below-----------------"
            mapM_ putStrLn unfiltered
            putStrLnM "------------- Filtered A + Symb below-----------------"
            mapM_ putStrLn filteredASym
            putStrLnM "------------- Filtered B + Symb below-----------------"
            mapM_ putStrLn filteredBSym
            putStrLnM "------------- END -----------------"
          Just aPrgm <- liftIO $ yul "" $ T.pack $ unlines filteredASym
          Just bPrgm <- liftIO $ yul "" $ T.pack $ unlines filteredBSym
          procs <- liftIO $ getNumProcessors
          withSolvers CVC5 (unsafeInto procs) (Just 100) $ \s -> do
            res <- equivalenceCheck s aPrgm bPrgm opts (mkCalldata Nothing [])
            end <- liftIO $ getCurrentTime
            case any isCex res of
              False -> liftIO $ do
                print $ "OK. Took " <> (show $ diffUTCTime end start) <> " seconds"
                let timeouts = filter isTimeout res
                unless (null timeouts) $ do
                  putStrLnM $ "But " <> (show $ length timeouts) <> " timeout(s) occurred"
                  internalError "Encountered timeouts"
              True -> liftIO $ do
                putStrLnM $ "Not OK: " <> show f <> " Got: " <> show res
                internalError "Was NOT equivalent"
           )
    ]
  ]
  where
    (===>) = assertSolidityComputation

checkEquivProp :: App m => Prop -> Prop -> m Bool
checkEquivProp = checkEquivBase (\l r -> PNeg (PImpl l r .&& PImpl r l))

checkEquiv :: (Typeable a, App m) => Expr a -> Expr a -> m Bool
checkEquiv = checkEquivBase (./=)

checkEquivBase :: (Eq a, App m) => (a -> a -> Prop) -> a -> a -> m Bool
checkEquivBase mkprop l r = do
  conf <-  readConfig
  withSolvers Z3 1 (Just 1) $ \solvers -> liftIO $ do
    if l == r
       then do
         putStrLnM "skip"
         pure True
       else do
         let smt = assertPropsNoSimp conf [mkprop l r]
         res <- checkSat solvers smt
         print res
         pure $ case res of
           Unsat -> True
           EVM.Solvers.Unknown -> True
           Sat _ -> False
           Error _ -> False

-- | Takes a runtime code and calls it with the provided calldata

-- | Takes a creation code and some calldata, runs the creation code, and calls the resulting contract with the provided calldata
runSimpleVM :: App m => ByteString -> ByteString -> m (Maybe ByteString)
runSimpleVM x ins = do
  loadVM x >>= \case
    Nothing -> pure Nothing
    Just vm -> do
     let calldata = (ConcreteBuf ins)
         vm' = set (#state % #calldata) calldata vm
     res <- Stepper.interpret (Fetch.zero 0 Nothing) vm' Stepper.execFully
     case res of
       Right (ConcreteBuf bs) -> pure $ Just bs
       s -> internalError $ show s

-- | Takes a creation code and returns a vm with the result of executing the creation code
loadVM :: App m => ByteString -> m (Maybe (VM Concrete RealWorld))
loadVM x = do
  vm <- liftIO $ stToIO $ vmForEthrunCreation x
  vm1 <- Stepper.interpret (Fetch.zero 0 Nothing) vm Stepper.runFully
  case vm1.result of
    Just (VMSuccess (ConcreteBuf targetCode)) -> do
      let target = vm1.state.contract
      vm2 <- Stepper.interpret (Fetch.zero 0 Nothing) vm1 (prepVm target targetCode)
      writeTrace vm2
      pure $ Just vm2
    _ -> pure Nothing
  where
    prepVm target targetCode = Stepper.evm $ do
      replaceCodeOfSelf (RuntimeCode $ ConcreteRuntimeCode targetCode)
      resetState
      assign (#state % #gas) 0xffffffffffffffff -- kludge
      execState (loadContract target) <$> get >>= put
      get

hex :: ByteString -> ByteString
hex s =
  case BS16.decodeBase16Untyped s of
    Right x -> x
    Left e -> internalError $ T.unpack e

singleContract :: Text -> Text -> IO (Maybe ByteString)
singleContract x s =
  solidity x [i|
    pragma experimental ABIEncoderV2;
    contract ${x} { ${s} }
  |]

defaultDataLocation :: AbiType -> Text
defaultDataLocation t =
  if (case t of
        AbiBytesDynamicType -> True
        AbiStringType -> True
        AbiArrayDynamicType _ -> True
        AbiArrayType _ _ -> True
        _ -> False)
  then "memory"
  else ""

runFunction :: App m => Text -> ByteString -> m (Maybe ByteString)
runFunction c input = do
  x <- liftIO $ singleContract "X" c
  runSimpleVM (fromJust x) input

runStatements :: App m => Text -> [AbiValue] -> AbiType -> m (Maybe ByteString)
runStatements stmts args t = do
  let params =
        T.intercalate ", "
          (map (\(x, c) -> abiTypeSolidity (abiValueType x)
                             <> " " <> defaultDataLocation (abiValueType x)
                             <> " " <> T.pack [c])
            (zip args "abcdefg"))
      s =
        "foo(" <> T.intercalate ","
                    (map (abiTypeSolidity . abiValueType) args) <> ")"

  runFunction [i|
    function foo(${params}) public pure returns (${abiTypeSolidity t} ${defaultDataLocation t} x) {
      ${stmts}
    }
  |] (abiMethod s (AbiTuple $ V.fromList args))

getStaticAbiArgs :: Int -> VM Symbolic s -> [Expr EWord]
getStaticAbiArgs n vm =
  let cd = vm.state.calldata
  in decodeStaticArgs 4 n cd

-- includes shaving off 4 byte function sig
decodeAbiValues :: [AbiType] -> ByteString -> [AbiValue]
decodeAbiValues types bs =
  let xy = case decodeAbiValue (AbiTupleType $ V.fromList types) (BS.fromStrict (BS.drop 4 bs)) of
        AbiTuple xy' -> xy'
        _ -> internalError "AbiTuple expected"
  in V.toList xy

-- abi types that are supported in the symbolic abi encoder
newtype SymbolicAbiType = SymbolicAbiType AbiType
  deriving (Eq, Show)

newtype SymbolicAbiVal = SymbolicAbiVal AbiValue
  deriving (Eq, Show)

instance Arbitrary SymbolicAbiVal where
  arbitrary = do
    SymbolicAbiType ty <- arbitrary
    SymbolicAbiVal <$> genAbiValue ty

instance Arbitrary SymbolicAbiType where
  arbitrary = SymbolicAbiType <$> frequency
    [ (5, (AbiUIntType . (* 8)) <$> choose (1, 32))
    , (5, (AbiIntType . (* 8)) <$> choose (1, 32))
    , (5, pure AbiAddressType)
    , (5, pure AbiBoolType)
    , (5, AbiBytesType <$> choose (1,32))
    , (1, do SymbolicAbiType ty <- scale (`div` 2) arbitrary
             AbiArrayType <$> (choose (1, 30)) <*> pure ty
      )
    ]

newtype Bytes = Bytes ByteString
  deriving Eq

instance Show Bytes where
  showsPrec _ (Bytes x) _ = show (BS.unpack x)

instance Arbitrary Bytes where
  arbitrary = fmap (Bytes . BS.pack) arbitrary

newtype RLPData = RLPData RLP
  deriving (Eq, Show)

-- bias towards bytestring to try to avoid infinite recursion
instance Arbitrary RLPData where
  arbitrary = frequency
   [(5, do
           Bytes bytes <- arbitrary
           return $ RLPData $ BS bytes)
   , (1, do
         k <- choose (0,10)
         ls <- vectorOf k arbitrary
         return $ RLPData $ List [r | RLPData r <- ls])
   ]

instance Arbitrary Word128 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary Word160 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary Word256 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary W64 where
  arbitrary = fmap W64 arbitrary

instance Arbitrary W256 where
  arbitrary = fmap W256 arbitrary

instance Arbitrary Addr where
  arbitrary = fmap Addr arbitrary

instance Arbitrary (Expr EAddr) where
  arbitrary = oneof
    [ fmap LitAddr arbitrary
    , fmap SymAddr (genName "addr")
    ]

instance Arbitrary (Expr Storage) where
  arbitrary = sized genStorage

instance Arbitrary (Expr EWord) where
  arbitrary = sized defaultWord

instance Arbitrary (Expr Byte) where
  arbitrary = sized genByte

instance Arbitrary (Expr Buf) where
  arbitrary = sized defaultBuf

instance Arbitrary (Expr End) where
  arbitrary = sized genEnd

instance Arbitrary (ContractCode) where
  arbitrary = oneof
    [ fmap UnknownCode arbitrary
    , liftM2 InitCode arbitrary arbitrary
    , fmap RuntimeCode arbitrary
    ]

instance Arbitrary (RuntimeCode) where
  arbitrary = oneof
    [ fmap ConcreteRuntimeCode arbitrary
    , fmap SymbolicRuntimeCode arbitrary
    ]

instance Arbitrary (V.Vector (Expr Byte)) where
  arbitrary = fmap V.fromList (listOf1 arbitrary)

instance Arbitrary (Expr EContract) where
  arbitrary = sized genEContract

-- LitOnly
newtype LitOnly a = LitOnly a
  deriving (Show, Eq)

newtype LitWord (sz :: Nat) = LitWord (Expr EWord)
  deriving (Show)

instance (KnownNat sz) => Arbitrary (LitWord sz) where
  arbitrary = LitWord <$> genLit (fromInteger v)
    where
      v = natVal (Proxy @sz)

instance Arbitrary (LitOnly (Expr Byte)) where
  arbitrary = LitOnly . LitByte <$> arbitrary

instance Arbitrary (LitOnly (Expr EWord)) where
  arbitrary = LitOnly . Lit <$> arbitrary

instance Arbitrary (LitOnly (Expr Buf)) where
  arbitrary = LitOnly . ConcreteBuf <$> arbitrary

genEContract :: Int -> Gen (Expr EContract)
genEContract sz = do
  c <- arbitrary
  b <- defaultWord sz
  n <- arbitrary
  s <- genStorage sz
  pure $ C c s b n

-- ZeroDepthWord
newtype ZeroDepthWord = ZeroDepthWord (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary ZeroDepthWord where
  arbitrary = do
    fmap ZeroDepthWord . sized $ genWord 0

-- WriteWordBuf
newtype WriteWordBuf = WriteWordBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary WriteWordBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""       -- empty
          , fmap ConcreteBuf arbitrary  -- concrete
          , sized (genBuf 100)          -- overlapping writes
          , arbitrary                   -- sparse writes
          ]
    fmap WriteWordBuf mkBuf

-- GenCopySliceBuf
newtype GenCopySliceBuf = GenCopySliceBuf (Expr Buf)
  deriving (Show, Eq)

instance Arbitrary GenCopySliceBuf where
  arbitrary = do
    let mkBuf = oneof
          [ pure $ ConcreteBuf ""
          , fmap ConcreteBuf arbitrary
          , arbitrary
          ]
    fmap GenCopySliceBuf mkBuf

-- GenWriteStorageExpr
newtype GenWriteStorageExpr = GenWriteStorageExpr (Expr EWord, Expr Storage)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageExpr where
  arbitrary = do
    slot <- arbitrary
    let mkStore = oneof
          [ pure $ ConcreteStore mempty
          , fmap ConcreteStore arbitrary
          , do
              -- generate some write chains where we know that at least one
              -- write matches either the input addr, or both the input
              -- addr and slot
              let addWrites :: Expr Storage -> Int -> Gen (Expr Storage)
                  addWrites b 0 = pure b
                  addWrites b n = liftM3 SStore arbitrary arbitrary (addWrites b (n - 1))
              s <- arbitrary
              addMatch <- fmap (SStore slot) arbitrary
              let withMatch = addMatch s
              newWrites <- oneof [ pure 0, pure 1, fmap (`mod` 5) arbitrary ]
              addWrites withMatch newWrites
          , arbitrary
          ]
    store <- mkStore
    pure $ GenWriteStorageExpr (slot, store)

-- GenWriteByteIdx
newtype GenWriteByteIdx = GenWriteByteIdx (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteByteIdx where
  arbitrary = do
    -- 1st: can never overflow an Int
    -- 2nd: can overflow an Int
    let mkIdx = frequency [ (10, genLit 1_000_000) , (1, fmap Lit arbitrary) ]
    fmap GenWriteByteIdx mkIdx

newtype LitProp = LitProp Prop
  deriving (Show, Eq)

instance Arbitrary LitProp where
  arbitrary = LitProp <$> sized (genProp True)


newtype StorageExp = StorageExp (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary StorageExp where
  arbitrary = StorageExp <$> (genStorageExp)

genStorageExp :: Gen (Expr EWord)
genStorageExp = do
  fromPos <- genSlot
  storage <- genStorageWrites
  pure $ SLoad fromPos storage

genSlot :: Gen (Expr EWord)
genSlot = frequency [ (1, do
                        buf <- genConcreteBufSlot 64
                        case buf of
                          (ConcreteBuf b) -> do
                            key <- genLit 10
                            pure $ Expr.MappingSlot b key
                          _ -> internalError "impossible"
                        )
                     -- map element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 64
                        pure $ Add (Keccak buf) l)
                    -- Array element
                     ,(2, do
                        l <- genLit 10
                        buf <- genConcreteBufSlot 32
                        pure $ Add (Keccak buf) l)
                     -- member of the Contract
                     ,(2, pure $ Lit 20)
                     -- array element
                     ,(2, do
                        arrayNum :: Int <- arbitrary
                        offs :: W256 <- arbitrary
                        pure $ Lit $ fst (Expr.preImages !! (arrayNum `mod` 3)) + (offs `mod` 3))
                     -- random stuff
                     ,(1, pure $ Lit (maxBound :: W256))
                     ]

-- Generates an N-long buffer, all with the same value, at most 8 different ones
genConcreteBufSlot :: Int -> Gen (Expr Buf)
genConcreteBufSlot len = do
  b :: Word8 <- arbitrary
  pure $ ConcreteBuf $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b])

genStorageWrites :: Gen (Expr Storage)
genStorageWrites = do
  toSlot <- genSlot
  val <- genLit (maxBound :: W256)
  store <- frequency [ (3, pure $ AbstractStore (SymAddr "") Nothing)
                     , (2, genStorageWrites)
                     ]
  pure $ SStore toSlot val store

instance Arbitrary Prop where
  arbitrary = sized (genProp False)

genProps :: Bool -> Int -> Gen [Prop]
genProps onlyLits sz2 = listOf $ genProp onlyLits sz2

genProp :: Bool -> Int -> Gen (Prop)
genProp _ 0 = PBool <$> arbitrary
genProp onlyLits sz = oneof
  [ liftM2 PEq subWord subWord
  , liftM2 PLT subWord subWord
  , liftM2 PGT subWord subWord
  , liftM2 PLEq subWord subWord
  , liftM2 PGEq subWord subWord
  , fmap PNeg subProp
  , liftM2 PAnd subProp subProp
  , liftM2 POr subProp subProp
  , liftM2 PImpl subProp subProp
  ]
  where
    subWord = if onlyLits then frequency [(2, Lit <$> arbitrary)
                                         ,(1, pure $ Lit 0)
                                         ,(1, pure $ Lit Expr.maxLit)
                                         ]
                          else genWord 1 (sz `div` 2)
    subProp = genProp onlyLits (sz `div` 2)

genByte :: Int -> Gen (Expr Byte)
genByte 0 = fmap LitByte arbitrary
genByte sz = oneof
  [ liftM2 IndexWord subWord subWord
  , liftM2 ReadByte subWord subBuf
  ]
  where
    subWord = defaultWord (sz `div` 10)
    subBuf = defaultBuf (sz `div` 10)

genLit :: W256 -> Gen (Expr EWord)
genLit bound = do
  w <- arbitrary
  pure $ Lit (w `mod` bound)

genNat :: Gen Int
genNat = fmap unsafeInto (arbitrary :: Gen Natural)

genName :: String -> Gen Text
-- In order not to generate SMT reserved words, we prepend with "esc_"
genName ty = fmap (T.pack . (("esc_" <> ty <> "_") <> )) $ listOf1 (oneof . (fmap pure) $ ['a'..'z'] <> ['A'..'Z'])

genEnd :: Int -> Gen (Expr End)
genEnd 0 = oneof
  [ fmap (Failure mempty mempty . UnrecognizedOpcode) arbitrary
  , pure $ Failure mempty mempty IllegalOverflow
  , pure $ Failure mempty mempty SelfDestruction
  ]
genEnd sz = oneof
  [ liftM3 Failure subProp (pure mempty) (fmap Revert subBuf)
  , liftM4 Success subProp (pure mempty) subBuf arbitrary
  , liftM3 ITE subWord subEnd subEnd
  -- TODO Partial
  ]
  where
    subBuf = defaultBuf (sz `div` 2)
    subWord = defaultWord (sz `div` 2)
    subEnd = genEnd (sz `div` 2)
    subProp = genProps False (sz `div` 2)

genSmallLit :: W256 -> Gen (Expr EWord)
genSmallLit m = do
  val :: W256 <- arbitrary
  pure $ Lit (val `mod` m)

genWord :: Int -> Int -> Gen (Expr EWord)
genWord litFreq 0 = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, pure 0)
       , (1, pure Expr.maxLit)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
      [ pure Origin
      , pure Coinbase
      , pure Timestamp
      , pure BlockNumber
      , pure PrevRandao
      , pure GasLimit
      , pure ChainId
      , pure BaseFee
      --, liftM2 SelfBalance arbitrary arbitrary
      --, liftM2 Gas arbitrary arbitrary
      , fmap Lit arbitrary
      , fmap Var (genName "word")
      ]
    )
  ]
genWord litFreq sz = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
       , (1, arbitrary)
       ]
      pure $ Lit val
    )
  , (1, oneof
    [ liftM2 Add subWord subWord
    , liftM2 Sub subWord subWord
    , liftM2 Mul subWord subWord
    , liftM2 Div subWord subWord
    , liftM2 SDiv subWord subWord
    , liftM2 Mod subWord subWord
    , liftM2 SMod subWord subWord
    --, liftM3 AddMod subWord subWord subWord
    --, liftM3 MulMod subWord subWord subWord -- it works, but it's VERY SLOW
    --, liftM2 Exp subWord litWord
    , liftM2 SEx subWord subWord
    , liftM2 Min subWord subWord
    , liftM2 LT subWord subWord
    , liftM2 GT subWord subWord
    , liftM2 LEq subWord subWord
    , liftM2 GEq subWord subWord
    , liftM2 SLT subWord subWord
    --, liftM2 SGT subWord subWord
    , liftM2 Eq subWord subWord
    , fmap IsZero subWord
    , liftM2 And subWord subWord
    , liftM2 Or subWord subWord
    , liftM2 Xor subWord subWord
    , fmap Not subWord
    , liftM2 SHL subWord subWord
    , liftM2 SHR subWord subWord
    , liftM2 SAR subWord subWord
    , fmap BlockHash subWord
    --, liftM3 Balance arbitrary arbitrary subWord
    --, fmap CodeSize subWord
    --, fmap ExtCodeHash subWord
    , fmap Keccak subBuf
    , fmap SHA256 subBuf
    , liftM2 SLoad subWord subStore
    , liftM2 ReadWord subWord subBuf
    , fmap BufLength subBuf
    , do
      one <- subByte
      two <- subByte
      three <- subByte
      four <- subByte
      five <- subByte
      six <- subByte
      seven <- subByte
      eight <- subByte
      nine <- subByte
      ten <- subByte
      eleven <- subByte
      twelve <- subByte
      thirteen <- subByte
      fourteen <- subByte
      fifteen <- subByte
      sixteen <- subByte
      seventeen <- subByte
      eighteen <- subByte
      nineteen <- subByte
      twenty <- subByte
      twentyone <- subByte
      twentytwo <- subByte
      twentythree <- subByte
      twentyfour <- subByte
      twentyfive <- subByte
      twentysix <- subByte
      twentyseven <- subByte
      twentyeight <- subByte
      twentynine <- subByte
      thirty <- subByte
      thirtyone <- subByte
      thirtytwo <- subByte
      pure $ JoinBytes
        one two three four five six seven eight nine ten
        eleven twelve thirteen fourteen fifteen sixteen
        seventeen eighteen nineteen twenty twentyone
        twentytwo twentythree twentyfour twentyfive
        twentysix twentyseven twentyeight twentynine
        thirty thirtyone thirtytwo
    ])
  ]
 where
   subWord = genWord litFreq (sz `div` 5)
   subBuf = defaultBuf (sz `div` 10)
   subStore = genStorage (sz `div` 10)
   subByte = genByte (sz `div` 10)

genWordArith :: Int -> Int -> Gen (Expr EWord)
genWordArith litFreq 0 = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (1, oneof [ fmap Lit arbitrary ])
  ]
genWordArith litFreq sz = frequency
  [ (litFreq, fmap Lit arbitrary)
  , (20, frequency
    [ (20, liftM2 Add  subWord subWord)
    , (20, liftM2 Sub  subWord subWord)
    , (20, liftM2 Mul  subWord subWord)
    , (20, liftM2 SEx  subWord subWord)
    , (20, liftM2 Xor  subWord subWord)
    -- these reduce variability
    , (3 , liftM2 Min  subWord subWord)
    , (3 , liftM2 Div  subWord subWord)
    , (3 , liftM2 SDiv subWord subWord)
    , (3 , liftM2 Mod  subWord subWord)
    , (3 , liftM2 SMod subWord subWord)
    , (3 , liftM2 SHL  subWord subWord)
    , (3 , liftM2 SHR  subWord subWord)
    , (3 , liftM2 SAR  subWord subWord)
    , (3 , liftM2 Or   subWord subWord)
    -- comparisons, reducing variability greatly
    , (1 , liftM2 LEq  subWord subWord)
    , (1 , liftM2 GEq  subWord subWord)
    , (1 , liftM2 SLT  subWord subWord)
    --(1, , liftM2 SGT subWord subWord
    , (1 , liftM2 Eq   subWord subWord)
    , (1 , liftM2 And  subWord subWord)
    , (1 , fmap IsZero subWord        )
    -- Expensive below
    --(1,  liftM3 AddMod subWord subWord subWord
    --(1,  liftM3 MulMod subWord subWord subWord
    --(1,  liftM2 Exp subWord litWord
    ])
  ]
 where
   subWord = genWordArith (litFreq `div` 2) (sz `div` 2)

-- Used to check for unsimplified expressions
newtype FoundBad = FoundBad { bad :: Bool } deriving (Show)
initFoundBad :: FoundBad
initFoundBad = FoundBad { bad = False }

-- Finds SLoad -> SStore. This should not occur in most scenarios
-- as we can simplify them away
badStoresInExpr :: Expr a -> Bool
badStoresInExpr expr = bad
  where
    FoundBad bad = execState (mapExprM findBadStore expr) initFoundBad
    findBadStore :: Expr a-> State FoundBad (Expr a)
    findBadStore e = case e of
      (SLoad _ (SStore _ _ _)) -> do
        put (FoundBad { bad = True })
        pure e
      _ -> pure e

defaultBuf :: Int -> Gen (Expr Buf)
defaultBuf = genBuf (4_000_000)

defaultWord :: Int -> Gen (Expr EWord)
defaultWord = genWord 10

maybeBoundedLit :: W256 -> Gen (Expr EWord)
maybeBoundedLit bound = do
  o <- (arbitrary :: Gen (Expr EWord))
  pure $ case o of
        Lit w -> Lit $ w `mod` bound
        _ -> o

genBuf :: W256 -> Int -> Gen (Expr Buf)
genBuf _ 0 = oneof
  [ fmap AbstractBuf (genName "buf")
  , fmap ConcreteBuf arbitrary
  ]
genBuf bound sz = oneof
  [ liftM3 WriteWord (maybeBoundedLit bound) subWord subBuf
  , liftM3 WriteByte (maybeBoundedLit bound) subByte subBuf
  -- we don't generate copyslice instances where:
  --   - size is abstract
  --   - size > 100 (due to unrolling in SMT.hs)
  --   - literal dstOffsets are > 4,000,000 (due to unrolling in SMT.hs)
  -- n.b. that 4,000,000 is the theoretical maximum memory size given a 30,000,000 block gas limit
  , liftM5 CopySlice subWord (maybeBoundedLit bound) smolLitWord subBuf subBuf
  ]
  where
    -- copySlice gets unrolled in the generated SMT so we can't go too crazy here
    smolLitWord = do
      w <- arbitrary
      pure $ Lit (w `mod` 100)
    subWord = defaultWord (sz `div` 5)
    subByte = genByte (sz `div` 10)
    subBuf = genBuf bound (sz `div` 10)

genStorage :: Int -> Gen (Expr Storage)
genStorage 0 = oneof
  [ liftM2 AbstractStore arbitrary (pure Nothing)
  , fmap ConcreteStore arbitrary
  ]
genStorage sz = liftM3 SStore key val subStore
  where
    subStore = genStorage (sz `div` 10)
    val = defaultWord (sz `div` 5)
    key = genStorageKey

genStorageKey :: Gen (Expr EWord)
genStorageKey = frequency
     -- array slot
    [ (4, liftM2 Expr.ArraySlotWithOffs (genByteStringKey 32) (genSmallLit 5))
    , (4, fmap Expr.ArraySlotZero (genByteStringKey 32))
     -- mapping slot
    , (8, liftM2 Expr.MappingSlot (genByteStringKey 64) (genSmallLit 5))
     -- small slot
    , (4, genLit 20)
    -- unrecognized slot type
    , (1, genSmallLit 5)
    ]

genByteStringKey :: W256 -> Gen (ByteString)
genByteStringKey len = do
  b :: Word8 <- arbitrary
  pure $ BS.pack ([ 0 | _ <- [0..(len-2)]] ++ [b `mod` 5])

-- GenWriteStorageLoad
newtype GenWriteStorageLoad = GenWriteStorageLoad (Expr EWord)
  deriving (Show, Eq)

instance Arbitrary GenWriteStorageLoad where
  arbitrary = do
    load <- genStorageLoad 10
    pure $ GenWriteStorageLoad load

    where
      genStorageLoad :: Int -> Gen (Expr EWord)
      genStorageLoad sz = liftM2 SLoad key subStore
        where
          subStore = genStorage (sz `div` 10)
          key = genStorageKey

data Invocation
  = SolidityCall Text [AbiValue]
  deriving Show

assertSolidityComputation :: App m => Invocation -> AbiValue -> m ()
assertSolidityComputation (SolidityCall s args) x =
  do y <- runStatements s args (abiValueType x)
     liftIO $ assertEqual (T.unpack s)
       (fmap Bytes (Just (encodeAbiValue x)))
       (fmap Bytes y)

bothM :: (Monad m) => (a -> m b) -> (a, a) -> m (b, b)
bothM f (a, a') = do
  b  <- f a
  b' <- f a'
  return (b, b')

applyPattern :: String -> TestTree  -> TestTree
applyPattern p = localOption (TestPattern (parseExpr p))

checkBadCheatCode :: Text -> Postcondition s
checkBadCheatCode sig _ = \case
  (Failure _ _ (BadCheatCode s)) -> (ConcreteBuf $ into s.unFunctionSelector) ./= (ConcreteBuf $ selector sig)
  _ -> PBool True

allBranchesFail :: App m => ByteString -> Maybe Sig -> m (Either [SMTCex] (Expr End))
allBranchesFail = checkPost (Just p)
  where
    p _ = \case
      Success _ _ _ _ -> PBool False
      _ -> PBool True

reachableUserAsserts :: App m => ByteString -> Maybe Sig -> m (Either [SMTCex] (Expr End))
reachableUserAsserts = checkPost (Just $ checkAssertions [0x01])

checkPost :: App m => Maybe (Postcondition RealWorld) -> ByteString -> Maybe Sig -> m (Either [SMTCex] (Expr End))
checkPost post c sig = do
  (e, res) <- withSolvers Z3 1 Nothing $ \s ->
    verifyContract s c sig [] defaultVeriOpts Nothing post
  let cexs = snd <$> mapMaybe getCex res
  case cexs of
    [] -> pure $ Right e
    cs -> pure $ Left cs

successGen :: [Prop] -> Expr End
successGen props = Success props mempty (ConcreteBuf "") mempty

-- gets the expected concrete values for symbolic abi testing
expectedConcVals :: Text -> AbiValue -> SMTCex
expectedConcVals nm val = case val of
  AbiUInt {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiInt {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiAddress {} -> mempty { addrs = Map.fromList [(SymAddr nm, truncateToAddr (mkWord val))] }
  AbiBool {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiBytes {} -> mempty { vars = Map.fromList [(Var nm, mkWord val)] }
  AbiArray _ _ vals -> mconcat . V.toList . V.imap (\(T.pack . show -> idx) v -> expectedConcVals (nm <> "-a-" <> idx) v) $ vals
  AbiTuple vals -> mconcat . V.toList . V.imap (\(T.pack . show -> idx) v -> expectedConcVals (nm <> "-t-" <> idx) v) $ vals
  _ -> internalError $ "unsupported Abi type " <> show nm <> " val: " <> show val <> " val type: " <> showAlter val
  where
    mkWord = word . encodeAbiValue
