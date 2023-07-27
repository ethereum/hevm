{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Prelude hiding (LT, GT)

import GHC.TypeLits
import Data.Proxy
import Control.Monad.State.Strict
import Data.Bits hiding (And, Xor)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as BS16
import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)
import Data.DoubleWord
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import Data.Text (Text)
import Data.Text qualified as T
import Data.Time (diffUTCTime, getCurrentTime)
import Data.Typeable
import Data.Vector qualified as Vector
import GHC.Conc (getNumProcessors)
import System.Directory
import System.Environment
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure, Success, isSuccess)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty.HUnit
import Test.Tasty.Runners hiding (Failure, Success)
import Test.Tasty.ExpectedFailure
import Text.RE.TDFA.String
import Text.RE.Replace
import Witch (unsafeInto, into)

import Optics.Core hiding (pre, re)
import Optics.State
import Optics.Operators.Unsafe

import EVM hiding (choose)
import EVM.ABI
import EVM.Exec
import EVM.Expr qualified as Expr
import EVM.Fetch qualified as Fetch
import EVM.Format (hexText, formatExpr)
import EVM.Patricia qualified as Patricia
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
import EVM.Types

main :: IO ()
main = defaultMain tests

-- | run a subset of tests in the repl. p is a tasty pattern:
-- https://github.com/UnkindPartition/tasty/tree/ee6fe7136fbcc6312da51d7f1b396e1a2d16b98a#patterns
runSubSet :: String -> IO ()
runSubSet p = defaultMain . applyPattern p $ tests

tests :: TestTree
tests = testGroup "hevm"
  [ Tracing.tests
  , testGroup "StorageTests"
    [ testCase "read-from-sstore" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x0) (Lit 0xab) (AbstractStore (LitAddr 0x0))))
    , testCase "read-from-concrete" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, 0xab)]))
    , testCase "read-past-write" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (SStore (Lit 0x1) (Var "b") (ConcreteStore $ Map.fromList [(0x0, 0xab)])))
    , testCase "accessStorage uses fetchedStorage" $ do
        let dummyContract =
              (initialContract (RuntimeCode (ConcreteRuntimeCode mempty)))
                { external = True }
            vm = vmForEthrunCreation ""
            -- perform the initial access
            vm1 = execState (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm
            -- it should fetch the contract first
            vm2 = case vm1.result of
                    Just (HandleEffect (Query (PleaseFetchContract _addr continue))) ->
                      execState (continue dummyContract) vm1
                    _ -> internalError "unexpected result"
            -- then it should fetch the slow
            vm3 = case vm2.result of
                    Just (HandleEffect (Query (PleaseFetchSlot _addr _slot continue))) ->
                      execState (continue 1337) vm2
                    _ -> internalError "unexpected result"
            -- perform the same access as for vm1
            vm4 = execState (EVM.accessStorage (LitAddr 0) (Lit 0) (pure . pure ())) vm3

        -- there won't be query now as accessStorage uses fetch cache
        assertBool (show vm4.result) (isNothing vm4.result)
    ]
  , testGroup "SimplifierUnitTests"
    -- common overflow cases that the simplifier was getting wrong
    [ testCase "writeWord-overflow" $ do
        let e = ReadByte (Lit 0x0) (WriteWord (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd) (Lit 0x0) (ConcreteBuf "\255\255\255\255"))
        b <- checkEquiv e (Expr.simplify e)
        assertBool "Simplifier failed" b
    , testCase "CopySlice-overflow" $ do
        let e = ReadWord (Lit 0x0) (CopySlice (Lit 0x0) (Lit 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc) (Lit 0x6) (ConcreteBuf "\255\255\255\255\255\255") (ConcreteBuf ""))
        b <- checkEquiv e (Expr.simplify e)
        assertBool "Simplifier failed" b
    , testCase "stripWrites-overflow" $ do
        -- below eventually boils down to
        -- unsafeInto (0xf0000000000000000000000000000000000000000000000000000000000000+1) :: Int
        -- which failed before
        let
          a = ReadByte (Lit 0xf0000000000000000000000000000000000000000000000000000000000000) (WriteByte (And (SHA256 (ConcreteBuf "")) (Lit 0x1)) (LitByte 0) (ConcreteBuf ""))
          b = Expr.simplify a
        ret <- checkEquiv a b
        assertBool "must be equivalent" ret
    ]
  -- These tests fuzz the simplifier by generating a random expression,
  -- applying some simplification rules, and then using the smt encoding to
  -- check that the simplified version is semantically equivalent to the
  -- unsimplified one
  , adjustOption (\(Test.Tasty.QuickCheck.QuickCheckTests n) -> Test.Tasty.QuickCheck.QuickCheckTests (min n 50)) $ testGroup "SimplifierTests"
    [ testProperty  "buffer-simplification" $ \(expr :: Expr Buf) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "store-simplification" $ \(expr :: Expr Storage) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "byte-simplification" $ \(expr :: Expr Byte) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "word-simplification" $ \(ZeroDepthWord expr) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "readStorage-equivalance" $ \(store, slot) -> ioProperty $ do
        let simplified = Expr.readStorage' slot store
            full = SLoad slot store
        checkEquiv simplified full
    , testProperty "writeStorage-equivalance" $ \(val, GenWriteStorageExpr (slot, store)) -> ioProperty $ do
        let simplified = Expr.writeStorage slot val store
            full = SStore slot val store
        checkEquiv simplified full
    , testProperty "readWord-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        checkEquiv simplified full
    , testProperty "writeWord-equivalance" $ \(idx, val, WriteWordBuf buf) -> ioProperty $ do
        let simplified = Expr.writeWord idx val buf
            full = WriteWord idx val buf
        checkEquiv simplified full
    , testProperty "arith-simplification" $ \(_ :: Int) -> ioProperty $ do
        expr <- generate . sized $ genWordArith 15
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "readByte-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readByte idx buf
            full = ReadByte idx buf
        checkEquiv simplified full
    -- we currently only simplify concrete writes over concrete buffers so that's what we test here
    , testProperty "writeByte-equivalance" $ \(LitOnly val, LitOnly buf, GenWriteByteIdx idx) -> ioProperty $ do
        let simplified = Expr.writeByte idx val buf
            full = WriteByte idx val buf
        checkEquiv simplified full
    , testProperty "copySlice-equivalance" $ \(srcOff, GenCopySliceBuf src, GenCopySliceBuf dst, LitWord @300 size) -> ioProperty $ do
        -- we bias buffers to be concrete more often than not
        dstOff <- generate (maybeBoundedLit 100_000)
        let simplified = Expr.copySlice srcOff dstOff size src dst
            full = CopySlice srcOff dstOff size src dst
        checkEquiv simplified full
    , testProperty "indexWord-equivalence" $ \(src, LitWord @50 idx) -> ioProperty $ do
        let simplified = Expr.indexWord idx src
            full = IndexWord idx src
        checkEquiv simplified full
    , testProperty "indexWord-mask-equivalence" $ \(src :: Expr EWord, LitWord @35 idx) -> ioProperty $ do
        mask <- generate $ do
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
    , testProperty "toList-equivalance" $ \buf -> ioProperty $ do
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

        input <- generate $ fixLength buf
        case Expr.toList input of
          Nothing -> do
            putStrLn "skip"
            pure True -- ignore cases where the buf cannot be represented as a list
          Just asList -> do
            let asBuf = Expr.fromList asList
            checkEquiv asBuf input
    ]
  , testGroup "MemoryTests"
    [ testCase "read-write-same-byte"  $ assertEqual ""
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteByte (Lit 0x20) (LitByte 0x12) mempty))
    , testCase "read-write-same-word"  $ assertEqual ""
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , testCase "read-byte-write-word"  $ assertEqual ""
        -- reading at byte 31 a word that's been written should return LSB
        (LitByte 0x12)
        (Expr.readByte (Lit 0x1f) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , testCase "read-byte-write-word2"  $ assertEqual ""
        -- Same as above, but offset not 0
        (LitByte 0x12)
        (Expr.readByte (Lit 0x20) (WriteWord (Lit 0x1) (Lit 0x12) mempty))
    ,testCase "read-write-with-offset"  $ assertEqual ""
        -- 0x3F = 63 decimal, 0x20 = 32. 0x12 = 18
        --    We write 128bits (32 Bytes), representing 18 at offset 32.
        --    Hence, when reading out the 63rd byte, we should read out the LSB 8 bits
        --           which is 0x12
        (LitByte 0x12)
        (Expr.readByte (Lit 0x3F) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    ,testCase "read-write-with-offset2"  $ assertEqual ""
        --  0x20 = 32, 0x3D = 61
        --  we write 128 bits (32 Bytes) representing 0x10012, at offset 32.
        --  we then read out a byte at offset 61.
        --  So, at 63 we'd read 0x12, at 62 we'd read 0x00, at 61 we should read 0x1
        (LitByte 0x1)
        (Expr.readByte (Lit 0x3D) (WriteWord (Lit 0x20) (Lit 0x10012) mempty))
    , testCase "read-write-with-extension-to-zero" $ assertEqual ""
        -- write word and read it at the same place (i.e. 0 offset)
        (Lit 0x12)
        (Expr.readWord (Lit 0x0) (WriteWord (Lit 0x0) (Lit 0x12) mempty))
    , testCase "read-write-with-extension-to-zero-with-offset" $ assertEqual ""
        -- write word and read it at the same offset of 4
        (Lit 0x12)
        (Expr.readWord (Lit 0x4) (WriteWord (Lit 0x4) (Lit 0x12) mempty))
    , testCase "read-write-with-extension-to-zero-with-offset2" $ assertEqual ""
        -- write word and read it at the same offset of 16
        (Lit 0x12)
        (Expr.readWord (Lit 0x20) (WriteWord (Lit 0x20) (Lit 0x12) mempty))
    , testCase "read-word-copySlice-overlap" $ assertEqual ""
        -- we should not recurse into a copySlice if the read index + 32 overlaps the sliced region
        (ReadWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
        (Expr.readWord (Lit 40) (CopySlice (Lit 0) (Lit 30) (Lit 12) (WriteWord (Lit 10) (Lit 0x64) (AbstractBuf "hi")) (AbstractBuf "hi")))
    , testCase "indexword-MSB" $ assertEqual ""
        -- 31st is the LSB byte (of 32)
        (LitByte 0x78)
        (Expr.indexWord (Lit 31) (Lit 0x12345678))
    , testCase "indexword-LSB" $ assertEqual ""
        -- 0th is the MSB byte (of 32), Lit 0xff22bb... is exactly 32 Bytes.
        (LitByte 0xff)
        (Expr.indexWord (Lit 0) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , testCase "indexword-LSB2" $ assertEqual ""
        -- same as above, but with offset 2
        (LitByte 0xbb)
        (Expr.indexWord (Lit 2) (Lit 0xff22bb4455667788990011223344556677889900112233445566778899001122))
    , testCase "encodeConcreteStore-overwrite" $
      assertEqual ""
        "(store (store emptyStore (_ bv1 256) (_ bv2 256)) (_ bv3 256) (_ bv4 256))"
        (EVM.SMT.encodeConcreteStore $
          Map.fromList [(W256 1, W256 2), (W256 3, W256 4)])
    , testCase "indexword-oob-sym" $ assertEqual ""
        -- indexWord should return 0 for oob access
        (LitByte 0x0)
        (Expr.indexWord (Lit 100) (JoinBytes
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)
          (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0) (LitByte 0)))
    , testCase "stripbytes-concrete-bug" $ assertEqual ""
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
    [ testCase "Trivial" $
        SolidityCall "x = 3;" []
          ===> AbiUInt 256 3

    , testCase "Arithmetic" $ do
        SolidityCall "x = a + 1;"
          [AbiUInt 256 1] ===> AbiUInt 256 2
        SolidityCall "unchecked { x = a - 1; }"
          [AbiUInt 8 0] ===> AbiUInt 8 255

    , testCase "keccak256()" $
        SolidityCall "x = uint(keccak256(abi.encodePacked(a)));"
          [AbiString ""] ===> AbiUInt 256 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470

    , testProperty "abi encoding vs. solidity" $ withMaxSuccess 20 $ forAll (arbitrary >>= genAbiValue) $
      \y -> ioProperty $ do
          Just encoded <- runStatements [i| x = abi.encode(a);|]
            [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ Vector.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (Vector.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ Vector.fromList [y])
          assertEqual "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    , testProperty "abi encoding vs. solidity (2 args)" $ withMaxSuccess 20 $ forAll (arbitrary >>= bothM genAbiValue) $
      \(x', y') -> ioProperty $ do
          Just encoded <- runStatements [i| x = abi.encode(a, b);|]
            [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ Vector.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (Vector.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ Vector.fromList [x',y'])
          assertEqual "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    -- we need a separate test for this because the type of a function is "function() external" in solidity but just "function" in the abi:
    , testProperty "abi encoding vs. solidity (function pointer)" $ withMaxSuccess 20 $ forAll (genAbiValue AbiFunctionType) $
      \y -> ioProperty $ do
          Just encoded <- runFunction [i|
              function foo(function() external a) public pure returns (bytes memory x) {
                x = abi.encode(a);
              }
            |] (abiMethod "foo(function)" (AbiTuple (Vector.singleton y)))
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ Vector.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (Vector.toList -> [e]) -> e
                _ -> internalError "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ Vector.fromList [y])
          assertEqual "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)
    ]

  , testGroup "Precompiled contracts"
      [ testGroup "Example (reverse)"
          [ testCase "success" $
              assertEqual "example contract reverses"
                (execute 0xdeadbeef "foobar" 6) (Just "raboof")
          , testCase "failure" $
              assertEqual "example contract fails on length mismatch"
                (execute 0xdeadbeef "foobar" 5) Nothing
          ]

      , testGroup "ECRECOVER"
          [ testCase "success" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4732"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
                a = hex "0000000000000000000000002d5e56d45c63150d937f2182538a0f18510cb11f"
              assertEqual "successful recovery"
                (Just a)
                (execute 1 (h <> v <> r <> s) 32)
          , testCase "fail on made up values" $ do
              let
                r = hex "c84e55cee2032ea541a32bf6749e10c8b9344c92061724c4e751600f886f4731"
                s = hex "1542b6457e91098682138856165381453b3d0acae2470286fd8c8a09914b1b5d"
                v = hex "000000000000000000000000000000000000000000000000000000000000001c"
                h = hex "513954cf30af6638cb8f626bd3f8c39183c26784ce826084d9d267868a18fb31"
              assertEqual "fail because bit flip"
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
    [ testCase "holes detected" $ do
        let code' = "608060405234801561001057600080fd5b5060405161040f38038061040f83398181016040528101906100329190610172565b73__$f3cbc3eb14e5bd0705af404abcf6f741ec$__63ab5c1ffe826040518263ffffffff1660e01b81526004016100699190610217565b60206040518083038186803b15801561008157600080fd5b505af4158015610095573d6000803e3d6000fd5b505050506040513d601f19601f820116820180604052508101906100b99190610145565b50506103c2565b60006100d36100ce84610271565b61024c565b9050828152602081018484840111156100ef576100ee610362565b5b6100fa8482856102ca565b509392505050565b600081519050610111816103ab565b92915050565b600082601f83011261012c5761012b61035d565b5b815161013c8482602086016100c0565b91505092915050565b60006020828403121561015b5761015a61036c565b5b600061016984828501610102565b91505092915050565b6000602082840312156101885761018761036c565b5b600082015167ffffffffffffffff8111156101a6576101a5610367565b5b6101b284828501610117565b91505092915050565b60006101c6826102a2565b6101d081856102ad565b93506101e08185602086016102ca565b6101e981610371565b840191505092915050565b60006102016003836102ad565b915061020c82610382565b602082019050919050565b6000604082019050818103600083015261023181846101bb565b90508181036020830152610244816101f4565b905092915050565b6000610256610267565b905061026282826102fd565b919050565b6000604051905090565b600067ffffffffffffffff82111561028c5761028b61032e565b5b61029582610371565b9050602081019050919050565b600081519050919050565b600082825260208201905092915050565b60008115159050919050565b60005b838110156102e85780820151818401526020810190506102cd565b838111156102f7576000848401525b50505050565b61030682610371565b810181811067ffffffffffffffff821117156103255761032461032e565b5b80604052505050565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052604160045260246000fd5b600080fd5b600080fd5b600080fd5b600080fd5b6000601f19601f8301169050919050565b7f6261720000000000000000000000000000000000000000000000000000000000600082015250565b6103b4816102be565b81146103bf57600080fd5b50565b603f806103d06000396000f3fe6080604052600080fdfea26469706673582212207d03b26e43dc3d116b0021ddc9817bde3762a3b14315351f11fc4be384fd14a664736f6c63430008060033"
        assertBool "linker hole not detected" (containsLinkerHole code'),
      testCase "no false positives" $ do
        let code' = "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
        assertBool "false positive" (not . containsLinkerHole $ code')
    ]

  , testGroup "metadata stripper"
    [ testCase "it strips the metadata for solc => 0.6" $ do
        let code' = hexText "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fea265627a7a723158205d775f914dcb471365a430b5f5b2cfe819e615cbbb5b2f1ccc7da1fd802e43c364736f6c634300050b0032"
            stripped = stripBytecodeMetadata code'
        assertEqual "failed to strip metadata" (show (ByteStringS stripped)) "0x608060405234801561001057600080fd5b50600436106100365760003560e01c806317bf8bac1461003b578063acffee6b1461005d575b600080fd5b610043610067565b604051808215151515815260200191505060405180910390f35b610065610073565b005b60008060015414905090565b6000809054906101000a900473ffffffffffffffffffffffffffffffffffffffff1673ffffffffffffffffffffffffffffffffffffffff1663f8a8fd6d6040518163ffffffff1660e01b815260040160206040518083038186803b1580156100da57600080fd5b505afa1580156100ee573d6000803e3d6000fd5b505050506040513d602081101561010457600080fd5b810190808051906020019092919050505060018190555056fe"
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

        (json, path') <- solidity' srccode
        let (Contracts solc', _, _) = fromJust $ readStdJSON json
            initCode = (solc' ^?! ix (path' <> ":A")).creationCode
        -- add constructor arguments
        assertEqual "constructor args screwed up metadata stripping" (stripBytecodeMetadata (initCode <> encodeAbiValue (AbiUInt 256 1))) (stripBytecodeMetadata initCode)
    ]

  , testGroup "RLP encodings"
    [ testProperty "rlp decode is a retraction (bytes)" $ \(Bytes bs) ->
--      withMaxSuccess 100000 $
      rlpdecode (rlpencode (BS bs)) == Just (BS bs)
    , testProperty "rlp encode is a partial inverse (bytes)" $ \(Bytes bs) ->
--      withMaxSuccess 100000 $
        case rlpdecode bs of
          Just r -> rlpencode r == bs
          Nothing -> True
    ,  testProperty "rlp decode is a retraction (RLP)" $ \(RLPData r) ->
--       withMaxSuccess 100000 $
       rlpdecode (rlpencode r) == Just r
    ]
  , testGroup "Merkle Patricia Trie"
    [  testProperty "update followed by delete is id" $ \(Bytes r, Bytes s, Bytes t) ->
        whenFail
        (putStrLn ("r:" <> (show (ByteStringS r))) >>
         putStrLn ("s:" <> (show (ByteStringS s))) >>
         putStrLn ("t:" <> (show (ByteStringS t)))) $
--       withMaxSuccess 100000 $
       Patricia.insertValues [(r, BS.pack[1]), (s, BS.pack[2]), (t, BS.pack[3]),
                              (r, mempty), (s, mempty), (t, mempty)]
       === (Just $ Patricia.Literal Patricia.Empty)
    ]
 , testGroup "Panic code tests via symbolic execution"
  [
     testCase "assert-fail" $ do
       Just c <- solcRuntime "MyContract"
           [i|
           contract MyContract {
             function fun(uint256 a) external pure {
               assert(a != 0);
             }
            }
           |]
       (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x01] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
       assertEqual "Must be 0" 0 $ getVar ctr "arg1"
       putStrLn  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
     ,
     testCase "safeAdd-fail" $ do
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
        assertBool "Overflow must occur" (toInteger x + toInteger y >= maxUint)
        putStrLn "expected counterexample found"
     ,
     testCase "div-by-zero-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a, uint256 b) external pure returns (uint256 c) {
               c = a/b;
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x12] c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        assertEqual "Division by 0 needs b=0" (getVar ctr "arg2") 0
        putStrLn "expected counterexample found"
     ,
      testCase "unused-args-fail" $ do
         Just c <- solcRuntime "C"
             [i|
             contract C {
               function fun(uint256 a) public pure {
                 assert(false);
               }
             }
             |]
         (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x1] c Nothing [] defaultVeriOpts
         putStrLn "expected counterexample found"
      ,
     testCase "enum-conversion-fail" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              enum MyEnum { ONE, TWO }
              function fun(uint256 a) external pure returns (MyEnum b) {
                b = MyEnum(a);
              }
             }
            |]
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x21] c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        assertBool "Enum is only defined for 0 and 1" $ (getVar ctr "arg1") > 1
        putStrLn "expected counterexample found"
     ,
     -- TODO 0x22 is missing: "0x22: If you access a storage byte array that is incorrectly encoded."
     -- TODO below should NOT fail
     -- TODO this has a loop that depends on a symbolic value and currently causes interpret to loop
     ignoreTest $ testCase "pop-empty-array" $ do
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
        print $ length a
        print $ show a
        putStrLn "expected counterexample found"
     ,
     testCase "access-out-of-bounds-array" $ do
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
        -- assertBool "Access must be beyond element 2" $ (getVar ctr "arg1") > 1
        putStrLn "expected counterexample found"
      ,
      -- Note: we catch the assertion here, even though we are only able to explore partially
      testCase "alloc-too-much" $ do
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
        putStrLn "expected counterexample found"
      ,
      -- TODO: we can't deal with symbolic jump conditions
      expectFail $ testCase "call-zero-inited-var-thats-a-function" $ do
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
        assertEqual "unexpected cex value" a 44
        putStrLn "expected counterexample found"
  ]
  , testGroup "Dapp-Tests"
    [ testCase "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "DappTools" $ do
        -- quick smokecheck to make sure that we can parse dapptools style build outputs
        let cases =
              [ ("test/contracts/pass/trivial.sol", ".*", True)
              , ("test/contracts/pass/invariants.sol", "invariantTestThisBal", True)
              , ("test/contracts/pass/dsProvePass.sol", "proveEasy", True)
              , ("test/contracts/fail/trivial.sol", ".*", False)
              , ("test/contracts/fail/invariantFail.sol", "invariantCount", False)
              , ("test/contracts/fail/dsProveFail.sol", "prove_add", False)
              ]
        results <- forM cases $ \(testFile, match, expected) -> do
          actual <- runSolidityTestCustom testFile match Nothing False Nothing DappTools
          pure (actual == expected)
        assertBool "test result" (and results)
    , testCase "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        runSolidityTest testFile "testFalse" >>= assertEqual "test result" False
    , testCase "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        runSolidityTest testFile "prove_trivial" >>= assertEqual "test result" False
        runSolidityTest testFile "prove_add" >>= assertEqual "test result" False
        --runSolidityTest testFile "prove_smtTimeout" >>= assertEqual "test result" False
        runSolidityTest testFile "prove_multi" >>= assertEqual "test result" False
        -- TODO: implement overflow checking optimizations and enable, currently this runs forever
        --runSolidityTest testFile "prove_distributivity" >>= assertEqual "test result" False
    , testCase "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runSolidityTestCustom testFile "prove_loop" (Just 10) False Nothing Foundry >>= assertEqual "test result" True
        runSolidityTestCustom testFile "prove_loop" (Just 100) False Nothing Foundry >>= assertEqual "test result" False
    , testCase "Invariant-Tests-Pass" $ do
        let testFile = "test/contracts/pass/invariants.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Invariant-Tests-Fail" $ do
        let testFile = "test/contracts/fail/invariantFail.sol"
        runSolidityTest testFile "invariantFirst" >>= assertEqual "test result" False
        runSolidityTest testFile "invariantCount" >>= assertEqual "test result" False
    , testCase "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Cheat-Codes-Fail" $ do
        let testFile = "test/contracts/fail/cheatCodes.sol"
        runSolidityTestCustom testFile "testBadFFI" Nothing False Nothing Foundry >>= assertEqual "test result" False
        runSolidityTestCustom testFile "test_prank_underflow" Nothing False Nothing Foundry >>= assertEqual "test result" False
    , testCase "Unwind" $ do
        let testFile = "test/contracts/pass/unwind.sol"
        runSolidityTest testFile ".*" >>= assertEqual "test result" True
    ]
  , testGroup "max-iterations"
    [ testCase "concrete-loops-reached" $ do
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
        assertBool "The expression is not partial" $ isPartial e
    , testCase "concrete-loops-not-reached" $ do
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
        assertBool "The expression is partial" $ not $ isPartial e
    , testCase "symbolic-loops-reached" $ do
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
        assertBool "The expression is not partial" $ Expr.containsNode isPartial e
    , testCase "inconsistent-paths" $ do
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
            -- we dont' ask the solver about the loop condition until we're
            -- already in an inconsistent path (i == 5, j <= 3, i < j), so we
            -- will continue looping here until we hit max iterations
            opts = defaultVeriOpts{ maxIter = Just 10, askSmtIters = 5 }
        (e, [Qed _]) <- withSolvers Z3 1 Nothing $
          \s -> checkAssert s defaultPanicCodes c sig [] opts
        assertBool "The expression is not partial" $ Expr.containsNode isPartial e
    , testCase "symbolic-loops-not-reached" $ do
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
        assertBool "The expression is partial" $ not (Expr.containsNode isPartial e)
    ]
  , testGroup "Symbolic execution"
      [
     testCase "require-test" $ do
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
        putStrLn "Require works as expected"
     ,
     testCase "ITE-with-bitwise-AND" $ do
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
       putStrLn "expected counterexample found"
     ,
     testCase "ITE-with-bitwise-OR" $ do
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
       putStrLn "this should always be true, due to bitwise OR with positive value"
    ,
    -- CopySlice check
    -- uses identity precompiled contract (0x4) to copy memory
    -- checks 9af114613075a2cd350633940475f8b6699064de (readByte + CopySlice had src/dest mixed up)
    -- without 9af114613 it dies with: `Exception: UnexpectedSymbolicArg 296 "MSTORE index"`
    --       TODO: check  9e734b9da90e3e0765128b1f20ce1371f3a66085 (bufLength + copySlice was off by 1)
    testCase "copyslice-check" $ do
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
      putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
     ,
     -- TODO look at tests here for SAR: https://github.com/dapphub/dapptools/blob/01ef8ea418c3fe49089a44d56013d8fcc34a1ec2/src/dapp-tests/pass/constantinople.sol#L250
     testCase "opcode-sar-neg" $ do
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
        putStrLn "SAR works as expected"
     ,
     testCase "opcode-sar-pos" $ do
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
        putStrLn "SAR works as expected"
     ,
     testCase "opcode-sar-fixedval-pos" $ do
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
        putStrLn "SAR works as expected"
     ,
     testCase "opcode-sar-fixedval-neg" $ do
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
        putStrLn "SAR works as expected"
     ,
     testCase "opcode-div-zero-1" $ do
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
        putStrLn "sdiv works as expected"
      ,
     testCase "opcode-sdiv-zero-1" $ do
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
        putStrLn "sdiv works as expected"
      ,
     testCase "opcode-sdiv-zero-2" $ do
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
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "sdiv works as expected"
      ,
     testCase "signed-overflow-checks" $ do
        Just c <- solcRuntime "C"
            [i|
            contract C {
              function fun(uint160 a) external {
                  int256 j = int256(uint256(a)) + 1;
                  assert(false);
              }
            }
            |]
        (_, [Cex _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint160)" [AbiUIntType 160])) [] defaultVeriOpts
        putStrLn "expected cex discovered"
      ,
     testCase "opcode-signextend-neg" $ do
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
        putStrLn "signextend works as expected"
      ,
     testCase "opcode-signextend-pos-nochop" $ do
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
        putStrLn "signextend works as expected"
      ,
      testCase "opcode-signextend-pos-chopped" $ do
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
        putStrLn "signextend works as expected"
      ,
      -- when b is too large, value is unchanged
      testCase "opcode-signextend-pos-b-toolarge" $ do
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
        putStrLn "signextend works as expected"
     ,
     testCase "opcode-shl" $ do
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
        putStrLn "SAR works as expected"
     ,
     testCase "opcode-xor-cancel" $ do
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
        putStrLn "XOR works as expected"
      ,
      testCase "opcode-xor-reimplement" $ do
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
        putStrLn "XOR works as expected"
      ,
      testCase "opcode-div-res-zero-on-div-by-zero" $ do
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
        putStrLn "DIV by zero is zero"
      ,
      -- Somewhat tautological since we are asserting the precondition
      -- on the same form as the actual "requires" clause.
      testCase "SafeAdd success case" $ do
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
        putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
     ,

      testCase "x == y => x + y == 2 * y" $ do
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
        putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
      ,
      testCase "summary storage writes" $ do
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
        putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- tests how whiffValue handles Neg via application of the triple IsZero simplification rule
        -- regression test for: https://github.com/dapphub/dapptools/pull/698
        testCase "Neg" $ do
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
            Just c <- yulRuntime "Neg" src
            (res, [Qed _]) <- withSolvers Z3 4 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "hello(address)" [AbiAddressType])) [] defaultVeriOpts
            putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "catch-storage-collisions-noproblem" $ do
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
          putStrLn "Correct, this can never fail"
        ,
        -- Inspired by these `msg.sender == to` token bugs
        -- which break linearity of totalSupply.
        testCase "catch-storage-collisions-good" $ do
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
          putStrLn $ "y:" <> show y
          putStrLn $ "x:" <> show x
          assertEqual "Catch storage collisions" x y
          putStrLn "expected counterexample found"
        ,
        testCase "simple-assert" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo() external pure {
                assert(false);
              }
             }
            |]
          (_, [Cex (Failure _ _ (Revert msg), _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo()" [])) [] defaultVeriOpts
          assertEqual "incorrect revert msg" msg (ConcreteBuf $ panicMsg 0x01)
        ,
        testCase "simple-assert-2" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo(uint256 x) external pure {
                assert(x != 10);
              }
             }
            |]
          (_, [(Cex (_, ctr))]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "foo(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          assertEqual "Must be 10" 10 $ getVar ctr "arg1"
          putStrLn "Got 10 Cex, as expected"
        ,
        testCase "assert-fail-equal" $ do
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
          assertBool "0 must be one of the Cex-es" $ isJust $ List.elemIndex 0 ints
          putStrLn "expected 2 counterexamples found, one Cex is the 0 value"
        ,
        testCase "assert-fail-notequal" $ do
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
          assertBool "At least one has to be 0, to go through the first assert" (x == 0 || y == 0)
          putStrLn "expected 2 counterexamples found."
        ,
        testCase "assert-fail-twoargs" $ do
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
          putStrLn "expected 2 counterexamples found"
        ,
        testCase "assert-2nd-arg" $ do
          Just c <- solcRuntime "AssertFailTwoParams"
            [i|
            contract AssertFailTwoParams {
              function fun(uint256 deposit_count1, uint256 deposit_count2) external pure {
                assert(deposit_count2 != 666);
              }
             }
            |]
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "fun(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          assertEqual "Must be 666" 666 $ getVar ctr "arg2"
          putStrLn "Found arg2 Ctx to be 666"
        ,
        -- LSB is zeroed out, byte(31,x) takes LSB, so y==0 always holds
        testCase "check-lsb-msb1" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- We zero out everything but the LSB byte. However, byte(31,x) takes the LSB byte
        -- so there is a counterexamle, where LSB of x is not zero
        testCase "check-lsb-msb2" $ do
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
          assertBool "last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff) > 0
          putStrLn "Expected counterexample found"
        ,
        -- We zero out everything but the 2nd LSB byte. However, byte(31,x) takes the 2nd LSB byte
        -- so there is a counterexamle, where 2nd LSB of x is not zero
        testCase "check-lsb-msb3 -- 2nd byte" $ do
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
          assertBool "second to last byte must be non-zero" $ ((Data.Bits..&.) (getVar ctr "arg1") 0xff00) > 0
          putStrLn "Expected counterexample found"
        ,
        -- Reverse of thest above
        testCase "check-lsb-msb4 2nd byte rev" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        -- Bitwise OR operation test
        testCase "opcode-bitwise-or-full-1s" $ do
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
          putStrLn "When OR-ing with full 1's we should get back full 1's"
        ,
        -- Bitwise OR operation test
        testCase "opcode-bitwise-or-byte-of-1s" $ do
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
          putStrLn "When OR-ing with a byte of 1's, we should get 1's back there"
        ,
        testCase "Deposit contract loop (z3)" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "Deposit-contract-loop-error-version" $ do
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
          assertEqual "Must be 255" 255 $ getVar ctr "arg1"
          putStrLn  $ "expected counterexample found, and it's correct: " <> (show $ getVar ctr "arg1")
        ,
        testCase "explore function dispatch" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x) public pure returns (uint) {
                return x;
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c Nothing [] defaultVeriOpts
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "check-asm-byte-in-bounds" $ do
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
          putStrLn "in bounds byte reads return the expected value"
        ,
        testCase "check-div-mod-sdiv-smod-by-zero-constant-prop" $ do
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
          putStrLn "div/mod/sdiv/smod by zero works as expected during constant propagation"
        ,
        testCase "check-asm-byte-oob" $ do
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
          putStrLn "oob byte reads always return 0"
        ,
        testCase "injectivity of keccak (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y) public pure {
                if (keccak256(abi.encodePacked(x)) == keccak256(abi.encodePacked(y))) assert(x == y);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256,uint256)" [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "injectivity of keccak contrapositive (32 bytes)" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "injectivity of keccak (64 bytes)" $ do
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
          assertEqual "x==y for hash collision" x y
          assertEqual "w==z for hash collision" w z
          putStrLn "expected counterexample found"
        ,
        testCase "calldata beyond calldatasize is 0 (symbolic calldata)" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "calldata beyond calldatasize is 0 (concrete dalldata prefix)" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "calldata symbolic access" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "multiple-contracts" $ do
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
            let vm = abstractVM (mkCalldata (Just (Sig "call_A()" [])) []) c Nothing
                       & set (#state % #callvalue) (Lit 0)
                       & over (#env % #contracts)
                          (Map.insert aAddr (initialContract (RuntimeCode (ConcreteRuntimeCode a))))
            verify s defaultVeriOpts vm (Just $ checkAssertions defaultPanicCodes)

          let storeCex = cex.store
              testCex = case (Map.lookup cAddr storeCex, Map.lookup aAddr storeCex) of
                          (Just sC, Just sA) -> case (Map.lookup 0 sC, Map.lookup 0 sA) of
                              (Just x, Just y) -> x /= y
                              (Just x, Nothing) -> x /= 0
                              _ -> False
                          _ -> False
          assertBool "Did not find expected storage cex" testCex
          putStrLn "expected counterexample found"
        ,
        expectFail $ testCase "calling unique contracts (read from storage)" $ do
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
          putStrLn "expected counterexample found"
        ,
        testCase "keccak concrete and sym agree" $ do
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
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "keccak concrete and sym injectivity" $ do
          Just c <- solcRuntime "A"
            [i|
              contract A {
                function f(uint x) public pure {
                  if (x !=3) assert(keccak256(abi.encode(x)) != keccak256(abi.encode(3)));
                }
              }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "f(uint256)" [AbiUIntType 256])) [] defaultVeriOpts
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        ignoreTest $ testCase "safemath distributivity (yul)" $ do
          let yulsafeDistributivity = hex "6355a79a6260003560e01c14156016576015601f565b5b60006000fd60a1565b603d602d604435600435607c565b6039602435600435607c565b605d565b6052604b604435602435605d565b600435607c565b141515605a57fe5b5b565b6000828201821115151560705760006000fd5b82820190505b92915050565b6000818384048302146000841417151560955760006000fd5b82820290505b92915050565b"
          let vm =  abstractVM (mkCalldata (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) []) yulsafeDistributivity Nothing
          (_, [Qed _]) <-  withSolvers Z3 1 Nothing $ \s -> verify s defaultVeriOpts vm (Just $ checkAssertions defaultPanicCodes)
          putStrLn "Proven"
        ,
        testCase "safemath distributivity (sol)" $ do
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

          (_, [Qed _]) <- withSolvers Z3 1 (Just 99999999) $ \s -> checkAssert s defaultPanicCodes c (Just (Sig "distributivity(uint256,uint256,uint256)" [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLn "Proven"
        ,
        testCase "storage-cex-1" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
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
          assertBool "Did not find expected storage cex" testCex
          putStrLn "Expected counterexample found"
        ,
        testCase "storage-cex-2" $ do
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
                          Just s -> Map.size s == 2 &&
                                    case (Map.lookup 0 s, Map.lookup (10 + a) s) of
                                      (Just x, Just y) -> x >= y
                                      _ -> False
                          _ -> False
          assertBool "Did not find expected storage cex" testCex
          putStrLn "Expected counterexample found"
        ,
        testCase "storage-cex-concrete" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              uint x;
              uint y;
              function fun(uint256 a) external{
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
          assertBool "Did not find expected storage cex" testCex
          putStrLn "Expected counterexample found"
        ,
        testCase "symbolic-address-create" $ do
          let src = [i|
                    contract A {
                      constructor() payable {}
                    }
                    contract C {
                      function fun(uint256 a) external{
                        assert(address(this).balance > a);
                        new A{value:a}();
                      }
                    }
                    |]
          Just a <- solcRuntime "A" src
          Just c <- solcRuntime "C" src
          (expr, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c Nothing [] defaultVeriOpts Nothing Nothing
          let isSuc (Success {}) = True
              isSuc _ = False
          case filter isSuc (flattenExpr expr) of
            [Success _ _ _ store] -> do
              let ca = fromJust (Map.lookup (SymAddr "freshSymAddr1") store)
              let code = case ca.code of
                    RuntimeCode (ConcreteRuntimeCode c') -> c'
                    _ -> internalError "expected concrete code"
              assertEqual "balance mismatch" (Var "arg1") ca.balance
              assertEqual "code mismatch" (stripBytecodeMetadata a) (stripBytecodeMetadata code)
              assertEqual "nonce mismatch" (Just 1) ca.nonce
            _ -> assertBool "too many success nodes!" False
        ,
        testCase "symbolic-balance-call" $ do
          let src = [i|
                    contract A {
                      function f() public payable returns (uint) {
                        return msg.value;
                      }
                    }
                    contract C {
                      function fun(uint256 x) external {
                        assert(address(this).balance > x);
                        A a = new A();
                        uint res = a.f{value:x}();
                        assert(res == x);
                      }
                    }
                    |]
          Just c <- solcRuntime "C" src
          (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c Nothing [] defaultVeriOpts Nothing (Just $ checkAssertions [0x01])
          putStrLn "expected cex discovered"
        ,
        testCase "deployed-contract-addresses-cannot-alias" $ do
          Just c <- solcRuntime "C"
            [i|
              contract A {}
              contract C {
                function f() external {
                  A a = new A();
                  assert(address(a) == address(this));
                }
              }
            |]
          res <- reachableUserAsserts c Nothing
          assertEqual "should not be able to alias" Nothing res
        ,
        testCase "addresses-in-args-can-alias-anything" $ do
          let addrs :: [String]
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
            Just [cex] <- reachableUserAsserts c sig
            pure cex.addrs

          let check as a = (Map.lookup (SymAddr "arg1") as) @?= (Map.lookup a as)
          check self (SymAddr "entrypoint")
          check origin (SymAddr "origin")
          check coinbase (SymAddr "coinbase")
          check caller (SymAddr "caller")
        ,
        testCase "addresses-in-args-can-alias-themselves" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function f(address a, address b) external {
                  if (a == b) assert(false);
                }
              }
            |]
          let sig = Just $ Sig "f(address,address)" [AbiAddressType,AbiAddressType]
          Just [cex] <- reachableUserAsserts c sig
          let arg1 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
              arg2 = fromJust $ Map.lookup (SymAddr "arg1") cex.addrs
          assertEqual "should match" arg1 arg2
        ,
        testCase "addresses-in-context-can-alias" $ do
          Just c <- solcRuntime "C"
            [i|
              contract C {
                function f() external {
                  if (tx.origin == msg.sender) assert(false);
                }
              }
            |]
          Just [cex] <- reachableUserAsserts c Nothing
          let origin = Map.lookup (SymAddr "origin") cex.addrs
              caller = Map.lookup (SymAddr "caller") cex.addrs
          assertEqual "orgin and caller should match" origin caller
        ,
        testCase "vm.store succeeds for a non aliased address" $ do
          pure ()
        ,
        testCase "vm.load fails for a potentially aliased address" $ do
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
          let postc _ = \case
                (Failure _ _ (BadCheatCode s)) -> (ConcreteBuf $ into s.unFunctionSelector) ./= (ConcreteBuf $ selector "store(address,bytes32,bytes32")
                _ -> PBool True
          (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c Nothing [] debugVeriOpts Nothing (Just postc)
          print cex
          pure ()
        ,
        testCase "vm.store fails for a potentially aliased address" $ do
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
          let postc _ = \case
                (Failure _ _ (BadCheatCode s)) -> (ConcreteBuf $ into s.unFunctionSelector) ./= (ConcreteBuf $ selector "store(address,bytes32,bytes32")
                _ -> PBool True
          (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c Nothing [] debugVeriOpts Nothing (Just postc)
          print cex
          pure ()
        ,
        testCase "transfering-eth-does-not-dealias" $ do
          Just c <- solcRuntime "C"
            [i|
              contract Send {
                constructor(address payable dst) payable {
                  selfdestruct(dst);
                }
              }
              contract C {
                function f() external {
                  uint preSender = msg.sender.balance;
                  uint preOrigin = tx.origin.balance;

                  // send some eth (we can't do calls to unknown
                  // code yet so we use selfdestruct
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
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
            verifyContract s c Nothing [] debugVeriOpts Nothing (Just $ checkAssertions [0x01])
          pure ()
        ,
        testCase "addresses-in-context-are-symbolic" $ do
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
            (_, [Cex (_, cex)]) <- withSolvers Z3 1 Nothing $ \s ->
              verifyContract s con Nothing [] defaultVeriOpts Nothing (Just $ checkAssertions [0x01])
            assertEqual "wrong number of addresses" 1 (length (Map.keys cex.addrs))
            pure cex

          assertEqual "wrong model for a" (Addr 0) (fromJust $ Map.lookup (SymAddr "caller") acex.addrs)
          assertEqual "wrong model for b" (Addr 1) (fromJust $ Map.lookup (SymAddr "coinbase") bcex.addrs)
          assertEqual "wrong model for c" (Addr 2) (fromJust $ Map.lookup (SymAddr "origin") ccex.addrs)
          assertEqual "wrong model for d" (Addr 3) (fromJust $ Map.lookup (SymAddr "entrypoint") dcex.addrs)
  ]
  , testGroup "equivalence-checking"
    [
      testCase "eq-yul-simple-cex" $ do
        Just aPrgm <- yul ""
          [i|
          {
            calldatacopy(0, 0, 32)
            switch mload(0)
            case 0 { }
            case 1 { }
            default { invalid() }
          }
          |]
        Just bPrgm <- yul ""
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
          assertBool "Must have a difference" (any isCex a)
      ,
      testCase "eq-sol-exp-qed" $ do
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
          assertEqual "Must have no difference" [Qed ()] a
      ,
      testCase "eq-balance-differs" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              function f() public {
                payable(address(0x0)).transfer(2);
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              function f() public {
                payable(address(0x0)).transfer(1);
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertBool "Must differ" (all isCex a)
      ,
      -- TODO: this fails because we don't check equivalence of deployed contracts
      expectFail $ testCase "eq-handles-contract-deployment" $ do
        Just aPrgm <- solcRuntime "B"
          [i|
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
                //payable(address(0x0)).transfer(address(this).balance);
              }
            }
          |]
        Just bPrgm <- solcRuntime "D"
          [i|
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
                //payable(address(0x0)).transfer(address(this).balance);
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertBool "Must differ" (all isCex a)
      ,
      testCase "eq-unknown-addr" $ do
        Just aPrgm <- solcRuntime "C"
          [i|
            contract C {
              uint bal;
              function a(address a, address b) public {
                bal = a.balance;
              }
            }
          |]
        Just bPrgm <- solcRuntime "C"
          [i|
            contract C {
              uint bal;
              function a(address a, address b) public {
                bal = b.balance;
              }
            }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          let cd = mkCalldata (Just (Sig "a(address,address)" [AbiAddressType, AbiAddressType])) []
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts cd
          -- TODO: We get a cex here, but since we were able to statically
          -- determine that the states differed by comparing the universe of
          -- addresses, we don't get back a full cex (i.e. it doesn't contains
          -- models for the addresses or their balances). Not sure how to deal with this...
          -- TODO: this doesn't work with fully abstract calldata, since we
          -- don't have a WAddr when we execute BALANCE
          assertEqual "Must be different" (any isCex a) True
      ,
      testCase "eq-sol-exp-cex" $ do
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
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts (mkCalldata Nothing [])
          assertEqual "Must be different" (any isCex a) True
      , testCase "eq-all-yul-optimization-tests" $ do
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
                    ]

        solcRepo <- fromMaybe (internalError "cannot find solidity repo") <$> (lookupEnv "HEVM_SOLIDITY_REPO")
        let testDir = solcRepo <> "/test/libyul/yulOptimizerTests"
        dircontents <- System.Directory.listDirectory testDir
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
        files <- recursiveList fullpaths []
        let filesFiltered = filter (\file -> not $ any (`List.isSubsequenceOf` file) ignoredTests) files

        -- Takes one file which follows the Solidity Yul optimizer unit tests format,
        -- extracts both the nonoptimized and the optimized versions, and checks equivalence.
        forM_ filesFiltered (\f-> do
          origcont <- readFile f
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
          start <- getCurrentTime
          putStrLn $ "Checking file: " <> f
          when opts.debug $ do
            putStrLn "-------------Original Below-----------------"
            mapM_ putStrLn unfiltered
            putStrLn "------------- Filtered A + Symb below-----------------"
            mapM_ putStrLn filteredASym
            putStrLn "------------- Filtered B + Symb below-----------------"
            mapM_ putStrLn filteredBSym
            putStrLn "------------- END -----------------"
          Just aPrgm <- yul "" $ T.pack $ unlines filteredASym
          Just bPrgm <- yul "" $ T.pack $ unlines filteredBSym
          procs <- getNumProcessors
          withSolvers CVC5 (unsafeInto procs) (Just 100) $ \s -> do
            res <- equivalenceCheck s aPrgm bPrgm opts (mkCalldata Nothing [])
            end <- getCurrentTime
            case any isCex res of
              False -> do
                print $ "OK. Took " <> (show $ diffUTCTime end start) <> " seconds"
                let timeouts = filter isTimeout res
                unless (null timeouts) $ do
                  putStrLn $ "But " <> (show $ length timeouts) <> " timeout(s) occurred"
                  internalError "Encountered timeouts"
              True -> do
                putStrLn $ "Not OK: " <> show f <> " Got: " <> show res
                internalError "Was NOT equivalent"
           )
    ]
  ]
  where
    (===>) = assertSolidityComputation


checkEquiv :: (Typeable a) => Expr a -> Expr a -> IO Bool
checkEquiv l r = withSolvers Z3 1 (Just 1) $ \solvers -> do
  if l == r
     then do
       putStrLn "skip"
       pure True
     else do
       let smt = assertProps [l ./= r]
       res <- checkSat solvers smt
       print res
       pure $ case res of
         Unsat -> True
         EVM.Solvers.Unknown -> True
         Sat _ -> False
         Error _ -> False

-- | Takes a runtime code and calls it with the provided calldata

-- | Takes a creation code and some calldata, runs the creation code, and calls the resulting contract with the provided calldata
runSimpleVM :: ByteString -> ByteString -> IO (Maybe ByteString)
runSimpleVM x ins = do
  loadVM x >>= \case
    Nothing -> pure Nothing
    Just vm -> do
     let calldata = (ConcreteBuf ins)
         vm' = set (#state % #calldata) calldata vm
     res <- Stepper.interpret (Fetch.zero 0 Nothing) vm' Stepper.execFully
     case res of
       (Right (ConcreteBuf bs)) -> pure $ Just bs
       s -> internalError $ show s

-- | Takes a creation code and returns a vm with the result of executing the creation code
loadVM :: ByteString -> IO (Maybe VM)
loadVM x = do
  vm1 <- Stepper.interpret (Fetch.zero 0 Nothing) (vmForEthrunCreation x) Stepper.runFully
  case vm1.result of
     Just (VMSuccess (ConcreteBuf targetCode)) -> do
       let target = vm1.state.contract
       vm2 <- Stepper.interpret (Fetch.zero 0 Nothing) vm1 (prepVm target targetCode >> Stepper.run)
       pure $ Just vm2
     _ -> pure Nothing
  where
    prepVm target targetCode = Stepper.evm $ do
      replaceCodeOfSelf (RuntimeCode $ ConcreteRuntimeCode targetCode)
      resetState
      assign (#state % #gas) 0xffffffffffffffff -- kludge
      loadContract target

hex :: ByteString -> ByteString
hex s =
  case BS16.decodeBase16 s of
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

runFunction :: Text -> ByteString -> IO (Maybe ByteString)
runFunction c input = do
  Just x <- singleContract "X" c
  runSimpleVM x input

runStatements
  :: Text -> [AbiValue] -> AbiType
  -> IO (Maybe ByteString)
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
  |] (abiMethod s (AbiTuple $ Vector.fromList args))

getStaticAbiArgs :: Int -> VM -> [Expr EWord]
getStaticAbiArgs n vm =
  let cd = vm.state.calldata
  in decodeStaticArgs 4 n cd

-- includes shaving off 4 byte function sig
decodeAbiValues :: [AbiType] -> ByteString -> [AbiValue]
decodeAbiValues types bs =
  let xy = case decodeAbiValue (AbiTupleType $ Vector.fromList types) (BS.fromStrict (BS.drop 4 bs)) of
        AbiTuple xy' -> xy'
        _ -> internalError "AbiTuple expected"
  in Vector.toList xy

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
    , fmap SymAddr genName
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

instance Arbitrary (Vector.Vector (Expr Byte)) where
  arbitrary = fmap Vector.fromList (listOf1 arbitrary)

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

genName :: Gen Text
-- In order not to generate SMT reserved words, we prepend with "esc_"
genName = fmap (T.pack . ("esc_" <> )) $ listOf1 (oneof . (fmap pure) $ ['a'..'z'] <> ['A'..'Z'])

genEnd :: Int -> Gen (Expr End)
genEnd 0 = oneof
 [ fmap (Failure mempty mempty . UnrecognizedOpcode) arbitrary
 , pure $ Failure mempty mempty IllegalOverflow
 , pure $ Failure mempty mempty SelfDestruction
 ]
genEnd sz = oneof
 [ fmap (Failure mempty mempty . Revert) subBuf
 , liftM4 Success (return mempty) (return mempty) subBuf arbitrary
 , liftM3 ITE subWord subEnd subEnd
 ]
 where
   subBuf = defaultBuf (sz `div` 2)
   subWord = defaultWord (sz `div` 2)
   subEnd = genEnd (sz `div` 2)

genWord :: Int -> Int -> Gen (Expr EWord)
genWord litFreq 0 = frequency
  [ (litFreq, do
      val <- frequency
       [ (10, fmap (`mod` 100) arbitrary)
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
      , fmap Var genName
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
  [ fmap AbstractBuf genName
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
  [ fmap AbstractStore arbitrary
  , fmap ConcreteStore arbitrary
  ]
genStorage sz = liftM3 SStore subWord subWord subStore
  where
    subStore = genStorage (sz `div` 10)
    subWord = defaultWord (sz `div` 5)

data Invocation
  = SolidityCall Text [AbiValue]
  deriving Show

assertSolidityComputation :: Invocation -> AbiValue -> IO ()
assertSolidityComputation (SolidityCall s args) x =
  do y <- runStatements s args (abiValueType x)
     assertEqual (T.unpack s)
       (fmap Bytes (Just (encodeAbiValue x)))
       (fmap Bytes y)

bothM :: (Monad m) => (a -> m b) -> (a, a) -> m (b, b)
bothM f (a, a') = do
  b  <- f a
  b' <- f a'
  return (b, b')

applyPattern :: String -> TestTree  -> TestTree
applyPattern p = localOption (TestPattern (parseExpr p))

reachableUserAsserts :: ByteString -> Maybe Sig -> IO (Maybe [SMTCex])
reachableUserAsserts c sig = do
  (_, res) <- withSolvers Z3 1 Nothing $ \s ->
    verifyContract s c sig [] debugVeriOpts Nothing (Just $ checkAssertions [0x01])
  mapMaybe getCex res
