{-# Language GADTs #-}
{-# Language NumericUnderscores #-}
{-# Language QuasiQuotes #-}
{-# Language DataKinds #-}

module Main where

import Data.Text (Text)
import Data.ByteString (ByteString)
import Data.Bits hiding (And, Xor)
import System.Directory
import GHC.Natural
import Control.Monad
import Text.RE.TDFA.String
import Text.RE.Replace
import Data.Time
import System.Environment

import Prelude hiding (fail, LT, GT)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as Hex
import Data.Maybe
import Data.Typeable
import Data.List (elemIndex)
import Data.DoubleWord
import Test.Tasty
import Test.Tasty.QuickCheck hiding (Failure)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty.HUnit
import Test.Tasty.Runners hiding (Failure)
import Test.Tasty.ExpectedFailure

import Control.Monad.State.Strict (execState, runState)
import Control.Lens hiding (List, pre, (.>), re)

import qualified Data.Vector as Vector
import Data.String.Here
import qualified Data.Map.Strict as Map

import Data.Binary.Put (runPut)
import Data.Binary.Get (runGetOrFail)

import EVM hiding (Query, allowFFI)
import EVM.SymExec
import EVM.ABI
import EVM.Exec
import qualified EVM.Patricia as Patricia
import EVM.Precompiled
import EVM.RLP
import EVM.Solidity
import EVM.Types
import EVM.Traversals
import EVM.SMT hiding (one)
import qualified EVM.Expr as Expr
import qualified Data.Text as T
import Data.List (isSubsequenceOf)
import EVM.TestUtils

main :: IO ()
main = defaultMain tests

-- | run a subset of tests in the repl. p is a tasty pattern:
-- https://github.com/UnkindPartition/tasty/tree/ee6fe7136fbcc6312da51d7f1b396e1a2d16b98a#patterns
runSubSet :: String -> IO ()
runSubSet p = defaultMain . applyPattern p $ tests

tests :: TestTree
tests = testGroup "hevm"
  [ testGroup "StorageTests"
    [ testCase "read-from-sstore" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (Lit 0x0) (SStore (Lit 0x0) (Lit 0x0) (Lit 0xab) AbstractStore))
    , testCase "read-from-concrete" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])]))
    , testCase "read-past-abstract-writes-to-different-address" $ assertEqual ""
        (Lit 0xab)
        (Expr.readStorage' (Lit 0x0) (Lit 0x0) (SStore (Lit 0x1) (Var "a") (Var "b") (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])])))
    , testCase "abstract-slots-block-reads-for-same-address" $ assertEqual ""
        (SLoad (Lit 0x0) (Lit 0x0) (SStore (Lit 0x0) (Var "b") (Var "c") (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])])))
        (Expr.readStorage' (Lit 0x0) (Lit 0x0)
          (SStore (Lit 0x1) (Var "1312") (Var "acab") (SStore (Lit 0x0) (Var "b") (Var "c") (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])]))))
    , testCase "abstract-addrs-block-reads" $ assertEqual ""
        (SLoad (Lit 0x0) (Lit 0x0) (SStore (Var "1312") (Lit 0x0) (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])])))
        (Expr.readStorage' (Lit 0x0) (Lit 0x0)
          (SStore (Lit 0xacab) (Lit 0xdead) (Lit 0x0) (SStore (Var "1312") (Lit 0x0) (Lit 0x0) (ConcreteStore $ Map.fromList [(0x0, Map.fromList [(0x0, 0xab)])]))))
    ]
  -- These tests fuzz the simplifier by generating a random expression,
  -- applying some simplification rules, and then using the smt encoding to
  -- check that the simplified version is semantically equivalent to the
  -- unsimplified one
  , testGroup "SimplifierTests"
    [ testProperty "buffer-simplification" $ \(expr :: Expr Buf) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "store-simplification" $ \(expr :: Expr Storage) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "byte-simplification" $ \(expr :: Expr Byte) -> ioProperty $ do
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "word-simplification" $ \(_ :: Int) -> ioProperty $ do
        expr <- generate . sized $ genWord 0 -- we want a lower frequency of lits for this test
        let simplified = Expr.simplify expr
        checkEquiv expr simplified
    , testProperty "readStorage-equivalance" $ \(store, addr, slot) -> ioProperty $ do
        let simplified = Expr.readStorage' addr slot store
            full = SLoad addr slot store
        checkEquiv simplified full
    , testProperty "writeStorage-equivalance" $ \(addr, slot, val) -> ioProperty $ do
        let mkStore = oneof
              [ pure EmptyStore
              , fmap ConcreteStore arbitrary
              , do
                  -- generate some write chains where we know that at least one
                  -- write matches either the input addr, or both the input
                  -- addr and slot
                  let matchAddr = liftM2 (SStore addr) arbitrary arbitrary
                      matchBoth = fmap (SStore addr slot) arbitrary
                      addWrites :: Expr Storage -> Int -> Gen (Expr Storage)
                      addWrites b 0 = pure b
                      addWrites b n = liftM4 SStore arbitrary arbitrary arbitrary (addWrites b (n - 1))
                  s <- arbitrary
                  addMatch <- oneof [ matchAddr, matchBoth ]
                  let withMatch = addMatch s
                  newWrites <- oneof [ pure 0, pure 1, fmap (`mod` 5) arbitrary ]
                  addWrites withMatch newWrites
              , arbitrary
              ]
        store <- generate mkStore
        let simplified = Expr.writeStorage addr slot val store
            full = SStore addr slot val store
        checkEquiv simplified full
    , testProperty "readWord-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readWord idx buf
            full = ReadWord idx buf
        checkEquiv simplified full
    , testProperty "writeWord-equivalance" $ \(idx, val) -> ioProperty $ do
        let mkBuf = oneof
              [ pure $ ConcreteBuf ""       -- empty
              , fmap ConcreteBuf arbitrary  -- concrete
              , sized (genBuf 100)          -- overlapping writes
              , arbitrary                   -- sparse writes
              ]
        buf <- generate mkBuf
        let simplified = Expr.writeWord idx val buf
            full = WriteWord idx val buf
        checkEquiv simplified full
    , testProperty "readByte-equivalance" $ \(buf, idx) -> ioProperty $ do
        let simplified = Expr.readByte idx buf
            full = ReadByte idx buf
        checkEquiv simplified full
    -- we currently only simplify concrete writes over concrete buffers so that's what we test here
    , testProperty "writeByte-equivalance" $ \(LitOnly val, LitOnly buf) -> ioProperty $ do
        idx <- generate $ frequency
          [ (10, genLit (fromIntegral (1_000_000 :: Int)))  -- can never overflow an Int
          , (1, fmap Lit arbitrary)                         -- can overflow an Int
          ]
        let simplified = Expr.writeByte idx val buf
            full = WriteByte idx val buf
        checkEquiv simplified full
    , testProperty "copySlice-equivalance" $ \(srcOff) -> ioProperty $ do
        -- we bias buffers to be concrete more often than not
        let mkBuf = oneof
              [ pure $ ConcreteBuf ""
              , fmap ConcreteBuf arbitrary
              , arbitrary
              ]
        src <- generate mkBuf
        dst <- generate mkBuf
        size <- generate (genLit 300)
        dstOff <- generate (maybeBoundedLit 100_000)
        let simplified = Expr.copySlice srcOff dstOff size src dst
            full = CopySlice srcOff dstOff size src dst
        checkEquiv simplified full
    , testProperty "indexWord-equivalence" $ \(src) -> ioProperty $ do
        idx <- generate (genLit 50)
        let simplified = Expr.indexWord idx src
            full = IndexWord idx src
        checkEquiv simplified full
    , testProperty "indexWord-mask-equivalence" $ \(src :: Expr EWord) -> ioProperty $ do
        idx <- generate (genLit 35)
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
      let
        w :: Int -> W256
        w x = W256 $ EVM.Types.word256 $ BS.pack [fromIntegral x]
      in
      assertEqual ""
        (EVM.SMT.encodeConcreteStore $
          Map.fromList [(w 1, (Map.fromList [(w 2, w 99), (w 2, w 100)]))])
        "(sstore (_ bv1 256) (_ bv2 256) (_ bv100 256) emptyStore)"
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
  , testGroup "Solidity expressions"
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
          -- traceM ("encoding: " ++ (show y) ++ " : " ++ show (abiValueType y))
          Just encoded <- runStatements [i| x = abi.encode(a);|]
            [y] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ Vector.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (Vector.toList -> [e]) -> e
                _ -> error "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ Vector.fromList [y])
          -- traceM ("encoded (solidity): " ++ show solidityEncoded)
          -- traceM ("encoded (hevm): " ++ show (AbiBytesDynamic hevmEncoded))
          assertEqual "abi encoding mismatch" solidityEncoded (AbiBytesDynamic hevmEncoded)

    , testProperty "abi encoding vs. solidity (2 args)" $ withMaxSuccess 20 $ forAll (arbitrary >>= bothM genAbiValue) $
      \(x', y') -> ioProperty $ do
          -- traceM ("encoding: " ++ (show x') ++ ", " ++ (show y')  ++ " : " ++ show (abiValueType x') ++ ", " ++ show (abiValueType y'))
          Just encoded <- runStatements [i| x = abi.encode(a, b);|]
            [x', y'] AbiBytesDynamicType
          let solidityEncoded = case decodeAbiValue (AbiTupleType $ Vector.fromList [AbiBytesDynamicType]) (BS.fromStrict encoded) of
                AbiTuple (Vector.toList -> [e]) -> e
                _ -> error "AbiTuple expected"
          let hevmEncoded = encodeAbiValue (AbiTuple $ Vector.fromList [x',y'])
          -- traceM ("encoded (solidity): " ++ show solidityEncoded)
          -- traceM ("encoded (hevm): " ++ show (AbiBytesDynamic hevmEncoded))
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
        let (solc', _, _) = fromJust $ readJSON json
            initCode :: ByteString
            initCode = fromJust $ solc' ^? ix (path' <> ":A") . creationCode
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
 , testGroup "Remote State Tests"
   [
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
       (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x01] c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x11] c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x12] c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        assertEqual "Division by 0 needs b=0" (getVar ctr "arg2") 0
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
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x21] c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
        a <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x31] c (Just ("fun(uint8)", [AbiUIntType 8])) [] defaultVeriOpts
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
        (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x32] c (Just ("fun(uint8)", [AbiUIntType 8])) [] defaultVeriOpts
        assertBool "Access must be beyond element 2" $ (getVar ctr "arg1") > 1
        putStrLn "expected counterexample found"
      ,
      -- TODO the system currently does not allow for symbolic array size allocation
      expectFail $ testCase "alloc-too-much" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 a) external {
                uint[] memory arr = new uint[](a);
              }
             }
            |]
        (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x41] c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "expected counterexample found"
      ,
      -- TODO the system currently does not allow for symbolic JUMP
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
        (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s [0x51] c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "expected counterexample found"
 ]

  , testGroup "Dapp Tests"
    [ testCase "Trivial-Pass" $ do
        let testFile = "test/contracts/pass/trivial.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Trivial-Fail" $ do
        let testFile = "test/contracts/fail/trivial.sol"
        runDappTest testFile "testFalse" >>= assertEqual "test result" False
    , testCase "Abstract" $ do
        let testFile = "test/contracts/pass/abstract.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Constantinople" $ do
        let testFile = "test/contracts/pass/constantinople.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Prove-Tests-Pass" $ do
        let testFile = "test/contracts/pass/dsProvePass.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Prove-Tests-Fail" $ do
        let testFile = "test/contracts/fail/dsProveFail.sol"
        runDappTest testFile "prove_trivial" >>= assertEqual "test result" False
        runDappTest testFile "prove_add" >>= assertEqual "test result" False
        --runDappTest testFile "prove_smtTimeout" >>= assertEqual "test result" False
        runDappTest testFile "prove_multi" >>= assertEqual "test result" False
        runDappTest testFile "prove_mul" >>= assertEqual "test result" False
        -- TODO: implement overflow checking optimizations and enable, currently this runs forever
        --runDappTest testFile "prove_distributivity" >>= assertEqual "test result" False
        runDappTest testFile "prove_transfer" >>= assertEqual "test result" False
    , testCase "Loop-Tests" $ do
        let testFile = "test/contracts/pass/loops.sol"
        runDappTestCustom testFile "prove_loop" (Just 10) False Nothing >>= assertEqual "test result" True
        runDappTestCustom testFile "prove_loop" (Just 100) False Nothing >>= assertEqual "test result" False
    , testCase "Invariant-Tests-Pass" $ do
        let testFile = "test/contracts/pass/invariants.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Invariant-Tests-Fail" $ do
        let testFile = "test/contracts/fail/invariantFail.sol"
        runDappTest testFile "invariantFirst" >>= assertEqual "test result" False
        runDappTest testFile "invariantCount" >>= assertEqual "test result" False
    , testCase "Cheat-Codes-Pass" $ do
        let testFile = "test/contracts/pass/cheatCodes.sol"
        runDappTest testFile ".*" >>= assertEqual "test result" True
    , testCase "Cheat-Codes-Fail" $ do
        let testFile = "test/contracts/fail/cheatCodes.sol"
        runDappTestCustom testFile "testBadFFI" Nothing False Nothing >>= assertEqual "test result" False
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(int256)", [AbiIntType 256])) [] defaultVeriOpts
        putStrLn "Require works as expected"
     ,
     testCase "ITE-with-bitwise-AND" $ do
        --- using ignore to suppress huge output
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
       (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
       putStrLn "expected counterexample found"
     ,
     testCase "ITE-with-bitwise-OR" $ do
        --- using ignore to suppress huge output
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
       (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
      let
        opts = VeriOpts
          { simp = False
          , debug = False
          , maxIter = Nothing
          , askSmtIters = Nothing
          , rpcInfo = Nothing
          }
        calldata' = Just ("checkval(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])
      (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
        checkAssert s defaultPanicCodes c calldata' [] opts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(int256,int256)", [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(int256,int256)", [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(int256,int256)", [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(int256,int256)", [AbiIntType 256, AbiIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "sdiv works as expected"
      ,
     testCase "opcode-div-zero-2" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint256 val) external pure {
                uint out;
                assembly {
                  out := div(0, val)
                }
                assert(out == 0);

              }
            }
            |]
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "sdiv works as expected"
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
        (_, [Qed _])  <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint8)", [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint8)", [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint8)", [AbiUIntType 256, AbiUIntType 8])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
        putStrLn "XOR works as expected"
      ,
      testCase "opcode-addmod-no-overflow" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint8 a, uint8 b, uint8 c) external pure {
                require(a < 4);
                require(b < 4);
                require(c < 4);
                uint16 r1;
                uint16 r2;
                uint16 g2;
                assembly {
                  r1 := add(a,b)
                  r2 := mod(r1, c)
                  g2 := addmod (a, b, c)
                }
                assert (r2 == g2);
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint8,uint8,uint8)", [AbiUIntType 8, AbiUIntType 8, AbiUIntType 8])) [] defaultVeriOpts
        putStrLn "ADDMOD is fine on NON overflow values"
      ,
      testCase "opcode-mulmod-no-overflow" $ do
        Just c <- solcRuntime "MyContract"
            [i|
            contract MyContract {
              function fun(uint8 a, uint8 b, uint8 c) external pure {
                require(a < 4);
                require(b < 4);
                require(c < 4);
                uint16 r1;
                uint16 r2;
                uint16 g2;
                assembly {
                  r1 := mul(a,b)
                  r2 := mod(r1, c)
                  g2 := mulmod (a, b, c)
                }
                assert (r2 == g2);
              }
            }
            |]
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint8,uint8,uint8)", [AbiUIntType 8, AbiUIntType 8, AbiUIntType 8])) [] defaultVeriOpts
        putStrLn "MULMOD is fine on NON overflow values"
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
        (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint16)", [AbiUIntType 16])) [] defaultVeriOpts
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
                                       _ -> error "expected 2 args"
                        in (x .<= Expr.add x y)
                           .&& view (state . callvalue) preVM .== Lit 0
            post prestate leaf =
              let (x, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> error "expected 2 args"
              in case leaf of
                   Return _ b _ -> (ReadWord (Lit 0) b) .== (Add x y)
                   _ -> PBool True
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> verifyContract s safeAdd (Just ("add(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts SymbolicS (Just pre) (Just post)
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
                                       _ -> error "expected 2 args"
                        in (x .<= Expr.add x y)
                           .&& (x .== y)
                           .&& view (state . callvalue) preVM .== Lit 0
            post prestate leaf =
              let (_, y) = case getStaticAbiArgs 2 prestate of
                             [x', y'] -> (x', y')
                             _ -> error "expected 2 args"
              in case leaf of
                   Return _ b _ -> (ReadWord (Lit 0) b) .== (Mul (Lit 2) y)
                   _ -> PBool True
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s ->
          verifyContract s safeAdd (Just ("add(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts SymbolicS (Just pre) (Just post)
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
        let pre vm = Lit 0 .== view (state . callvalue) vm
            post prestate leaf =
              let y = case getStaticAbiArgs 1 prestate of
                        [y'] -> y'
                        _ -> error "expected 1 arg"
                  this = Expr.litAddr $ view (state . codeContract) prestate
                  prex = Expr.readStorage' this (Lit 0) (view (env . storage) prestate)
              in case leaf of
                Return _ _ postStore -> Expr.add prex (Expr.mul (Lit 2) y) .== (Expr.readStorage' this (Lit 0) postStore)
                _ -> PBool True
        (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> verifyContract s c (Just ("f(uint256)", [AbiUIntType 256])) [] defaultVeriOpts SymbolicS (Just pre) (Just post)
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
            (res, [Qed _]) <- withSolvers Z3 4 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("hello(address)", [AbiAddressType])) [] defaultVeriOpts
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
          let pre vm = (Lit 0) .== view (state . callvalue) vm
              post prestate poststate =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = Expr.litAddr $ view (state . codeContract) prestate
                    prestore =  view (env . storage) prestate
                    prex = Expr.readStorage' this x prestore
                    prey = Expr.readStorage' this y prestore
                in case poststate of
                     Return _ _ poststore -> let
                           postx = Expr.readStorage' this x poststore
                           posty = Expr.readStorage' this y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> verifyContract s c (Just ("f(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts SymbolicS (Just pre) (Just post)
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
          let pre vm = (Lit 0) .== view (state . callvalue) vm
              post prestate poststate =
                let (x,y) = case getStaticAbiArgs 2 prestate of
                        [x',y'] -> (x',y')
                        _ -> error "expected 2 args"
                    this = Expr.litAddr $ view (state . codeContract) prestate
                    prestore =  view (env . storage) prestate
                    prex = Expr.readStorage' this x prestore
                    prey = Expr.readStorage' this y prestore
                in case poststate of
                     Return _ _ poststore -> let
                           postx = Expr.readStorage' this x poststore
                           posty = Expr.readStorage' this y poststore
                       in Expr.add prex prey .== Expr.add postx posty
                     _ -> PBool True
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> verifyContract s c (Just ("f(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts SymbolicS (Just pre) (Just post)
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          putStrLn $ "y:" <> show y
          putStrLn $ "x:" <> show x
          assertEqual "Catch storage collisions" x y
          putStrLn "expected counterexample found"
        ,
        testCase "Simple Assert" $ do
          Just c <- solcRuntime "C"
            [i|
            contract C {
              function foo() external pure {
                assert(false);
              }
             }
            |]
          (_, [Cex (l, _)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo()", [])) [] defaultVeriOpts
          assertEqual "incorrect revert msg" l (EVM.Types.Revert [] (ConcreteBuf $ panicMsg 0x01))
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
          (_, [(Cex (_, ctr))]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, a), Cex (_, b)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
          let ints = map (flip getVar "arg1") [a,b]
          assertBool "0 must be one of the Cex-es" $ isJust $ elemIndex 0 ints
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
          (_, [Cex (_, a), Cex (_, b)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex _, Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("fun(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("deposit(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s allPanicCodes c (Just ("deposit(uint8)", [AbiUIntType 8])) [] defaultVeriOpts
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
          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("foo(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        testCase "injectivity of keccak all pairs (32 bytes)" $ do
          Just c <- solcRuntime "A"
            [i|
            contract A {
              function f(uint x, uint y, uint z) public pure {
                bytes32 w; bytes32 u; bytes32 v;
                w = keccak256(abi.encode(x));
                u = keccak256(abi.encode(y));
                v = keccak256(abi.encode(z));
                if (w == u) assert(x==y);
                if (w == v) assert(x==z);
                if (u == v) assert(y==z);
              }
            }
            |]
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256,uint256,uint256)", [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
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
          (_, [Cex (_, ctr)]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256,uint256,uint256,uint256)", replicate 4 (AbiUIntType 256))) [] defaultVeriOpts
          let x = getVar ctr "arg1"
          let y = getVar ctr "arg2"
          let w = getVar ctr "arg3"
          let z = getVar ctr "arg4"
          assertEqual "x==y for hash collision" x y
          assertEqual "w==z for hash collision" w z
          putStrLn "expected counterexample found"
        ,
        expectFail $ testCase "calldata beyond calldatasize is 0 (z3)" $ do
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
        ignoreTest $ testCase "keccak soundness" $ do
        --- using ignore to suppress huge output
          Just c <- solcRuntime "C"
            [i|
              contract C {
                mapping (uint => mapping (uint => uint)) maps;

                  function f(uint x, uint y) public view {
                  assert(maps[y][0] == maps[x][0]);
                }
              }
            |]

          -- should find a counterexample
          (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256,uint256)", [AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLn "expected counterexample found"
        ,
        testCase "multiple-contracts" $ do
          let code' =
                [i|
                  contract C {
                    uint x;
                    A constant a = A(0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B);

                    function call_A() public view {
                      // should fail since a.x() can be anything
                      assert(a.x() == x);
                    }
                  }
                  contract A {
                    uint public x;
                  }
                |]
              aAddr = Addr 0x35D1b3F3D7966A1DFe207aa4514C12a259A0492B
          Just c <- solcRuntime "C" code'
          Just a <- solcRuntime "A" code'
          (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> do
            let vm0 = abstractVM (Just ("call_A()", [])) [] c Nothing SymbolicS
            let vm = vm0
                  & set (state . callvalue) (Lit 0)
                  & over (env . contracts)
                       (Map.insert aAddr (initialContract (RuntimeCode (ConcreteRuntimeCode a))))
                  -- NOTE: this used to as follows, but there is no _storage field in Contract record
                  -- (Map.insert aAddr (initialContract (RuntimeCode $ ConcreteBuffer a) &
                  --                     set EVM.storage (EVM.Symbolic [] store)))
            verify s defaultVeriOpts vm (Just $ checkAssertions defaultPanicCodes)
          putStrLn "found counterexample:"
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
          (_, [Cex _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("call_A()", [])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("kecc(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
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
          (res, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("f(uint256)", [AbiUIntType 256])) [] defaultVeriOpts
          putStrLn $ "successfully explored: " <> show (Expr.numBranches res) <> " paths"
        ,
        ignoreTest $ testCase "safemath distributivity (yul)" $ do
          let yulsafeDistributivity = hex "6355a79a6260003560e01c14156016576015601f565b5b60006000fd60a1565b603d602d604435600435607c565b6039602435600435607c565b605d565b6052604b604435602435605d565b600435607c565b141515605a57fe5b5b565b6000828201821115151560705760006000fd5b82820190505b92915050565b6000818384048302146000841417151560955760006000fd5b82820290505b92915050565b"
          let vm =  abstractVM (Just ("distributivity(uint256,uint256,uint256)", [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] yulsafeDistributivity Nothing SymbolicS
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

          (_, [Qed _]) <- withSolvers Z3 1 Nothing $ \s -> checkAssert s defaultPanicCodes c (Just ("distributivity(uint256,uint256,uint256)", [AbiUIntType 256, AbiUIntType 256, AbiUIntType 256])) [] defaultVeriOpts
          putStrLn "Proven"
 ]
  , testGroup "Equivalence checking"
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
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts Nothing
          assertBool "Must have a difference" (not (null a))
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
                    b =  x<<1;
                  }
                }
              }
          |]
        withSolvers Z3 3 Nothing $ \s -> do
          a <- equivalenceCheck s aPrgm bPrgm defaultVeriOpts Nothing
          assertEqual "Must have no difference" [] a
          return ()
      ,
      testCase "eq-sol-exp-cex" $ do
        -- These yul programs are not equivalent: (try --calldata $(seth --to-uint256 2) for example)
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
          let myVeriOpts = VeriOpts{ simp = True, debug = False, maxIter = Just 2, askSmtIters = Just 2, rpcInfo = Nothing}
          a <- equivalenceCheck s aPrgm bPrgm myVeriOpts Nothing
          assertEqual "Must be different" (containsA (Cex ()) a) True
          return ()
      , testCase "eq-all-yul-optimization-tests" $ do
        let myVeriOpts = VeriOpts{ simp = True, debug = False, maxIter = Just 5, askSmtIters = Just 20, rpcInfo = Nothing }
            ignoredTests = [
                      "controlFlowSimplifier/terminating_for_nested.yul"
                    , "controlFlowSimplifier/terminating_for_nested_reversed.yul"

                    -- unbounded loop --
                    , "commonSubexpressionEliminator/branches_for.yul"
                    , "commonSubexpressionEliminator/loop.yul"
                    , "conditionalSimplifier/clear_after_if_continue.yul"
                    , "conditionalSimplifier/no_opt_if_break_is_not_last.yul"
                    , "conditionalUnsimplifier/clear_after_if_continue.yul"
                    , "conditionalUnsimplifier/no_opt_if_break_is_not_last.yul"
                    , "expressionSimplifier/inside_for.yul"
                    , "forLoopConditionIntoBody/cond_types.yul"
                    , "forLoopConditionIntoBody/simple.yul"
                    , "fullSimplify/inside_for.yul"
                    , "fullSuite/devcon_example.yul"
                    , "fullSuite/loopInvariantCodeMotion.yul"
                    , "fullSuite/no_move_loop_orig.yul"
                    , "loadResolver/loop.yul"
                    , "loopInvariantCodeMotion/multi.yul"
                    , "loopInvariantCodeMotion/recursive.yul"
                    , "loopInvariantCodeMotion/simple.yul"
                    , "redundantAssignEliminator/for_branch.yul"
                    , "redundantAssignEliminator/for_break.yul"
                    , "redundantAssignEliminator/for_continue.yul"
                    , "redundantAssignEliminator/for_decl_inside_break_continue.yul"
                    , "redundantAssignEliminator/for_deep_noremove.yul"
                    , "redundantAssignEliminator/for_deep_simple.yul"
                    , "redundantAssignEliminator/for_multi_break.yul"
                    , "redundantAssignEliminator/for_nested.yul"
                    , "redundantAssignEliminator/for_rerun.yul"
                    , "redundantAssignEliminator/for_stmnts_after_break_continue.yul"
                    , "rematerialiser/branches_for1.yul"
                    , "rematerialiser/branches_for2.yul"
                    , "rematerialiser/for_break.yul"
                    , "rematerialiser/for_continue.yul"
                    , "rematerialiser/for_continue_2.yul"
                    , "rematerialiser/for_continue_with_assignment_in_post.yul"
                    , "rematerialiser/no_remat_in_loop.yul"
                    , "ssaTransform/for_reassign_body.yul"
                    , "ssaTransform/for_reassign_init.yul"
                    , "ssaTransform/for_reassign_post.yul"
                    , "ssaTransform/for_simple.yul"
                    , "loopInvariantCodeMotion/nonMovable.yul"
                    , "unusedAssignEliminator/for_rerun.yul"
                    , "unusedAssignEliminator/for_continue_3.yul"
                    , "unusedAssignEliminator/for_deep_simple.yul"
                    , "ssaTransform/for_def_in_init.yul"
                    , "rematerialiser/many_refs_small_cost_loop.yul"
                    , "loopInvariantCodeMotion/no_move_state_loop.yul"
                    , "loopInvariantCodeMotion/dependOnVarInLoop.yul"
                    , "forLoopInitRewriter/empty_pre.yul"
                    , "loadResolver/keccak_crash.yul"
                    , "blockFlattener/for_stmt.yul" -- symb input can loop it forever
                    , "unusedAssignEliminator/for.yul" -- not infinite, just 2**256-3
                    , "loopInvariantCodeMotion/no_move_state.yul" -- not infinite, but rollaround on a large int
                    , "loopInvariantCodeMotion/non-ssavar.yul" -- same as above
                    , "forLoopInitRewriter/complex_pre.yul"
                    , "rematerialiser/some_refs_small_cost_loop.yul" -- not infinite but 100 long
                    , "forLoopInitRewriter/simple.yul"
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
                    , "ssaAndBack/multi_assign.yul"
                    , "ssaAndBack/multi_assign_if.yul"
                    , "ssaAndBack/multi_assign_switch.yul"
                    , "ssaAndBack/simple.yul"
                    , "ssaReverser/simple.yul"

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
                    , "varNameCleaner/function_names.yul"

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

                    -- Takes too long, would timeout on most test setups.
                    -- We could probably fix these by "bunching together" queries
                    , "fullSuite/clear_after_if_continue.yul"
                    , "reasoningBasedSimplifier/smod.yul"
                    , "reasoningBasedSimplifier/mulmod.yul"

                    -- TODO check what's wrong with these!
                    , "unusedStoreEliminator/create_inside_function.yul"
                    , "fullSimplify/not_applied_removes_non_constant_and_not_movable.yul" -- create bug?
                    , "unusedStoreEliminator/create.yul" -- create bug?
                    , "fullSuite/extcodelength.yul" -- extcodecopy bug?
                    , "loadResolver/keccak_short.yul" -- keccak bug
                    , "reasoningBasedSimplifier/signed_division.yul" -- ACTUAL bug, SDIV I think?
                    ]

        solcRepo <- fromMaybe (error "cannot find solidity repo") <$> (lookupEnv "HEVM_SOLIDITY_REPO")
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
        --
        let filesFiltered = filter (\file -> not $ any (\filt -> Data.List.isSubsequenceOf filt file) ignoredTests) files
        --
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
            symbolicMem _ = error "Program too short"

            unfiltered = lines origcont
            filteredASym = symbolicMem [ x | x <- unfiltered, (not $ x =~ [re|^//|]) && (not $ x =~ [re|^$|]) ]
            filteredBSym = symbolicMem [ replaceAll "" $ x *=~[re|^//|] | x <- onlyAfter [re|^// step:|] unfiltered, not $ x =~ [re|^$|] ]
          start <- getCurrentTime
          putStrLn $ "Checking file: " <> f
          when (debug myVeriOpts) $ do
            putStrLn "-------------Original Below-----------------"
            mapM_ putStrLn unfiltered
            putStrLn "------------- Filtered A + Symb below-----------------"
            mapM_ putStrLn filteredASym
            putStrLn "------------- Filtered B + Symb below-----------------"
            mapM_ putStrLn filteredBSym
            putStrLn "------------- END -----------------"
          Just aPrgm <- yul "" $ T.pack $ unlines filteredASym
          Just bPrgm <- yul "" $ T.pack $ unlines filteredBSym
          withSolvers CVC5 6 (Just 3) $ \s -> do
            res <- equivalenceCheck s aPrgm bPrgm myVeriOpts Nothing
            end <- getCurrentTime
            case containsA (Cex()) res of
              False -> do
                print $ "OK. Took " <> (show $ diffUTCTime end start) <> " seconds"
                let timeouts = filter (\(_, _, c) -> c == EVM.SymExec.Timeout()) res
                unless (null timeouts) $ putStrLn $ "But " <> (show $ length timeouts) <> " timeout(s) occurred"
              True -> do
                putStrLn $ "Not OK: " <> show f <> " Got: " <> show res
                error "Was NOT equivalent, error"
           )
    ]
  ]
  where
    (===>) = assertSolidityComputation


checkEquiv :: (Typeable a) => Expr a -> Expr a -> IO Bool
checkEquiv l r = withSolvers Z3 1 (Just 100) $ \solvers -> do
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
         EVM.SMT.Unknown -> True
         Sat _ -> False
         Error _ -> False


runSimpleVM :: ByteString -> ByteString -> Maybe ByteString
runSimpleVM x ins = case loadVM x of
                      Nothing -> Nothing
                      Just vm -> let calldata' = (ConcreteBuf ins)
                       in case runState (assign (state.calldata) calldata' >> exec) vm of
                            (VMSuccess (ConcreteBuf bs), _) -> Just bs
                            _ -> Nothing

loadVM :: ByteString -> Maybe VM
loadVM x =
    case runState exec (vmForEthrunCreation x) of
       (VMSuccess (ConcreteBuf targetCode), vm1) -> do
         let target = view (state . contract) vm1
             vm2 = execState (replaceCodeOfSelf (RuntimeCode (ConcreteRuntimeCode targetCode))) vm1
         return $ snd $ flip runState vm2
                (do resetState
                    assign (state . gas) 0xffffffffffffffff -- kludge
                    loadContract target)
       _ -> Nothing

hex :: ByteString -> ByteString
hex s =
  case Hex.decode s of
    Right x -> x
    Left e -> error e

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
  return $ runSimpleVM x input

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
  let cd = view (state . calldata) vm
  in decodeStaticArgs 4 n cd

-- includes shaving off 4 byte function sig
decodeAbiValues :: [AbiType] -> ByteString -> [AbiValue]
decodeAbiValues types bs =
  let xy = case decodeAbiValue (AbiTupleType $ Vector.fromList types) (BS.fromStrict (BS.drop 4 bs)) of
        AbiTuple xy' -> xy'
        _ -> error "AbiTuple expected"
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

instance Arbitrary Word256 where
  arbitrary = liftM2 fromHiAndLo arbitrary arbitrary

instance Arbitrary W256 where
  arbitrary = fmap W256 arbitrary

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

newtype LitOnly a = LitOnly a
  deriving (Show, Eq)

instance Arbitrary (LitOnly (Expr Byte)) where
  arbitrary = LitOnly . LitByte <$> arbitrary

instance Arbitrary (LitOnly (Expr EWord)) where
  arbitrary = LitOnly . Lit <$> arbitrary

instance Arbitrary (LitOnly (Expr Buf)) where
  arbitrary = LitOnly . ConcreteBuf <$> arbitrary

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
genNat = fmap fromIntegral (arbitrary :: Gen Natural)

genName :: Gen Text
-- In order not to generate SMT reserved words, we prepend with "esc_"
genName = fmap (T.pack . ("esc_" <> )) $ listOf1 (oneof . (fmap pure) $ ['a'..'z'] <> ['A'..'Z'])

genEnd :: Int -> Gen (Expr End)
genEnd 0 = oneof
 [ pure $ Failure [] Invalid
 , pure $ Failure [] EVM.Types.IllegalOverflow
 , pure $ Failure [] SelfDestruct
 ]
genEnd sz = oneof
 [ fmap (EVM.Types.Revert []) subBuf
 , liftM3 Return (return []) subBuf subStore
 , liftM3 ITE subWord subEnd subEnd
 ]
 where
   subBuf = defaultBuf (sz `div` 2)
   subStore = genStorage (sz `div` 2)
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
      , fmap CallValue genNat
      , fmap Caller genNat
      , fmap Address genNat
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
    , liftM3 SLoad subWord subWord subStore
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
  [ pure AbstractStore
  , pure EmptyStore
  --, fmap ConcreteStore arbitrary
  ]
genStorage sz = liftM4 SStore subWord subWord subWord subStore
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
