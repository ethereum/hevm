{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Control.Monad.State.Strict (liftIO)
import Data.Aeson qualified as JSON
import Data.ByteString.UTF8 as BSU 
import Data.ByteString qualified as ByteString
import Data.Either
import Data.Function
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.String.Here
import EVM
import EVM.ABI
import EVM.Effects (App, runApp)
import EVM.Fetch qualified as Fetch
import EVM.Format
import EVM.Sign
import EVM.Solidity
import EVM.Stepper qualified as Stepper
import EVM.Test.Tracing
import EVM.Transaction qualified
import EVM.Types
import EVM.UnitTest
import GHC.Word
import System.Directory (setCurrentDirectory)
import System.FilePath.Find qualified as Find
import System.IO.Temp
import System.Process (readProcessWithExitCode)
import Test.Tasty.Bench
import Control.Monad.ST
import EVM.FeeSchedule (feeSchedule)

-- benchmark hevm and EVM tool on the folder called benchmarks
-- using tasty-bench

vmFromByteString :: App m => ByteString -> m (VM Concrete RealWorld)
vmFromByteString = vmFromRawByteString . fromJust . hexByteString

vmFromRawByteString :: App m => ByteString -> m (VM Concrete RealWorld)
vmFromRawByteString bs = liftIO $
  bs
    & ConcreteRuntimeCode
    & RuntimeCode
    & initialContract
    & vm0
    & stToIO
    & fmap EVM.Transaction.initTx

vm0 :: Contract -> ST s (VM Concrete s)
vm0 c = makeVm $ vm0Opts c

vm0Opts :: Contract -> VMOpts Concrete
vm0Opts c =
  VMOpts
    { contract = c,
      calldata = (ConcreteBuf "", []),
      value = Lit 0xfffffffffffff, -- balance
      baseState = EmptyBase,
      address = LitAddr 0xacab,
      caller = LitAddr 0,
      origin = LitAddr 0,
      gas = 0xffffffffffffffff,
      baseFee = 0,
      priorityFee = 0,
      gaslimit = 0xffffffffffffffff,
      coinbase = LitAddr 0,
      number = Lit 0,
      timestamp = Lit 0,
      blockGaslimit = 0xffffffffffffffff,
      gasprice = 0,
      maxCodeSize = 0xffffffff,
      prevRandao = 0,
      schedule = feeSchedule,
      chainId = 1,
      create = False,
      txAccessList = mempty, -- TODO: support me soon
      allowFFI = False,
      otherContracts = [],
      freshAddresses = 0,
      beaconRoot = 0
    }

benchCode :: ByteString -> Benchmark
benchCode bs = bench "interpret" $ nfIO $ runApp $ do
  vm <- vmFromByteString bs
  isRight <$> Stepper.interpret (Fetch.zero 0 Nothing) vm Stepper.execFully

benchFile :: FilePath -> Benchmark
benchFile path = bench (show path) $ nfIO $ runApp $ do
  bs <- liftIO $ strip0x <$> ByteString.readFile path
  vm <- vmFromByteString bs
  isRight <$> Stepper.interpret (Fetch.zero 0 Nothing) vm Stepper.execFully

-- bench every .bin file in a given folder
benchFolder :: FilePath -> IO [Benchmark]
benchFolder path = map benchFile <$> Find.find Find.always (Find.extension Find.==? ".bin") path

-- why do we need this?
vmOptsToTestVMParams :: VMOpts Concrete -> TestVMParams
vmOptsToTestVMParams v =
  TestVMParams
    { address = v.address,
      caller = v.caller,
      origin = v.origin,
      gasCreate = v.gas,
      gasCall = v.gas,
      baseFee = v.baseFee,
      priorityFee = v.priorityFee,
      balanceCreate = case v.value of
        Lit x -> x
        _ -> 0,
      coinbase = v.coinbase,
      number = case v.number of
        Lit x -> x
        _ -> 0,
      timestamp = case v.timestamp of
        Lit x -> x
        _ -> 0,
      gaslimit = v.gaslimit,
      gasprice = v.gasprice,
      maxCodeSize = v.maxCodeSize,
      prevrandao = v.prevRandao,
      chainId = v.chainId
    }

callMainForBytecode :: App m => ByteString -> m (Either EvmError (Expr 'Buf))
callMainForBytecode bs = do
  vm <- vmFromRawByteString bs
  Stepper.interpret (Fetch.zero 0 Nothing) vm (Stepper.evm (abiCall (vmOptsToTestVMParams (vm0Opts (initialContract (RuntimeCode (ConcreteRuntimeCode bs))))) (Left ("main()", emptyAbi))) >> Stepper.execFully)

benchMain :: (String, ByteString) -> Benchmark
benchMain (name, bs) = bench name $ nfIO $ runApp $ (\x -> if isRight x then () else internalError "failed") <$> callMainForBytecode bs

benchBytecodes :: [ByteString] -> [Benchmark]
benchBytecodes = map (\x -> bench "bytecode" $ nfIO $ runApp (do
                                                       vm <- vmFromRawByteString x
                                                       isRight <$> (Stepper.interpret (Fetch.zero 0 Nothing) vm Stepper.execFully)))

callMain :: TestVMParams -> EVM Concrete s ()
callMain params = makeTxCall params (ConcreteBuf (abiMethod "main()" emptyAbi), [])

evmSetup' :: [Word8] -> ByteString -> (EVM.Transaction.Transaction, EVMToolEnv, EVMToolAlloc, Addr, Addr, Integer)
evmSetup' contr txData = (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk)
  where
    bitcode = ByteString.pack contr
    contrAlloc =
      EVMToolAlloc
        { balance = 0xffffffffffffff,
          code = bitcode,
          nonce = 0x48
        }
    txn =
      EVM.Transaction.Transaction
        { txdata = txData,
          gasLimit = 0xffffffffffffff,
          gasPrice = Just 1,
          nonce = 172,
          toAddr = Just 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192,
          r = 0, -- will be fixed when we sign
          s = 0, -- will be fixed when we sign
          v = 0, -- will be fixed when we sign
          value = 0, -- setting this > 0 fails because HEVM doesn't handle value sent in toplevel transaction
          txtype = EVM.Transaction.EIP1559Transaction,
          accessList = [],
          maxPriorityFeeGas = Just 1,
          maxFeePerGas = Just 1,
          chainId = 1
        }
    evmEnv =
      EVMToolEnv
        { coinbase = 0xff,
          timestamp = Lit 0x3e8,
          number = Lit 0x0,
          gasLimit = 0xffffffffffffff,
          baseFee = 0x0,
          maxCodeSize = 0xfffff,
          schedule = feeSchedule,
          blockHashes = blockHashesDefault,
          withdrawals = mempty,
          currentRandom = 42,
          parentBeaconBlockRoot = 5
        }
    sk = 0xDC38EE117CAE37750EB1ECC5CFD3DE8E85963B481B93E732C5D0CB66EE6B0C9D
    fromAddress :: Addr
    fromAddress = fromJust $ deriveAddr sk
    toAddress :: Addr
    toAddress = 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192

runGethOnFile :: FilePath -> IO Benchmark
runGethOnFile path = do
  bs <- fromJust . hexByteString . strip0x <$> ByteString.readFile path
  let contr = ByteString.unpack bs
  let (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk) = evmSetup' contr mempty
      txs = [EVM.Transaction.sign sk txn]
      walletAlloc =
        EVMToolAlloc
          { balance = 0x5ffd4878be161d74,
            code = mempty,
            nonce = 0xac
          }
      alloc :: Map.Map Addr EVMToolAlloc
      alloc = Map.fromList ([(fromAddress, walletAlloc), (toAddress, contrAlloc)])

  -- do each benchmark in a temporary directory
  pure $
    bench (show path) $
      nfIO $
        withTempDirectory
          "/tmp"
          "name"
          ( \dir -> do
              setCurrentDirectory dir
              JSON.encodeFile "txs.json" txs
              JSON.encodeFile "alloc.json" alloc
              JSON.encodeFile "env.json" evmEnv
              readProcessWithExitCode
                "evm"
                [ "transition",
                  "--input.alloc",
                  "alloc.json",
                  "--input.env",
                  "env.json",
                  "--input.txs",
                  "txs.json"
                ]
                ""
          )

benchEVMTool :: FilePath -> IO Benchmark
benchEVMTool path = runGethOnFile path

benchEVMToolFolder :: FilePath -> IO [Benchmark]
benchEVMToolFolder path = do
  files <- Find.find Find.always (Find.extension Find.==? ".bin") path
  mapM benchEVMTool files

mkBench :: (Int -> IO a) -> [Int] -> IO [(String, a)]
mkBench f l = mapM (\n -> (show n,) <$> f n) l

main :: IO ()
main = do
  let f (name, prog) = do
        ll <- mkBench prog [2 ^ n | n :: Int <- [1 .. 14]]
        pure $ bgroup name (benchMain <$> ll)
  let benchmarks = [ 
                     ("loop", simpleLoop)
                   , ("primes", primes)
                   , ("hashes", hashes)
                   , ("hashmem", hashmem)
                   , ("balanceTransfer", balanceTransfer)
                   , ("funcCall", funcCall)
                   , ("contractCreation", contractCreation)
                   , ("contractCreationMem", contractCreationMem)
                   ]
  defaultMain =<< mapM f benchmarks
  

-- Loop that adds up n numbers
simpleLoop :: Int -> IO ByteString
simpleLoop n = do
  let src =
        [i|
          contract A {
            function main() public {
              uint256 acc = 0;
              for (uint i = 0; i < ${n}; i++) {
                acc += i;
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Computes prime numbers and stores them up to n.
primes :: Int -> IO ByteString
primes n = do
  let src =
        [i|
          contract A {
            mapping (uint => uint) public primes;
            function isPrime (uint n) public returns (bool) {
              if (n == 2) {
                return true;
              }
              if (n % 2 == 0) {
                return false;
              }
              for (uint i = 3; i * i < n; i += 2) {
                if (n % i == 0) {
                  return false;
                }
              }
              return true;
            }
            
            function main() public {
              uint n = 0;
              for (uint i = 0; i < ${n}; i++) {
                if (isPrime(i)) {
                  primes[n++] = i;
                }
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Program that repeatedly hashes a value
hashes :: Int -> IO ByteString
hashes n = do
  let src =
        [i|
          contract A {
            function main() public {
              bytes32 h = 0;
              for (uint i = 0; i < ${n}; i++) {
                h = keccak256(abi.encode(h));
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- Program that repeatedly hashes a value and stores it in a map
hashmem :: Int -> IO ByteString
hashmem n = do
  let src =
        [i|
          contract A {
            mapping (uint256 => uint256) public map;
            function main() public {
              uint256 h = 0;
              for (uint i = 0; i < ${n}; i++) {
                uint256 x = h;
                h = uint256(keccak256(abi.encode(h)));
                map[x] = h;
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

balanceTransfer :: Int -> IO ByteString
balanceTransfer n = do
  let src =
        [i|
          contract A {
            function main() public {
              address payable to = payable(address(0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192)); 
              for (uint i = 0; i < ${n}; i++) {
                to.transfer(1);
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

funcCall :: Int -> IO ByteString
funcCall n = do
  let src =
        [i|
          contract A {
            uint256 public acc;
            function f(uint256 x) public {
              acc += x;
            }
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                f(i);
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

-- creates n contracts
contractCreation :: Int -> IO ByteString
contractCreation n = do
  let src =
        [i|
          contract B { }
          contract A {
            B public b;
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                b = new B();
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)

contractCreationMem :: Int -> IO ByteString
contractCreationMem n = do
  let src =
        [i|
          contract B { string m = "the quick brown fox jumps over the lazy dog"; }
          contract A {
            B public b;
            function main() public {
              for (uint i = 0; i < ${n}; i++) {
                b = new B();
              }
            }
          }
        |]
  fmap fromJust (runApp $ solcRuntime "A" src)
