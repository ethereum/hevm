{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Control.Monad.State.Strict (liftIO)
import Data.ByteString.UTF8 as BSU 
import Data.Either
import Data.Function
import Data.Maybe
import Data.String.Here
import EVM
import EVM.ABI
import EVM.Effects (App, runApp)
import EVM.Fetch qualified as Fetch
import EVM.Solidity
import EVM.Stepper qualified as Stepper
import EVM.Transaction qualified
import EVM.Types
import EVM.UnitTest
import Test.Tasty.Bench
import Control.Monad.ST
import EVM.FeeSchedule (feeSchedule)

-- benchmark hevm using tasty-bench

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
