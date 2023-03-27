{-# Language GADTs #-}
{-# Language DataKinds #-}

module Main where

import Control.Lens
import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import Control.Monad.State.Strict (execStateT)
import Data.Functor
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Vector as V

import EVM
import EVM.ABI
import EVM.SMT
import EVM.Solvers
import EVM.Fetch
import EVM.SymExec
import EVM.TestUtils
import qualified EVM.Stepper as Stepper
import qualified EVM.Fetch as Fetch
import EVM.Types hiding (BlockNumber)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "rpc"
  [ testGroup "Block Parsing Tests"
    [ testCase "pre-merge-block" $ do
        let block' = BlockNumber 15537392
        (cb, numb, basefee, prevRan) <- fetchBlockFrom block' testRpc >>= \case
                      Nothing -> error "Could not fetch block"
                      Just EVM.Block{..} -> pure ( coinbase
                                                 , number
                                                 , baseFee
                                                 , prevRandao
                                                 )

        assertEqual "coinbase" (Addr 0xea674fdde714fd979de3edf0f56aa9716b898ec8) cb
        assertEqual "number" (BlockNumber numb) block'
        assertEqual "basefee" 38572377838 basefee
        assertEqual "prevRan" 11049842297455506 prevRan
    , testCase "post-merge-block" $ do
        let block' = BlockNumber 16184420
        (cb, numb, basefee, prevRan) <- fetchBlockFrom block' testRpc >>= \case
                      Nothing -> error "Could not fetch block"
                      Just EVM.Block{..} -> pure ( coinbase
                                                 , number
                                                 , baseFee
                                                 , prevRandao
                                                 )

        assertEqual "coinbase" (Addr 0x690b9a9e9aa1c9db991c7721a92d351db4fac990) cb
        assertEqual "number" (BlockNumber numb) block'
        assertEqual "basefee" 22163046690 basefee
        assertEqual "prevRan" 0x2267531ab030ed32fd5f2ef51f81427332d0becbd74fe7f4cd5684ddf4b287e0 prevRan
    ]
  , testGroup "execution with remote state"
    -- execute against remote state from a ds-test harness
    [ testCase "dapp-test" $ do
        let testFile = "test/contracts/pass/rpc.sol"
        runDappTestCustom testFile ".*" Nothing False testRpcInfo >>= assertEqual "test result" True

    -- concretely exec "transfer" on WETH9 using remote rpc
    -- https://etherscan.io/token/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code
    , testCase "weth-conc" $ do
        let
          blockNum = 16198552
          wad = 0x999999999999999999
          calldata' = ConcreteBuf $ abiMethod "transfer(address,uint256)" (AbiTuple (V.fromList [AbiAddress (Addr 0xdead), AbiUInt 256 wad]))
        vm <- weth9VM blockNum (calldata', [])
        postVm <- withSolvers Z3 1 Nothing $ \solvers ->
          execStateT (Stepper.interpret (Fetch.oracle solvers (Just (BlockNumber blockNum, testRpc))) . void $ Stepper.execFully) vm
        let
          postStore = case view (env . storage) postVm of
            ConcreteStore s -> s
            _ -> error "ConcreteStore expected"
          wethStore = fromJust $ Map.lookup 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2 postStore
          receiverBal = fromJust $ Map.lookup (keccak' (word256Bytes 0xdead <> word256Bytes 0x3)) wethStore
          msg = case view result postVm of
            Just (VMSuccess m) -> m
            _ -> error "VMSuccess expected"
        assertEqual "should succeed" msg (ConcreteBuf $ word256Bytes 0x1)
        assertEqual "should revert" receiverBal (W256 $ 2595433725034301 + wad)

    -- symbolically exec "transfer" on WETH9 using remote rpc
    -- https://etherscan.io/token/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code
    , testCase "weth-sym" $ do
        let
          blockNum = 16198552
          calldata' = symCalldata "transfer(address,uint256)" [AbiAddressType, AbiUIntType 256] ["0xdead"] (AbstractBuf "txdata")
          postc _ (EVM.Types.Revert _ _) = PBool False
          postc _ _ = PBool True
        vm <- weth9VM blockNum calldata'
        (_, [Cex (_, model)]) <- withSolvers Z3 1 Nothing $ \solvers ->
          verify solvers (rpcVeriOpts (BlockNumber blockNum, testRpc)) vm (Just postc)
        assertBool "model should exceed caller balance" (getVar model "arg2" >= 695836005599316055372648)
    ]
  ]

-- call into WETH9 from 0xf04a... (a large holder)
weth9VM :: W256 -> (Expr Buf, [Prop]) -> IO (EVM.VM)
weth9VM blockNum calldata' = do
  let
    caller' = Lit 0xf04a5cc80b1e94c69b48f5ee68a08cd2f09a7c3e
    weth9 = Addr 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2
    callvalue' = Lit 0
  vmFromRpc blockNum calldata' callvalue' caller' weth9

vmFromRpc :: W256 -> (Expr Buf, [Prop]) -> Expr EWord -> Expr EWord -> Addr -> IO (EVM.VM)
vmFromRpc blockNum calldata' callvalue' caller' address' = do
  ctrct <- fetchContractFrom (BlockNumber blockNum) testRpc address' >>= \case
        Nothing -> error $ "contract not found: " <> show address'
        Just contract' -> return contract'

  blk <- fetchBlockFrom (BlockNumber blockNum) testRpc >>= \case
    Nothing -> error "could not fetch block"
    Just b -> pure b

  pure $ EVM.makeVm $ EVM.VMOpts
    { EVM.vmoptContract      = ctrct
    , EVM.vmoptCalldata      = calldata'
    , EVM.vmoptValue         = callvalue'
    , EVM.vmoptAddress       = address'
    , EVM.vmoptCaller        = caller'
    , EVM.vmoptOrigin        = 0xacab
    , EVM.vmoptGas           = 0xffffffffffffffff
    , EVM.vmoptGaslimit      = 0xffffffffffffffff
    , EVM.vmoptBaseFee       = blk.baseFee
    , EVM.vmoptPriorityFee   = 0
    , EVM.vmoptCoinbase      = blk.coinbase
    , EVM.vmoptNumber        = blk.number
    , EVM.vmoptTimestamp     = blk.timestamp
    , EVM.vmoptBlockGaslimit = blk.gaslimit
    , EVM.vmoptGasprice      = 0
    , EVM.vmoptMaxCodeSize   = blk.maxCodeSize
    , EVM.vmoptPrevRandao    = blk.prevRandao
    , EVM.vmoptSchedule      = blk.schedule
    , EVM.vmoptChainId       = 1
    , EVM.vmoptCreate        = False
    , EVM.vmoptStorageBase   = EVM.Concrete
    , EVM.vmoptTxAccessList  = mempty
    , EVM.vmoptAllowFFI      = False
    }

testRpc :: Text
testRpc = "https://eth-mainnet.alchemyapi.io/v2/vpeKFsEF6PHifHzdtcwXSDbhV3ym5Ro4"

testRpcInfo :: RpcInfo
testRpcInfo = Just (BlockNumber 16198552, testRpc)
