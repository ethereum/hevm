{-# Language GADTs #-}
{-# Language DataKinds #-}

module Main where

import Control.Lens
import Test.Tasty
import Test.Tasty.HUnit
import Data.Text (Text)
import qualified Data.Text.IO as T

import EVM
import EVM.ABI
import EVM.SMT
import EVM.Format
import EVM.Fetch
import EVM.SymExec
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
                      Just EVM.Block{..} -> return (_coinbase
                                                   , _number
                                                   , _baseFee
                                                   , _prevRandao
                                                   )

        assertEqual "coinbase" (Addr 0xea674fdde714fd979de3edf0f56aa9716b898ec8) cb
        assertEqual "number" (BlockNumber numb) block'
        assertEqual "basefee" 38572377838 basefee
        assertEqual "prevRan" 11049842297455506 prevRan
    , testCase "post-merge-block" $ do
        let block' = BlockNumber 16184420
        (cb, numb, basefee, prevRan) <- fetchBlockFrom block' testRpc >>= \case
                      Nothing -> error "Could not fetch block"
                      Just EVM.Block{..} -> return (_coinbase
                                                   , _number
                                                   , _baseFee
                                                   , _prevRandao
                                                   )

        assertEqual "coinbase" (Addr 0x690b9a9e9aa1c9db991c7721a92d351db4fac990) cb
        assertEqual "number" (BlockNumber numb) block'
        assertEqual "basefee" 22163046690 basefee
        assertEqual "prevRan" 0x2267531ab030ed32fd5f2ef51f81427332d0becbd74fe7f4cd5684ddf4b287e0 prevRan
    ]
  , testGroup "execution with remote state"
    [ testCase "dapp-test" undefined
    , testCase "weth-conc" undefined
    , testCase "weth-sym-remote" $ do
        let
          -- call into WETH9 at block 16181378 from 0xf04a... (a large holder)
          blockNum = 16198552
          caller' = Lit 0xf04a5cc80b1e94c69b48f5ee68a08cd2f09a7c3e
          weth9 = Addr 0xC02aaA39b223FE8D0A0e5C4F27eAD9083C756Cc2
          calldata' = symCalldata "transfer(address,uint256)" [AbiAddressType, AbiUIntType 256] ["0xdead"] (AbstractBuf "txdata")
          callvalue' = Lit 0

          -- we are looking for a revert if the `wad` is greater than the callers balance
          postc _ (EVM.Types.Revert _ _) = PBool False
          postc _ _ = PBool True
        vm <- vmFromRpc blockNum calldata' callvalue' caller' weth9
        (_, [Cex (_, model)]) <- withSolvers Z3 1 Nothing $ \solvers ->
          verify solvers (rpcVeriOpts (BlockNumber blockNum, testRpc)) vm (Just postc)
        assertBool "model should exceed caller balance" (getVar model "arg2" >= 695836005599316055372648)
    ]
  ]

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
    , EVM.vmoptBaseFee       = view baseFee blk
    , EVM.vmoptPriorityFee   = 0
    , EVM.vmoptCoinbase      = view coinbase blk
    , EVM.vmoptNumber        = view number blk
    , EVM.vmoptTimestamp     = view timestamp blk
    , EVM.vmoptBlockGaslimit = view gaslimit blk
    , EVM.vmoptGasprice      = 0
    , EVM.vmoptMaxCodeSize   = view maxCodeSize blk
    , EVM.vmoptPrevRandao    = view prevRandao blk
    , EVM.vmoptSchedule      = view schedule blk
    , EVM.vmoptChainId       = 1
    , EVM.vmoptCreate        = False
    , EVM.vmoptStorageBase   = EVM.Concrete
    , EVM.vmoptTxAccessList  = mempty
    , EVM.vmoptAllowFFI      = False
    }

testRpc :: Text
testRpc = "https://eth-mainnet.alchemyapi.io/v2/vpeKFsEF6PHifHzdtcwXSDbhV3ym5Ro4"
