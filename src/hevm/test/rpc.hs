{-# Language GADTs #-}
{-# Language DataKinds #-}

module Main where

import Data.Text (Text)

import Test.Tasty
import Test.Tasty.HUnit

import qualified EVM.Fetch as Fetch
import qualified EVM
import EVM.Types

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "rpc"
  [ testGroup "Block Parsing Tests"
    [ testCase "pre-merge-block" $ do
        let block' = Fetch.BlockNumber 15537392
        (cb, numb, basefee, prevRan) <- Fetch.fetchBlockFrom block' testRpc >>= \case
                      Nothing -> error "Could not fetch block"
                      Just EVM.Block{..} -> return (_coinbase
                                                   , _number
                                                   , _baseFee
                                                   , _prevRandao
                                                   )

        assertEqual "coinbase" (Addr 0xea674fdde714fd979de3edf0f56aa9716b898ec8) cb
        assertEqual "number" (Fetch.BlockNumber numb) block'
        assertEqual "basefee" 38572377838 basefee
        assertEqual "prevRan" 11049842297455506 prevRan
    , testCase "post-merge-block" $ do
        let block' = Fetch.BlockNumber 16184420
        (cb, numb, basefee, prevRan) <- Fetch.fetchBlockFrom block' testRpc >>= \case
                      Nothing -> error "Could not fetch block"
                      Just EVM.Block{..} -> return (_coinbase
                                                   , _number
                                                   , _baseFee
                                                   , _prevRandao
                                                   )

        assertEqual "coinbase" (Addr 0x690b9a9e9aa1c9db991c7721a92d351db4fac990) cb
        assertEqual "number" (Fetch.BlockNumber numb) block'
        assertEqual "basefee" 22163046690 basefee
        assertEqual "prevRan" 0x2267531ab030ed32fd5f2ef51f81427332d0becbd74fe7f4cd5684ddf4b287e0 prevRan
    ]
  ]

testRpc :: Text
testRpc = "https://eth-mainnet.alchemyapi.io/v2/vpeKFsEF6PHifHzdtcwXSDbhV3ym5Ro4"
