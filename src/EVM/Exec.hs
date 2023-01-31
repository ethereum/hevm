module EVM.Exec where

import EVM
import EVM.Concrete (createAddress)
import EVM.Types
import EVM.Expr (litAddr)

import qualified EVM.FeeSchedule as FeeSchedule

import Control.Lens
import Control.Monad.Trans.State.Strict (get, State)
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)


ethrunAddress :: Addr
ethrunAddress = Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

vmForEthrunCreation :: ByteString -> VM
vmForEthrunCreation creationCode =
  (makeVm $ VMOpts
    { vmoptContract = initialContract (InitCode creationCode mempty)
    , vmoptCalldata = mempty
    , vmoptValue = (Lit 0)
    , vmoptStorageBase = Concrete
    , vmoptAddress = createAddress ethrunAddress 1
    , vmoptCaller = litAddr ethrunAddress
    , vmoptOrigin = ethrunAddress
    , vmoptCoinbase = 0
    , vmoptNumber = 0
    , vmoptTimestamp = (Lit 0)
    , vmoptBlockGaslimit = 0
    , vmoptGasprice = 0
    , vmoptPrevRandao = 42069
    , vmoptGas = 0xffffffffffffffff
    , vmoptGaslimit = 0xffffffffffffffff
    , vmoptBaseFee = 0
    , vmoptPriorityFee = 0
    , vmoptMaxCodeSize = 0xffffffff
    , vmoptSchedule = FeeSchedule.berlin
    , vmoptChainId = 1
    , vmoptCreate = False
    , vmoptTxAccessList = mempty
    , vmoptAllowFFI = False
    }) & set (env . contracts . at ethrunAddress)
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode ""))))

exec :: State VM VMResult
exec = do
  vm <- get
  case vm._result of
    Nothing -> exec1 >> exec
    Just r -> pure r

run :: State VM VM
run = do
  vm <- get
  case vm._result of
    Nothing -> exec1 >> run
    Just _ -> pure vm

execWhile :: (VM -> Bool) -> State VM Int
execWhile p = go 0
  where
    go i = do
      vm <- get
      if p vm && isNothing vm._result
        then do
          go $! (i + 1)
      else
        pure i
