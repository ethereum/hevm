module EVM.Exec where

import EVM
import EVM.Concrete (createAddress)
import EVM.Types
import EVM.Expr (litAddr)

import qualified EVM.FeeSchedule as FeeSchedule

import Control.Lens
import Control.Monad.State.Class (MonadState)
import Control.Monad.State.Strict (runState)
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)

import qualified Control.Monad.State.Class as State

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
             (Just (initialContract (RuntimeCode mempty)))

exec :: MonadState VM m => m VMResult
exec =
  use EVM.result >>= \case
    Nothing -> State.state (runState exec1) >> exec
    Just x  -> return x

run :: MonadState VM m => m VM
run =
  use EVM.result >>= \case
    Nothing -> State.state (runState exec1) >> run
    Just _  -> State.get

execWhile :: MonadState VM m => (VM -> Bool) -> m Int
execWhile p = go 0
  where
    go i = do
      x <- State.get
      if p x && isNothing (view result x)
        then do
          State.state (runState exec1)
          go $! (i + 1)
      else
        return i
