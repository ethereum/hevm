{-# Language DataKinds #-}

module EVM.Exec where

import EVM
import EVM.Concrete (createAddress)
import EVM.Types
import EVM.Expr (litAddr)

import qualified EVM.FeeSchedule as FeeSchedule

import Optics.Core
import Control.Monad.Trans.State.Strict (get, StateT(..))
import Control.Monad.State.Strict (execState, runState)
import Data.ByteString (ByteString)
import Data.Maybe (isNothing)
import qualified EVM.Fetch as Fetch
import Data.Text



ethrunAddress :: Addr
ethrunAddress = Addr 0x00a329c0648769a73afac7f9381e08fb43dbea72

vmForEthrunCreation :: ByteString -> VM
vmForEthrunCreation creationCode =
  (makeVm $ VMOpts
    { contract = initialContract (InitCode creationCode mempty)
    , calldata = mempty
    , value = (Lit 0)
    , initialStorage = EmptyStore
    , address = createAddress ethrunAddress 1
    , caller = litAddr ethrunAddress
    , origin = ethrunAddress
    , coinbase = 0
    , number = 0
    , timestamp = (Lit 0)
    , blockGaslimit = 0
    , gasprice = 0
    , prevRandao = 42069
    , gas = 0xffffffffffffffff
    , gaslimit = 0xffffffffffffffff
    , baseFee = 0
    , priorityFee = 0
    , maxCodeSize = 0xffffffff
    , schedule = FeeSchedule.berlin
    , chainId = 1
    , create = False
    , txAccessList = mempty
    , allowFFI = False
    }) & set (#env % #contracts % at ethrunAddress)
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode ""))))

exec :: EVM VMResult
exec = do
  vm <- get
  case vm.result of
    Nothing -> exec1 >> exec
    Just r -> pure r

run :: EVM VM
run = do
  vm <- get
  case vm.result of
    Nothing -> exec1 >> run
    Just _ -> pure vm

execWhile :: (VM -> Bool) -> EVM Int
execWhile p = go 0
  where
    go i = do
      vm <- get
      if p vm && isNothing vm.result
        then do
          go $! (i + 1)
      else
        pure i

-- essentially a combination of 'interpret _ _ runFully', bypassing all the monadic interpreter shenanegans
runWithHandler :: Fetch.Fetcher -> VM -> IO VM
runWithHandler fetcher vm =
  let (r, vm') = runState exec vm
  in case r of
    HandleEffect (Query (PleaseAskSMT (Lit c) _ continue)) -> do
      let vm'' = execState (continue (Case (c > 0))) vm'
      runWithHandler fetcher vm''
    HandleEffect (Query q) -> do
      m <- fetcher q
      let vm'' = execState m vm'
      runWithHandler fetcher vm''
    HandleEffect (Choose _) -> error "cannot make choices with this interpreter"
    _ -> pure vm'

-- essentially a combination of 'interpret _ _ execFully', bypassing all the monadic interpreter shenanegans
execWithHandler :: Fetch.Fetcher -> VM -> IO (Either EvmError (Expr Buf))
execWithHandler fetcher vm = fst <$> runStateT (execWithHandlerT fetcher) vm

runWithHandlerT:: Fetch.Fetcher -> StateT VM IO ()
runWithHandlerT f = StateT $ \v -> do s <- runWithHandler f v
                                      pure ((), s)

execWithHandlerT :: Fetch.Fetcher -> StateT VM IO (Either EvmError (Expr Buf))
execWithHandlerT f =
  StateT $ \v -> do s <- runWithHandler f v
                    case s.result of
                      Just (VMFailure x) -> pure (Left x, s)
                      Just (VMSuccess x) -> pure (Right x, s)
                      Just (Unfinished x) ->
                        error $ "Internal Error: partial execution encountered during concrete execution: " <> show x
                      _ -> error $ "Internal error: the impossible has occurred"



enter :: Text -> EVM ()
enter = pushTrace . EntryTrace
