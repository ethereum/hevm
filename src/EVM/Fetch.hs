{-# Language GADTs #-}
{-# Language DataKinds #-}

module EVM.Fetch where

import Prelude hiding (Word)

import EVM.ABI
import EVM.SMT
import EVM.Solvers
import EVM.Types
import EVM.Format (hexText)
import EVM        (emptyContract, initialContract)
import qualified EVM.FeeSchedule as FeeSchedule

import Optics.Core

import Control.Monad.Trans.Maybe
import Data.Aeson hiding (Error)
import Data.Aeson.Optics
import qualified Data.ByteString as BS
import Data.Text (Text, unpack, pack)
import Data.Maybe (fromMaybe)
import Data.List (foldl')
import qualified Data.Text as T

import qualified Data.Vector as RegularVector
import Network.Wreq
import Network.Wreq.Session (Session)
import System.Process

import qualified Network.Wreq.Session as Session
import Numeric.Natural (Natural)

-- | Abstract representation of an RPC fetch request
data RpcQuery a where
  QueryCode    :: Addr         -> RpcQuery BS.ByteString
  QueryBlock   ::                 RpcQuery Block
  QueryBalance :: Addr         -> RpcQuery W256
  QueryNonce   :: Addr         -> RpcQuery W64
  QuerySlot    :: Addr -> W256 -> RpcQuery W256
  QueryChainId ::                 RpcQuery W256

data BlockNumber = Latest | BlockNumber W256
  deriving (Show, Eq)

deriving instance Show (RpcQuery a)

type RpcInfo = Maybe (BlockNumber, Text)

rpc :: String -> [Value] -> Value
rpc method args = object
  [ "jsonrpc" .= ("2.0" :: String)
  , "id"      .= Number 1
  , "method"  .= method
  , "params"  .= args
  ]

class ToRPC a where
  toRPC :: a -> Value

instance ToRPC Addr where
  toRPC = String . pack . show

instance ToRPC W256 where
  toRPC = String . pack . show

instance ToRPC Bool where
  toRPC = Bool

instance ToRPC BlockNumber where
  toRPC Latest          = String "latest"
  toRPC (EVM.Fetch.BlockNumber n) = String . pack $ show n

readText :: Read a => Text -> a
readText = read . unpack

fetchQuery
  :: Show a
  => BlockNumber
  -> (Value -> IO (Maybe Value))
  -> RpcQuery a
  -> IO (Maybe a)
fetchQuery n f q = do
  x <- case q of
    QueryCode addr -> do
        m <- f (rpc "eth_getCode" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          hexText <$> t
    QueryNonce addr -> do
        m <- f (rpc "eth_getTransactionCount" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QueryBlock -> do
      m <- f (rpc "eth_getBlockByNumber" [toRPC n, toRPC False])
      return $ m >>= parseBlock
    QueryBalance addr -> do
        m <- f (rpc "eth_getBalance" [toRPC addr, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QuerySlot addr slot -> do
        m <- f (rpc "eth_getStorageAt" [toRPC addr, toRPC slot, toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
    QueryChainId -> do
        m <- f (rpc "eth_chainId" [toRPC n])
        pure $ do
          t <- preview _String <$> m
          readText <$> t
  return x


parseBlock :: (AsValue s, Show s) => s -> Maybe Block
parseBlock j = do
  coinbase   <- LitAddr . readText <$> j ^? key "miner" % _String
  timestamp  <- Lit . readText <$> j ^? key "timestamp" % _String
  number     <- readText <$> j ^? key "number" % _String
  gasLimit   <- readText <$> j ^? key "gasLimit" % _String
  let
   baseFee = readText <$> j ^? key "baseFeePerGas" % _String
   -- It seems unclear as to whether this field should still be called mixHash or renamed to prevRandao
   -- According to https://github.com/ethereum/EIPs/blob/master/EIPS/eip-4399.md it should be renamed
   -- but alchemy is still returning mixHash
   mixhash = readText <$> j ^? key "mixHash" % _String
   prevRandao = readText <$> j ^? key "prevRandao" % _String
   difficulty = readText <$> j ^? key "difficulty" % _String
   prd = case (prevRandao, mixhash, difficulty) of
     (Just p, _, _) -> p
     (Nothing, Just mh, Just 0x0) -> mh
     (Nothing, Just _, Just d) -> d
     _ -> error "Internal Error: block contains both difficulty and prevRandao"
  -- default codesize, default gas limit, default feescedule
  return $ Block coinbase timestamp number prd gasLimit (fromMaybe 0 baseFee) 0xffffffff FeeSchedule.berlin

fetchWithSession :: Text -> Session -> Value -> IO (Maybe Value)
fetchWithSession url sess x = do
  r <- asValue =<< Session.post sess (unpack url) x
  return (r ^? (lensVL responseBody) % key "result")

fetchContractWithSession
  :: BlockNumber -> Text -> Addr -> Session -> IO (Maybe Contract)
fetchContractWithSession n url addr sess = runMaybeT $ do
  let
    fetch :: Show a => RpcQuery a -> IO (Maybe a)
    fetch = fetchQuery n (fetchWithSession url sess)

  code    <- MaybeT $ fetch (QueryCode addr)
  nonce   <- MaybeT $ fetch (QueryNonce addr)
  balance <- MaybeT $ fetch (QueryBalance addr)

  pure $
    initialContract (RuntimeCode (ConcreteRuntimeCode code))
      & set #nonce    (Just nonce)
      & set #balance  (Lit balance)
      & set #external True

fetchSlotWithSession
  :: BlockNumber -> Text -> Session -> Addr -> W256 -> IO (Maybe W256)
fetchSlotWithSession n url sess addr slot =
  fetchQuery n (fetchWithSession url sess) (QuerySlot addr slot)

fetchBlockWithSession
  :: BlockNumber -> Text -> Session -> IO (Maybe Block)
fetchBlockWithSession n url sess =
  fetchQuery n (fetchWithSession url sess) QueryBlock

fetchBlockFrom :: BlockNumber -> Text -> IO (Maybe Block)
fetchBlockFrom n url = do
  sess <- Session.newAPISession
  fetchBlockWithSession n url sess

fetchContractFrom :: BlockNumber -> Text -> Addr -> IO (Maybe Contract)
fetchContractFrom n url addr = do
  sess <- Session.newAPISession
  fetchContractWithSession n url addr sess

fetchSlotFrom :: BlockNumber -> Text -> Addr -> W256 -> IO (Maybe W256)
fetchSlotFrom n url addr slot = do
  sess <- Session.newAPISession
  fetchSlotWithSession n url sess addr slot

fetchChainIdFrom :: Text -> IO (Maybe W256)
fetchChainIdFrom url = do
  sess <- Session.newAPISession
  fetchQuery Latest (fetchWithSession url sess) QueryChainId

http :: Natural -> Maybe Natural -> BlockNumber -> Text -> Fetcher
http smtjobs smttimeout n url q =
  withSolvers Z3 smtjobs smttimeout $ \s ->
    oracle s (Just (n, url)) q

zero :: Natural -> Maybe Natural -> Fetcher
zero smtjobs smttimeout q =
  withSolvers Z3 smtjobs smttimeout $ \s ->
    oracle s Nothing q

-- smtsolving + (http or zero)
oracle :: SolverGroup -> RpcInfo -> Fetcher
oracle solvers info q = do
  case q of
    PleaseDoFFI vals continue -> case vals of
       cmd : args -> do
          (_, stdout', _) <- readProcessWithExitCode cmd args ""
          pure . continue . encodeAbiValue $
            AbiTuple (RegularVector.fromList [ AbiBytesDynamic . hexText . pack $ stdout'])
       _ -> error (show vals)

    PleaseAskSMT branchcondition pathconditions continue -> do
         let pathconds = foldl' PAnd (PBool True) pathconditions
         -- Is is possible to satisfy the condition?
         continue <$> checkBranch solvers (branchcondition ./= (Lit 0)) pathconds

    PleaseFetchContract addr continue -> do
      contract <- case info of
        Nothing -> return $ Just emptyContract
        Just (n, url) -> fetchContractFrom n url addr
      case contract of
        Just x -> return $ continue x
        Nothing -> error ("oracle error: " ++ show q)

    PleaseFetchSlot addr slot continue ->
      case info of
        Nothing -> return (continue 0)
        Just (n, url) ->
         fetchSlotFrom n url addr (fromIntegral slot) >>= \case
           Just x  -> return (continue x)
           Nothing ->
             error ("oracle error: " ++ show q)

type Fetcher = Query -> IO (EVM ())

-- | Checks which branches are satisfiable, checking the pathconditions for consistency
-- if the third argument is true.
-- When in debug mode, we do not want to be able to navigate to dead paths,
-- but for normal execution paths with inconsistent pathconditions
-- will be pruned anyway.
checkBranch :: SolverGroup -> Prop -> Prop -> IO BranchCondition
checkBranch solvers branchcondition pathconditions = do
  checkSat solvers (assertProps [(branchcondition .&& pathconditions)]) >>= \case
     -- the condition is unsatisfiable
     Unsat -> -- if pathconditions are consistent then the condition must be false
            return $ Case False
     -- Sat means its possible for condition to hold
     Sat _ -> -- is its negation also possible?
            checkSat solvers (assertProps [(pathconditions .&& (PNeg branchcondition))]) >>= \case
               -- No. The condition must hold
               Unsat -> return $ Case True
               -- Yes. Both branches possible
               Sat _ -> return EVM.Types.Unknown
               -- Explore both branches in case of timeout
               EVM.Solvers.Unknown -> return EVM.Types.Unknown
               Error e -> error $ "Internal Error: SMT Solver returned with an error: " <> T.unpack e
     -- If the query times out, we simply explore both paths
     EVM.Solvers.Unknown -> return EVM.Types.Unknown
     Error e -> error $ "Internal Error: SMT Solver returned with an error: " <> T.unpack e
