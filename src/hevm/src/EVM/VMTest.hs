{-# Language CPP #-}
{-# LANGUAGE TupleSections #-}

module EVM.VMTest
  ( Case
  , BlockchainCase

  , parseBCSuite

  , initTx
  , setupTx
  , vmForCase
  , checkExpectation
  ) where

import Prelude hiding (Word)

import qualified EVM
import EVM (contractcode, storage, origStorage, balance, nonce, initialContract, StorageBase(..))
import EVM.Expr (litCode, litAddr)
import qualified EVM.Concrete as EVM
import qualified EVM.FeeSchedule

import EVM.Transaction
import EVM.Types

import Control.Arrow ((***), (&&&))
import Control.Lens
import Control.Monad

import GHC.Stack

import Data.Aeson ((.:), (.:?), FromJSON (..))
import Data.Map (Map)
import Data.Maybe (fromMaybe, isNothing)
import Data.Witherable (Filterable, catMaybes)

import qualified Data.Map          as Map
import qualified Data.Aeson        as JSON
import qualified Data.Aeson.Types  as JSON
import qualified Data.ByteString.Lazy  as Lazy
import qualified Data.Vector as V

type Storage = Map W256 W256

data Which = Pre | Post

data Block = Block
  { blockCoinbase    :: Addr
  , blockDifficulty  :: W256
  , blockGasLimit    :: W256
  , blockBaseFee     :: W256
  , blockNumber      :: W256
  , blockTimestamp   :: W256
  , blockTxs         :: [Transaction]
  } deriving Show

data Case = Case
  { testVmOpts      :: EVM.VMOpts
  , checkContracts  :: Map Addr (EVM.Contract, Storage)
  , testExpectation :: Map Addr (EVM.Contract, Storage)
  } deriving Show

data BlockchainCase = BlockchainCase
  { blockchainBlocks  :: [Block]
  , blockchainPre     :: Map Addr (EVM.Contract, Storage)
  , blockchainPost    :: Map Addr (EVM.Contract, Storage)
  , blockchainNetwork :: String
  } deriving Show

splitEithers :: (Filterable f) => f (Either a b) -> (f a, f b)
splitEithers =
  (catMaybes *** catMaybes)
  . (fmap fst &&& fmap snd)
  . (fmap (preview _Left &&& preview _Right))

checkStateFail :: Bool -> Case -> EVM.VM -> (Bool, Bool, Bool, Bool, Bool) -> IO Bool
checkStateFail diff x vm (okState, okMoney, okNonce, okData, okCode) = do
  let
    printContracts :: Map Addr (EVM.Contract, Storage) -> IO ()
    printContracts cs = putStrLn $ Map.foldrWithKey (\k (c, s) acc ->
      acc ++ show k ++ " : "
                   ++ (show . toInteger  $ (view nonce c)) ++ " "
                   ++ (show . toInteger  $ (view balance c)) ++ " "
                   ++ (printStorage s)
        ++ "\n") "" cs

    reason = map fst (filter (not . snd)
        [ ("bad-state",       okMoney || okNonce || okData  || okCode || okState)
        , ("bad-balance", not okMoney || okNonce || okData  || okCode || okState)
        , ("bad-nonce",   not okNonce || okMoney || okData  || okCode || okState)
        , ("bad-storage", not okData  || okMoney || okNonce || okCode || okState)
        , ("bad-code",    not okCode  || okMoney || okNonce || okData || okState)
        ])
    check = checkContracts x
    expected = testExpectation x
    actual = Map.map (,mempty) $ view (EVM.env . EVM.contracts) vm -- . to (fmap (clearZeroStorage.clearOrigStorage))) vm
    printStorage = show -- TODO: fixme

  putStr (unwords reason)
  when (diff && (not okState)) $ do
    putStrLn "\nPre balance/state: "
    printContracts check
    putStrLn "\nExpected balance/state: "
    printContracts expected
    putStrLn "\nActual balance/state: "
    printContracts actual
  return okState

checkExpectation :: HasCallStack => Bool -> Case -> EVM.VM -> IO Bool
checkExpectation diff x vm = do
  let expectation = testExpectation x
      (okState, b2, b3, b4, b5) = checkExpectedContracts vm expectation
  unless okState $ void $ checkStateFail
    diff x vm (okState, b2, b3, b4, b5)
  return okState

-- quotient account state by nullness
(~=) :: Map Addr (EVM.Contract, Storage) -> Map Addr (EVM.Contract, Storage) -> Bool
(~=) cs1 cs2 =
    let nullAccount = EVM.initialContract (EVM.RuntimeCode mempty)
        padNewAccounts cs ks = Map.union cs $ Map.fromList [(k, (nullAccount, mempty)) | k <- ks]
        padded_cs1 = padNewAccounts cs1 (Map.keys cs2)
        padded_cs2 = padNewAccounts cs2 (Map.keys cs1)
    in and $ zipWith (===) (Map.elems padded_cs1) (Map.elems padded_cs2)

(===) :: (EVM.Contract, Storage) -> (EVM.Contract, Storage) -> Bool
(c1, s1) === (c2, s2) =
  codeEqual && storageEqual && (c1 ^. balance == c2 ^. balance) && (c1 ^. nonce ==  c2 ^. nonce)
  where
    storageEqual = s1 == s2
    codeEqual = case (c1 ^. contractcode, c2 ^. contractcode) of
      (EVM.RuntimeCode a', EVM.RuntimeCode b') -> a' == b'
      _ -> error "unexpected code"

checkExpectedContracts :: HasCallStack => EVM.VM -> Map Addr (EVM.Contract, Storage) -> (Bool, Bool, Bool, Bool, Bool)
checkExpectedContracts vm expected =
  let cs = zipWithStorages $ vm ^. EVM.env . EVM.contracts -- . to (fmap (clearZeroStorage.clearOrigStorage))
      expectedCs = clearStorage <$> expected
  in ( (expectedCs ~= cs)
     , (clearBalance <$> expectedCs) ~= (clearBalance <$> cs)
     , (clearNonce   <$> expectedCs) ~= (clearNonce   <$> cs)
     , (clearStorage <$> expectedCs) ~= (clearStorage <$> cs)
     , (clearCode    <$> expectedCs) ~= (clearCode    <$> cs)
     )
  where
  zipWithStorages = Map.mapWithKey (\addr c -> (c, lookupStorage addr))
  lookupStorage addr =
    case vm ^. EVM.env . EVM.storage of
      ConcreteStore s -> mempty -- clearZeroStorage $ fromMaybe mempty $ Map.lookup (num addr) s
      EmptyStore -> mempty
      AbstractStore -> mempty -- error "AbstractStore, should this be handled?"
      SStore {} -> mempty -- error "SStore, should this be handled?"

{-
clearOrigStorage :: EVM.Contract -> EVM.Contract
clearOrigStorage = undefined
-}

-- TODO: why is this needed?
clearZeroStorage :: Storage -> Storage
clearZeroStorage = Map.filter (/= 0)

clearStorage :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearStorage (c, _) = (c, mempty)

clearBalance :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearBalance (c, s) = (set balance 0 c, s)

clearNonce :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearNonce (c, s) = (set nonce 0 c, s)

clearCode :: (EVM.Contract, Storage) -> (EVM.Contract, Storage)
clearCode (c, s) = (set contractcode (EVM.RuntimeCode mempty) c, s)



newtype ContractWithStorage = ContractWithStorage { unContractWithStorage :: (EVM.Contract, Storage) }

instance FromJSON ContractWithStorage where
  parseJSON (JSON.Object v) = do
    code <- (EVM.RuntimeCode . V.fromList . litCode <$> (hexText <$> v .: "code"))
    storage' <- v .: "storage"
    balance' <- v .: "balance"
    nonce'   <- v .: "nonce"
    let c = EVM.initialContract code
              & balance .~ balance'
              & nonce   .~ nonce'
    return $ ContractWithStorage (c, storage')

  parseJSON invalid =
    JSON.typeMismatch "Contract" invalid

instance FromJSON BlockchainCase where
  parseJSON (JSON.Object v) = BlockchainCase
    <$> v .: "blocks"
    <*> parseContracts Pre v
    <*> parseContracts Post v
    <*> v .: "network"
  parseJSON invalid =
    JSON.typeMismatch "GeneralState test case" invalid

instance FromJSON Block where
  parseJSON (JSON.Object v) = do
    v'         <- v .: "blockHeader"
    txs        <- v .: "transactions"
    coinbase   <- addrField v' "coinbase"
    difficulty <- wordField v' "difficulty"
    gasLimit   <- wordField v' "gasLimit"
    number     <- wordField v' "number"
    baseFee    <- fmap read <$> v' .:? "baseFeePerGas"
    timestamp  <- wordField v' "timestamp"
    return $ Block coinbase difficulty gasLimit (fromMaybe 0 baseFee) number timestamp txs
  parseJSON invalid =
    JSON.typeMismatch "Block" invalid

parseContracts ::
  Which -> JSON.Object -> JSON.Parser (Map Addr (EVM.Contract, Storage))
parseContracts w v =
  (Map.map unContractWithStorage) <$> (v .: which >>= parseJSON)
  where which = case w of
          Pre  -> "pre"
          Post -> "postState"

parseBCSuite ::
  Lazy.ByteString -> Either String (Map String Case)
parseBCSuite x = case (JSON.eitherDecode' x) :: Either String (Map String BlockchainCase) of
  Left e        -> Left e
  Right bcCases -> let allCases = fromBlockchainCase <$> bcCases
                       keepError (Left e) = errorFatal e
                       keepError _        = True
                       filteredCases = Map.filter keepError allCases
                       (erroredCases, parsedCases) = splitEithers filteredCases
    in if Map.size erroredCases > 0
    then Left ("errored case: " ++ (show erroredCases))
    else if Map.size parsedCases == 0
    then Left "No cases to check."
    else Right parsedCases


data BlockchainError
  = TooManyBlocks
  | TooManyTxs
  | NoTxs
  | SignatureUnverified
  | InvalidTx
  | OldNetwork
  | FailedCreate
  deriving Show

errorFatal :: BlockchainError -> Bool
errorFatal TooManyBlocks = True
errorFatal TooManyTxs = True
errorFatal SignatureUnverified = True
errorFatal InvalidTx = True
errorFatal _ = False

fromBlockchainCase :: BlockchainCase -> Either BlockchainError Case
fromBlockchainCase (BlockchainCase blocks preState postState network) =
  case (blocks, network) of
    ([block], "London") -> case blockTxs block of
      [tx] -> fromBlockchainCase' block tx preState postState
      []        -> Left NoTxs
      _         -> Left TooManyTxs
    ([_], _) -> Left OldNetwork
    (_, _)   -> Left TooManyBlocks

fromBlockchainCase' :: Block -> Transaction
                       -> Map Addr (EVM.Contract, Storage) -> Map Addr (EVM.Contract, Storage)
                       -> Either BlockchainError Case
fromBlockchainCase' block tx preState postState =
  let isCreate = isNothing (txToAddr tx) in
  case (sender 1 tx, checkTx tx block preState) of
      (Nothing, _) -> Left SignatureUnverified
      (_, Nothing) -> Left (if isCreate then FailedCreate else InvalidTx)
      (Just origin, Just checkState) -> Right $ Case
        (EVM.VMOpts
         { vmoptContract      = EVM.initialContract theCode
         , vmoptCalldata      = cd
         , vmoptValue         = Lit (txValue tx)
         , vmoptAddress       = toAddr
         , vmoptCaller        = litAddr origin
         , vmoptStorageBase   = Concrete
         , vmoptOrigin        = origin
         , vmoptGas           = txGasLimit tx - fromIntegral (txGasCost feeSchedule tx)
         , vmoptBaseFee       = blockBaseFee block
         , vmoptPriorityFee   = priorityFee tx (blockBaseFee block)
         , vmoptGaslimit      = txGasLimit tx
         , vmoptNumber        = blockNumber block
         , vmoptTimestamp     = Lit $ blockTimestamp block
         , vmoptCoinbase      = blockCoinbase block
         , vmoptDifficulty    = blockDifficulty block
         , vmoptMaxCodeSize   = 24576
         , vmoptBlockGaslimit = blockGasLimit block
         , vmoptGasprice      = effectiveGasPrice
         , vmoptSchedule      = feeSchedule
         , vmoptChainId       = 1
         , vmoptCreate        = isCreate
         , vmoptTxAccessList  = txAccessMap tx
         , vmoptAllowFFI      = False
         })
        checkState
        postState
          where
            toAddr = fromMaybe (EVM.createAddress origin senderNonce) (txToAddr tx)
            senderNonce = view (accountAt origin . nonce) (Map.map fst preState)
            feeSchedule = EVM.FeeSchedule.berlin
            toCode = Map.lookup toAddr preState
            theCode = if isCreate
                      then EVM.InitCode (txData tx) mempty
                      else maybe (EVM.RuntimeCode mempty) (view contractcode) (fst <$> toCode)
            effectiveGasPrice = effectiveprice tx (blockBaseFee block)
            cd = if isCreate
                 then mempty
                 else ConcreteBuf $ txData tx

effectiveprice :: Transaction -> W256 -> W256
effectiveprice tx baseFee = priorityFee tx baseFee + baseFee

priorityFee :: Transaction -> W256 -> W256
priorityFee tx baseFee = let
    (txPrioMax, txMaxFee) = case txType tx of
               EIP1559Transaction ->
                 let Just maxPrio = txMaxPriorityFeeGas tx
                     Just maxFee = txMaxFeePerGas tx
                 in (maxPrio, maxFee)
               _ ->
                 let Just gasPrice = txGasPrice tx
                 in (gasPrice, gasPrice)
  in min txPrioMax (txMaxFee - baseFee)

maxBaseFee :: Transaction -> W256
maxBaseFee tx =
  case txType tx of
     EIP1559Transaction ->
       let Just maxFee = txMaxFeePerGas tx
       in maxFee
     _ ->
       let Just gasPrice = txGasPrice tx
       in gasPrice


validateTx :: Transaction -> Block -> Map Addr (EVM.Contract, Storage) -> Maybe ()
validateTx tx block cs = do
  let cs' = Map.map fst cs
  origin        <- sender 1 tx
  originBalance <- (view balance) <$> view (at origin) cs'
  originNonce   <- (view nonce)   <$> view (at origin) cs'
  let gasDeposit = (effectiveprice tx (blockBaseFee block)) * (txGasLimit tx)
  if gasDeposit + (txValue tx) <= originBalance
    && txNonce tx == originNonce && blockBaseFee block <= maxBaseFee tx
  then Just ()
  else Nothing

checkTx :: Transaction -> Block -> Map Addr (EVM.Contract, Storage) -> Maybe (Map Addr (EVM.Contract, Storage))
checkTx tx block prestate = do
  origin <- sender 1 tx
  validateTx tx block prestate
  let isCreate   = isNothing (txToAddr tx)
      senderNonce = view (accountAt origin . nonce) (Map.map fst prestate)
      toAddr      = fromMaybe (EVM.createAddress origin senderNonce) (txToAddr tx)
      prevCode    = view (accountAt toAddr . contractcode) (Map.map fst prestate)
      prevNonce   = view (accountAt toAddr . nonce) (Map.map fst prestate)
  if isCreate && ((case prevCode of {EVM.RuntimeCode b -> not (null b); _ -> True}) || (prevNonce /= 0))
  then mzero
  else
    return prestate

vmForCase :: Case -> EVM.VM
vmForCase x =
  let
    a = checkContracts x
    cs = Map.map fst a
    st = Map.mapKeys num $ Map.map snd a
    vm = EVM.makeVm (testVmOpts x)
      & set (EVM.env . EVM.contracts) cs
      & set (EVM.env . EVM.storage) (ConcreteStore st)
      & set (EVM.env . EVM.origStorage) st
  in
    initTx vm
