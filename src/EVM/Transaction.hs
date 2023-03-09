module EVM.Transaction where

import Prelude hiding (Word)

import qualified EVM
import EVM (balance, initialContract)
import EVM.FeeSchedule
import EVM.RLP
import EVM.Types
import EVM.Expr (litAddr)
import Control.Lens
import EVM.Sign

import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Maybe (fromMaybe, isNothing, fromJust)
import GHC.Generics (Generic)

import Data.Aeson (FromJSON (..))
import qualified Data.Aeson        as JSON
import qualified Data.Aeson.Types  as JSON
import qualified Data.ByteString   as BS
import qualified Data.Map          as Map
import Data.Word (Word64)
import Numeric (showHex)

data AccessListEntry = AccessListEntry {
  accessAddress :: Addr,
  accessStorageKeys :: [W256]
} deriving (Show, Generic)

instance JSON.ToJSON AccessListEntry

data TxType = LegacyTransaction
            | AccessListTransaction
            | EIP1559Transaction
  deriving (Show, Eq, Generic)

instance JSON.ToJSON TxType where
  toJSON t = case t of
               EIP1559Transaction    -> "0x2" -- EIP1559
               LegacyTransaction     -> "0x1" -- EIP2718
               AccessListTransaction -> "0x1" -- EIP2930


data Transaction = Transaction {
    txData     :: ByteString,
    txGasLimit :: Word64,
    txGasPrice :: Maybe W256,
    txNonce    :: W256,
    txR        :: W256,
    txS        :: W256,
    txToAddr   :: Maybe Addr,
    txV        :: W256,
    txValue    :: W256,
    txType     :: TxType,
    txAccessList :: [AccessListEntry],
    txMaxPriorityFeeGas :: Maybe W256,
    txMaxFeePerGas :: Maybe W256,
    txChainId  :: W256
} deriving (Show, Generic)

instance JSON.ToJSON Transaction where
  toJSON t = JSON.object [ ("input",             (JSON.toJSON (ByteStringS t.txData)))
                         , ("gas",               (JSON.toJSON $ "0x" ++ showHex (toInteger $ t.txGasLimit) ""))
                         , ("gasPrice",          (JSON.toJSON $ show $ fromJust $ t.txGasPrice))
                         , ("v",                 (JSON.toJSON $ show $ (t.txV)-27))
                         , ("r",                 (JSON.toJSON $ show $ t.txR))
                         , ("s",                 (JSON.toJSON $ show $ t.txS))
                         , ("to",                (JSON.toJSON $ t.txToAddr))
                         , ("nonce",             (JSON.toJSON $ show $ t.txNonce))
                         , ("value",             (JSON.toJSON $ show $ t.txValue))
                         , ("type",              (JSON.toJSON $ t.txType))
                         , ("accessList",        (JSON.toJSON $ t.txAccessList))
                         , ("maxPriorityFeePerGas", (JSON.toJSON $ show $ fromJust $ t.txMaxPriorityFeeGas))
                         , ("maxFeePerGas",      (JSON.toJSON $ show $ fromJust $ t.txMaxFeePerGas))
                         , ("chainId",           (JSON.toJSON $ show t.txChainId))
                         ]

emptyTransaction :: Transaction
emptyTransaction = Transaction { txData = mempty
                               , txGasLimit = 0
                               , txGasPrice = Nothing
                               , txNonce = 0
                               , txR = 0
                               , txS = 0
                               , txToAddr = Nothing
                               , txV = 0
                               , txValue = 0
                               , txType = EIP1559Transaction
                               , txAccessList = []
                               , txMaxPriorityFeeGas = Nothing
                               , txMaxFeePerGas = Nothing
                               , txChainId = 1
                               }

-- | utility function for getting a more useful representation of accesslistentries
-- duplicates only matter for gas computation
txAccessMap :: Transaction -> Map Addr [W256]
txAccessMap tx = ((Map.fromListWith (++)) . makeTups) tx.txAccessList
  where makeTups = map (\ale -> (ale.accessAddress , ale.accessStorageKeys ))

-- Given Transaction, it recovers the address that sent it
sender :: Transaction -> Maybe Addr
sender tx = ecrec v' tx.txR  tx.txS hash
  where hash = keccak' (signingData tx)
        v    = tx.txV
        v'   = if v == 27 || v == 28 then v
               else 27 + v

sign :: Integer -> Transaction -> Transaction
sign sk tx = tx { txV = num v, txR = r, txS = s}
  where
    hash = keccak' $ signingData tx
    (v, r, s) = EVM.Sign.sign hash sk

signingData :: Transaction -> ByteString
signingData tx =
  case tx.txType of
    LegacyTransaction -> if v == (tx.txChainId * 2 + 35) || v == (tx.txChainId * 2 + 36)
      then eip155Data
      else normalData
    AccessListTransaction -> eip2930Data
    EIP1559Transaction -> eip1559Data
  where v          = fromIntegral tx.txV
        to'        = case tx.txToAddr of
          Just a  -> BS $ word160Bytes a
          Nothing -> BS mempty
        maxFee = fromJust tx.txMaxFeePerGas
        maxPrio = fromJust tx.txMaxPriorityFeeGas
        gasPrice = fromJust tx.txGasPrice
        accessList = tx.txAccessList
        rlpAccessList = EVM.RLP.List $ map (\accessEntry ->
          EVM.RLP.List [BS $ word160Bytes accessEntry.accessAddress,
                        EVM.RLP.List $ map rlpWordFull accessEntry.accessStorageKeys]
          ) accessList
        normalData = rlpList [rlpWord256 tx.txNonce,
                              rlpWord256 gasPrice,
                              rlpWord256 (num tx.txGasLimit),
                              to',
                              rlpWord256 tx.txValue,
                              BS tx.txData]
        eip155Data = rlpList [rlpWord256 tx.txNonce,
                              rlpWord256 gasPrice,
                              rlpWord256 (num tx.txGasLimit),
                              to',
                              rlpWord256 tx.txValue,
                              BS tx.txData,
                              rlpWord256 tx.txChainId,
                              rlpWord256 0x0,
                              rlpWord256 0x0]
        eip1559Data = cons 0x02 $ rlpList [
          rlpWord256 tx.txChainId,
          rlpWord256 tx.txNonce,
          rlpWord256 maxPrio,
          rlpWord256 maxFee,
          rlpWord256 (num tx.txGasLimit),
          to',
          rlpWord256 tx.txValue,
          BS tx.txData,
          rlpAccessList]

        eip2930Data = cons 0x01 $ rlpList [
          rlpWord256 tx.txChainId,
          rlpWord256 tx.txNonce,
          rlpWord256 gasPrice,
          rlpWord256 (num tx.txGasLimit),
          to',
          rlpWord256 tx.txValue,
          BS tx.txData,
          rlpAccessList]

accessListPrice :: FeeSchedule Word64 -> [AccessListEntry] -> Word64
accessListPrice fs al =
    sum (map
      (\ale ->
        fs.g_access_list_address  +
        (fs.g_access_list_storage_key  * (fromIntegral . length) ale.accessStorageKeys))
        al)

txGasCost :: FeeSchedule Word64 -> Transaction -> Word64
txGasCost fs tx =
  let calldata     = tx.txData
      zeroBytes    = BS.count 0 calldata
      nonZeroBytes = BS.length calldata - zeroBytes
      baseCost     = fs.g_transaction
        + (if isNothing tx.txToAddr then fs.g_txcreate else 0)
        + (accessListPrice fs tx.txAccessList )
      zeroCost     = fs.g_txdatazero
      nonZeroCost  = fs.g_txdatanonzero
  in baseCost + zeroCost * (fromIntegral zeroBytes) + nonZeroCost * (fromIntegral nonZeroBytes)

instance FromJSON AccessListEntry where
  parseJSON (JSON.Object val) = do
    accessAddress_ <- addrField val "address"
    accessStorageKeys_ <- (val JSON..: "storageKeys") >>= parseJSONList
    return $ AccessListEntry accessAddress_ accessStorageKeys_
  parseJSON invalid =
    JSON.typeMismatch "AccessListEntry" invalid

instance FromJSON Transaction where
  parseJSON (JSON.Object val) = do
    tdata    <- dataField val "data"
    gasLimit <- word64Field val "gasLimit"
    gasPrice <- fmap read <$> val JSON..:? "gasPrice"
    maxPrio  <- fmap read <$> val JSON..:? "maxPriorityFeePerGas"
    maxFee   <- fmap read <$> val JSON..:? "maxFeePerGas"
    nonce    <- wordField val "nonce"
    r        <- wordField val "r"
    s        <- wordField val "s"
    toAddr   <- addrFieldMaybe val "to"
    v        <- wordField val "v"
    value    <- wordField val "value"
    txType   <- fmap (read :: String -> Int) <$> (val JSON..:? "type")
    case txType of
      Just 0x00 -> return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing 1
      Just 0x01 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value AccessListTransaction accessListEntries Nothing Nothing 1
      Just 0x02 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value EIP1559Transaction accessListEntries maxPrio maxFee 1
      Just _ -> fail "unrecognized custom transaction type"
      Nothing -> return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing 1
  parseJSON invalid =
    JSON.typeMismatch "Transaction" invalid

accountAt :: Addr -> Getter (Map Addr EVM.Contract) EVM.Contract
accountAt a = (at a) . (to $ fromMaybe newAccount)

touchAccount :: Addr -> Map Addr EVM.Contract -> Map Addr EVM.Contract
touchAccount a = Map.insertWith (flip const) a newAccount

newAccount :: EVM.Contract
newAccount = initialContract $ EVM.RuntimeCode (EVM.ConcreteRuntimeCode "")

-- | Increments origin nonce and pays gas deposit
setupTx :: Addr -> Addr -> W256 -> Word64 -> Map Addr EVM.Contract -> Map Addr EVM.Contract
setupTx origin coinbase gasPrice gasLimit prestate =
  let gasCost = gasPrice * (num gasLimit)
  in (Map.adjust ((over EVM.nonce   (+ 1))
               . (over balance (subtract gasCost))) origin)
    . touchAccount origin
    . touchAccount coinbase $ prestate

-- | Given a valid tx loaded into the vm state,
-- subtract gas payment from the origin, increment the nonce
-- and pay receiving address
initTx :: EVM.VM -> EVM.VM
initTx vm = let
    toAddr   = vm._state._contract
    origin   = vm._tx._origin
    gasPrice = vm._tx._gasprice
    gasLimit = vm._tx._txgaslimit
    coinbase = vm._block._coinbase
    value    = vm._state._callvalue
    toContract = initialContract vm._state._code
    preState = setupTx origin coinbase gasPrice gasLimit vm._env._contracts
    oldBalance = view (accountAt toAddr . balance) preState
    creation = vm._tx._isCreate
    initState = (case unlit value of
      Just v -> ((Map.adjust (over balance (subtract v))) origin)
              . (Map.adjust (over balance (+ v))) toAddr
      Nothing -> id)
      . (if creation
         then Map.insert toAddr (toContract & balance .~ oldBalance)
         else touchAccount toAddr)
      $ preState

    resetConcreteStore s = if creation then Map.insert (num toAddr) mempty s else s

    resetStore (ConcreteStore s) = ConcreteStore (resetConcreteStore s)
    resetStore (SStore a@(Lit _) k v s) = if creation && a == (litAddr toAddr) then resetStore s else (SStore a k v (resetStore s))
    resetStore (SStore {}) = error "cannot reset storage if it contains symbolic addresses"
    resetStore s = s
    in
      vm & EVM.env . EVM.contracts .~ initState
         & EVM.tx . EVM.txReversion .~ preState
         & EVM.env . EVM.storage %~ resetStore
         & EVM.env . EVM.origStorage %~ resetConcreteStore
