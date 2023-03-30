module EVM.Transaction where

import Prelude hiding (Word)

import qualified EVM
import EVM (initialContract)
import EVM.FeeSchedule
import EVM.RLP
import EVM.Types
import EVM.Expr (litAddr)
import EVM.Sign

import Optics.Core hiding (cons)

import Data.ByteString (ByteString, cons)
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
  address :: Addr,
  storageKeys :: [W256]
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
    txdata            :: ByteString,
    gasLimit          :: Word64,
    gasPrice          :: Maybe W256,
    nonce             :: W256,
    r                 :: W256,
    s                 :: W256,
    toAddr            :: Maybe Addr,
    v                 :: W256,
    value             :: W256,
    txtype            :: TxType,
    accessList        :: [AccessListEntry],
    maxPriorityFeeGas :: Maybe W256,
    maxFeePerGas      :: Maybe W256,
    chainId           :: W256
} deriving (Show, Generic)

instance JSON.ToJSON Transaction where
  toJSON t = JSON.object [ ("input",             (JSON.toJSON (ByteStringS t.txdata)))
                         , ("gas",               (JSON.toJSON $ "0x" ++ showHex (toInteger $ t.gasLimit) ""))
                         , ("gasPrice",          (JSON.toJSON $ show $ fromJust $ t.gasPrice))
                         , ("v",                 (JSON.toJSON $ show $ (t.v)-27))
                         , ("r",                 (JSON.toJSON $ show $ t.r))
                         , ("s",                 (JSON.toJSON $ show $ t.s))
                         , ("to",                (JSON.toJSON $ t.toAddr))
                         , ("nonce",             (JSON.toJSON $ show $ t.nonce))
                         , ("value",             (JSON.toJSON $ show $ t.value))
                         , ("type",              (JSON.toJSON $ t.txtype))
                         , ("accessList",        (JSON.toJSON $ t.accessList))
                         , ("maxPriorityFeePerGas", (JSON.toJSON $ show $ fromJust $ t.maxPriorityFeeGas))
                         , ("maxFeePerGas",      (JSON.toJSON $ show $ fromJust $ t.maxFeePerGas))
                         , ("chainId",           (JSON.toJSON $ show t.chainId))
                         ]

emptyTransaction :: Transaction
emptyTransaction = Transaction { txdata = mempty
                               , gasLimit = 0
                               , gasPrice = Nothing
                               , nonce = 0
                               , r = 0
                               , s = 0
                               , toAddr = Nothing
                               , v = 0
                               , value = 0
                               , txtype = EIP1559Transaction
                               , accessList = []
                               , maxPriorityFeeGas = Nothing
                               , maxFeePerGas = Nothing
                               , chainId = 1
                               }

-- | utility function for getting a more useful representation of accesslistentries
-- duplicates only matter for gas computation
txAccessMap :: Transaction -> Map Addr [W256]
txAccessMap tx = ((Map.fromListWith (++)) . makeTups) tx.accessList
  where makeTups = map (\ale -> (ale.address , ale.storageKeys ))

-- Given Transaction, it recovers the address that sent it
sender :: Transaction -> Maybe Addr
sender tx = ecrec v' tx.r  tx.s hash
  where hash = keccak' (signingData tx)
        v    = tx.v
        v'   = if v == 27 || v == 28 then v
               else 27 + v

sign :: Integer -> Transaction -> Transaction
sign sk tx = tx { v = num v, r = r, s = s}
  where
    hash = keccak' $ signingData tx
    (v, r, s) = EVM.Sign.sign hash sk

signingData :: Transaction -> ByteString
signingData tx =
  case tx.txtype of
    LegacyTransaction -> if v == (tx.chainId * 2 + 35) || v == (tx.chainId * 2 + 36)
      then eip155Data
      else normalData
    AccessListTransaction -> eip2930Data
    EIP1559Transaction -> eip1559Data
  where v          = fromIntegral tx.v
        to'        = case tx.toAddr of
          Just a  -> BS $ word160Bytes a
          Nothing -> BS mempty
        maxFee = fromJust tx.maxFeePerGas
        maxPrio = fromJust tx.maxPriorityFeeGas
        gasPrice = fromJust tx.gasPrice
        accessList = tx.accessList
        rlpAccessList = EVM.RLP.List $ map (\accessEntry ->
          EVM.RLP.List [BS $ word160Bytes accessEntry.address,
                        EVM.RLP.List $ map rlpWordFull accessEntry.storageKeys]
          ) accessList
        normalData = rlpList [rlpWord256 tx.nonce,
                              rlpWord256 gasPrice,
                              rlpWord256 (num tx.gasLimit),
                              to',
                              rlpWord256 tx.value,
                              BS tx.txdata]
        eip155Data = rlpList [rlpWord256 tx.nonce,
                              rlpWord256 gasPrice,
                              rlpWord256 (num tx.gasLimit),
                              to',
                              rlpWord256 tx.value,
                              BS tx.txdata,
                              rlpWord256 tx.chainId,
                              rlpWord256 0x0,
                              rlpWord256 0x0]
        eip1559Data = cons 0x02 $ rlpList [
          rlpWord256 tx.chainId,
          rlpWord256 tx.nonce,
          rlpWord256 maxPrio,
          rlpWord256 maxFee,
          rlpWord256 (num tx.gasLimit),
          to',
          rlpWord256 tx.value,
          BS tx.txdata,
          rlpAccessList]

        eip2930Data = cons 0x01 $ rlpList [
          rlpWord256 tx.chainId,
          rlpWord256 tx.nonce,
          rlpWord256 gasPrice,
          rlpWord256 (num tx.gasLimit),
          to',
          rlpWord256 tx.value,
          BS tx.txdata,
          rlpAccessList]

accessListPrice :: FeeSchedule Word64 -> [AccessListEntry] -> Word64
accessListPrice fs al =
    sum (map
      (\ale ->
        fs.g_access_list_address  +
        (fs.g_access_list_storage_key  * (fromIntegral . length) ale.storageKeys))
        al)

txGasCost :: FeeSchedule Word64 -> Transaction -> Word64
txGasCost fs tx =
  let calldata     = tx.txdata
      zeroBytes    = BS.count 0 calldata
      nonZeroBytes = BS.length calldata - zeroBytes
      baseCost     = fs.g_transaction
        + (if isNothing tx.toAddr then fs.g_txcreate else 0)
        + (accessListPrice fs tx.accessList )
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
accountAt a = (at a) % (to $ fromMaybe newAccount)

touchAccount :: Addr -> Map Addr EVM.Contract -> Map Addr EVM.Contract
touchAccount a = Map.insertWith (flip const) a newAccount

newAccount :: EVM.Contract
newAccount = initialContract $ EVM.RuntimeCode (EVM.ConcreteRuntimeCode "")

-- | Increments origin nonce and pays gas deposit
setupTx :: Addr -> Addr -> W256 -> Word64 -> Map Addr EVM.Contract -> Map Addr EVM.Contract
setupTx origin coinbase gasPrice gasLimit prestate =
  let gasCost = gasPrice * (num gasLimit)
  in (Map.adjust ((over #nonce   (+ 1))
               . (over #balance (subtract gasCost))) origin)
    . touchAccount origin
    . touchAccount coinbase $ prestate

-- | Given a valid tx loaded into the vm state,
-- subtract gas payment from the origin, increment the nonce
-- and pay receiving address
initTx :: EVM.VM -> EVM.VM
initTx vm = let
    toAddr   = vm.state.contract
    origin   = vm.tx.origin
    gasPrice = vm.tx.gasprice
    gasLimit = vm.tx.gaslimit
    coinbase = vm.block.coinbase
    value    = vm.state.callvalue
    toContract = initialContract vm.state.code
    preState = setupTx origin coinbase gasPrice gasLimit vm.env.contracts
    oldBalance = view (accountAt toAddr % #balance) preState
    creation = vm.tx.isCreate
    initState = (case unlit value of
      Just v -> ((Map.adjust (over #balance (subtract v))) origin)
              . (Map.adjust (over #balance (+ v))) toAddr
      Nothing -> id)
      . (if creation
         then Map.insert toAddr (toContract & #balance .~ oldBalance)
         else touchAccount toAddr)
      $ preState

    resetConcreteStore s = if creation then Map.insert (num toAddr) mempty s else s

    resetStore (ConcreteStore s) = ConcreteStore (resetConcreteStore s)
    resetStore (SStore a@(Lit _) k v s) = if creation && a == (litAddr toAddr) then resetStore s else (SStore a k v (resetStore s))
    resetStore (SStore {}) = error "cannot reset storage if it contains symbolic addresses"
    resetStore s = s
    in
      vm & #env % #contracts .~ initState
         & #tx % #txReversion .~ preState
         & #env % #storage %~ resetStore
         & #env % #origStorage %~ resetConcreteStore
