module EVM.Transaction where

import Prelude hiding (Word)

import qualified EVM
import EVM (balance, initialContract)
import EVM.FeeSchedule
import EVM.Precompiled (execute)
import EVM.RLP
import EVM.Types
import EVM.Expr (litAddr)

import Control.Lens

import Data.Aeson (FromJSON (..))
import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Maybe (fromMaybe, isNothing, fromJust)
import GHC.Generics (Generic)

import qualified Data.Aeson        as JSON
import qualified Data.Aeson.Types  as JSON
import qualified Data.ByteString   as BS
import qualified Data.Map          as Map
import Data.Word (Word64)

import Crypto.Number.ModArithmetic (expFast)
import qualified Crypto.Hash as Crypto
import Crypto.Hash (Digest, SHA256, RIPEMD160, digestFromByteString)
import Crypto.PubKey.ECC.ECDSA (signDigestWith, PrivateKey(..), Signature(..))
import Crypto.PubKey.ECC.Types (getCurveByName, CurveName(..), Point(..))
import Crypto.PubKey.ECC.Generate (generateQ)
import Data.Memory.Encoding.Base16 (toHexadecimal)
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
instance JSON.ToJSON TxType

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
    txMaxFeePerGas :: Maybe W256
} deriving (Show, Generic)
instance JSON.ToJSON Transaction where
  toJSON t = JSON.object [ ("input",             (JSON.toJSON $ txData t))
                         , ("gas",               (JSON.toJSON $ ("0x" ++ showHex (toInteger $ txGasLimit t) "")))
                         , ("gasPrice",          (JSON.toJSON $ (show $ fromJust $ txGasPrice t)))
                         -- , ("txNonce",           (JSON.toJSON $ txNonce   t))
                         , ("v",                 (JSON.toJSON $ show $ txV       t))
                         , ("r",                 (JSON.toJSON $ show $ txR       t))
                         , ("s",                 (JSON.toJSON $ show $ txS       t))
                         , ("to",                (JSON.toJSON $ txToAddr  t))
                         , ("nonce",             (JSON.toJSON $ (show $ txV       t)))
                         , ("value",             (JSON.toJSON $ (show $ txValue   t)))
                         -- , ("type",              (JSON.toJSON $ txType    t))
                         , ("accessList",        (JSON.toJSON $ txAccessList t))
                         , ("maxPriorityFeeGas", (JSON.toJSON $ txMaxPriorityFeeGas t))
                         -- , ("maxFeePerGas",      (JSON.toJSON $ txMaxFeePerGas t))
                         ]

exampleTransaction = Transaction { txData     = mempty
                                 , txGasLimit = 0xffff
                                 , txGasPrice = Just 0
                                 , txNonce    = 420
                                 , txR        = 330
                                 , txS        = 330
                                 , txToAddr   = Just 0x0
                                 , txV        = 0
                                 , txValue    = 0
                                 , txType     = EIP1559Transaction
                                 , txAccessList = []
                                 , txMaxPriorityFeeGas =  Just 1
                                 , txMaxFeePerGas = Just 1
                                 }

-- | utility function for getting a more useful representation of accesslistentries
-- duplicates only matter for gas computation
txAccessMap :: Transaction -> Map Addr [W256]
txAccessMap tx = ((Map.fromListWith (++)) . makeTups) $ txAccessList tx
  where makeTups = map (\ale -> (accessAddress ale, accessStorageKeys ale))

ecrec :: W256 -> W256 -> W256 -> W256 -> Maybe Addr
ecrec v r s e = num . word <$> EVM.Precompiled.execute 1 input 32
  where input = BS.concat (word256Bytes <$> [e, v, r, s])

sender :: Int -> Transaction -> Maybe Addr
sender chainId tx = ecrec v' (txR tx) (txS tx) hash
  where hash = keccak' (signingData chainId tx)
        v    = txV tx
        v'   = if v == 27 || v == 28 then v
               else 27 + v


sign :: Int -> Integer -> Transaction -> Transaction
sign chainId sk tx = tx { txR = num $ sign_r sig
                        , txS = num $ sign_s sig
                        , txV = 28}
  where
    curve = getCurveByName SEC_p256k1
    priv = PrivateKey curve sk
    digest = digestFromByteString (word256Bytes $ keccak' $ signingData chainId tx)
    sig = ethsign priv (fromJust digest)


-- | We don't wanna introduce the machinery needed to sign with a random nonce,
-- so we just use the same nonce every time (420). This is obviusly very
-- insecure, but fine for testing purposes.
ethsign :: PrivateKey -> Digest Crypto.Keccak_256 -> Signature
ethsign sk digest = go 420
  where
    go k = case signDigestWith k sk digest of
       Nothing  -> go (k + 1)
       Just sig -> sig



signingData :: Int -> Transaction -> ByteString
signingData chainId tx =
  case txType tx of
    LegacyTransaction -> if v == (chainId * 2 + 35) || v == (chainId * 2 + 36)
      then eip155Data
      else normalData
    AccessListTransaction -> eip2930Data
    EIP1559Transaction -> eip1559Data
  where v          = fromIntegral (txV tx)
        to'        = case txToAddr tx of
          Just a  -> BS $ word160Bytes a
          Nothing -> BS mempty
        maxFee = fromJust $ txMaxFeePerGas tx
        maxPrio = fromJust $ txMaxPriorityFeeGas tx
        gasPrice = fromJust $ txGasPrice tx
        accessList = txAccessList tx
        rlpAccessList = EVM.RLP.List $ map (\accessEntry ->
          EVM.RLP.List [BS $ word160Bytes (accessAddress accessEntry),
                        EVM.RLP.List $ map rlpWordFull $ accessStorageKeys accessEntry]
          ) accessList
        normalData = rlpList [rlpWord256 (txNonce tx),
                              rlpWord256 gasPrice,
                              rlpWord256 (num $ txGasLimit tx),
                              to',
                              rlpWord256 (txValue tx),
                              BS (txData tx)]
        eip155Data = rlpList [rlpWord256 (txNonce tx),
                              rlpWord256 gasPrice,
                              rlpWord256 (num $ txGasLimit tx),
                              to',
                              rlpWord256 (txValue tx),
                              BS (txData tx),
                              rlpWord256 (fromIntegral chainId),
                              rlpWord256 0x0,
                              rlpWord256 0x0]
        eip1559Data = cons 0x02 $ rlpList [
          rlpWord256 (fromIntegral chainId),
          rlpWord256 (txNonce tx),
          rlpWord256 maxPrio,
          rlpWord256 maxFee,
          rlpWord256 (num $ txGasLimit tx),
          to',
          rlpWord256 (txValue tx),
          BS (txData tx),
          rlpAccessList]

        eip2930Data = cons 0x01 $ rlpList [
          rlpWord256 (fromIntegral chainId),
          rlpWord256 (txNonce tx),
          rlpWord256 gasPrice,
          rlpWord256 (num $ txGasLimit tx),
          to',
          rlpWord256 (txValue tx),
          BS (txData tx),
          rlpAccessList]

accessListPrice :: FeeSchedule Word64 -> [AccessListEntry] -> Word64
accessListPrice fs al =
    sum (map
      (\ale ->
        g_access_list_address fs +
        (g_access_list_storage_key fs * (fromIntegral . length) (accessStorageKeys ale)))
        al)

txGasCost :: FeeSchedule Word64 -> Transaction -> Word64
txGasCost fs tx =
  let calldata     = txData tx
      zeroBytes    = BS.count 0 calldata
      nonZeroBytes = BS.length calldata - zeroBytes
      baseCost     = g_transaction fs
        + (if isNothing (txToAddr tx) then g_txcreate fs else 0)
        + (accessListPrice fs $ txAccessList tx)
      zeroCost     = g_txdatazero fs
      nonZeroCost  = g_txdatanonzero fs
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
      Just 0x00 -> return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing
      Just 0x01 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value AccessListTransaction accessListEntries Nothing Nothing
      Just 0x02 -> do
        accessListEntries <- (val JSON..: "accessList") >>= parseJSONList
        return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value EIP1559Transaction accessListEntries maxPrio maxFee
      Just _ -> fail "unrecognized custom transaction type"
      Nothing -> return $ Transaction tdata gasLimit gasPrice nonce r s toAddr v value LegacyTransaction [] Nothing Nothing
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
    toAddr   = view (EVM.state . EVM.contract) vm
    origin   = view (EVM.tx . EVM.origin) vm
    gasPrice = view (EVM.tx . EVM.gasprice) vm
    gasLimit = view (EVM.tx . EVM.txgaslimit) vm
    coinbase = view (EVM.block . EVM.coinbase) vm
    value    = view (EVM.state . EVM.callvalue) vm
    toContract = initialContract (view (EVM.state . EVM.code) vm)
    preState = setupTx origin coinbase gasPrice gasLimit $ view (EVM.env . EVM.contracts) vm
    oldBalance = view (accountAt toAddr . balance) preState
    creation = view (EVM.tx . EVM.isCreate) vm
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
