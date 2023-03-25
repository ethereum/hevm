module EVM.Dapp where

import EVM (Trace(..), ContractCode(..), Contract(..), RuntimeCode (..))
import EVM.ABI (Event, AbiType, SolError)
import EVM.Concrete
import EVM.Debug (srcMapCodePos)
import EVM.Solidity
import EVM.Types (W256, abiKeccak, keccak', Addr, regexMatches, unlit, unlitByte, FunctionSelector)

import Control.Arrow ((>>>))
import Data.Aeson (Value)
import Data.Bifunctor (first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List (find, sort)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (isJust, fromJust, mapMaybe)
import Data.Sequence qualified as Seq
import Data.Text (Text, isPrefixOf, pack, unpack)
import Data.Text.Encoding (encodeUtf8)
import Data.Vector qualified as V

data DappInfo = DappInfo
  { root       :: FilePath
  , solcByName :: Map Text SolcContract
  , solcByHash :: Map W256 (CodeType, SolcContract)
  , solcByCode :: [(Code, SolcContract)] -- for contracts with `immutable` vars.
  , sources    :: SourceCache
  , unitTests  :: [(Text, [(Test, [AbiType])])]
  , abiMap     :: Map FunctionSelector Method
  , eventMap   :: Map W256 Event
  , errorMap   :: Map W256 SolError
  , astIdMap   :: Map Int Value
  , astSrcMap  :: SrcMap -> Maybe Value
  }

-- | bytecode modulo immutables, to identify contracts
data Code = Code
  { raw :: ByteString
  , immutableLocations :: [Reference]
  }
  deriving Show

data DappContext = DappContext
  { info :: DappInfo
  , env  :: Map Addr Contract
  }

data Test = ConcreteTest Text | SymbolicTest Text | InvariantTest Text

instance Show Test where
  show t = unpack $ extractSig t

dappInfo
  :: FilePath -> Map Text SolcContract -> SourceCache -> DappInfo
dappInfo root solcByName sources =
  let
    solcs = Map.elems solcByName
    astIds = astIdMap $ snd <$> Map.toList sources.asts
    immutables = filter ((/=) mempty . (.immutableReferences)) solcs

  in DappInfo
    { root = root
    , unitTests = findAllUnitTests solcs
    , sources = sources
    , solcByName = solcByName
    , solcByHash =
        let
          f g k = Map.fromList [(g x, (k, x)) | x <- solcs]
        in
          mappend
           (f (.runtimeCodehash)  Runtime)
           (f (.creationCodehash) Creation)
      -- contracts with immutable locations can't be id by hash
    , solcByCode =
      [(Code x.runtimeCode (concat $ Map.elems x.immutableReferences), x) | x <- immutables]
      -- Sum up the ABI maps from all the contracts.
    , abiMap   = mconcat (map (.abiMap) solcs)
    , eventMap = mconcat (map (.eventMap) solcs)
    , errorMap = mconcat (map (.errorMap) solcs)

    , astIdMap  = astIds
    , astSrcMap = astSrcMap astIds
    }

emptyDapp :: DappInfo
emptyDapp = dappInfo "" mempty (SourceCache mempty mempty mempty)

-- Dapp unit tests are detected by searching within abi methods
-- that begin with "test" or "prove", that are in a contract with
-- the "IS_TEST()" abi marker, for a given regular expression.
--
-- The regex is matched on the full test method name, including path
-- and contract, i.e. "path/to/file.sol:TestContract.test_name()".
--
-- Tests beginning with "test" are interpreted as concrete tests, whereas
-- tests beginning with "prove" are interpreted as symbolic tests.

unitTestMarkerAbi :: FunctionSelector
unitTestMarkerAbi = abiKeccak (encodeUtf8 "IS_TEST()")

findAllUnitTests :: [SolcContract] -> [(Text, [(Test, [AbiType])])]
findAllUnitTests = findUnitTests ".*:.*\\.(test|prove|invariant).*"

mkTest :: Text -> Maybe Test
mkTest sig
  | "test" `isPrefixOf` sig = Just (ConcreteTest sig)
  | "prove" `isPrefixOf` sig = Just (SymbolicTest sig)
  | "invariant" `isPrefixOf` sig = Just (InvariantTest sig)
  | otherwise = Nothing

findUnitTests :: Text -> ([SolcContract] -> [(Text, [(Test, [AbiType])])])
findUnitTests match =
  concatMap $ \c ->
    case Map.lookup unitTestMarkerAbi c.abiMap of
      Nothing -> []
      Just _  ->
        let testNames = unitTestMethodsFiltered (regexMatches match) c
        in [(c.contractName, testNames) | not (BS.null c.runtimeCode) && not (null testNames)]

unitTestMethodsFiltered :: (Text -> Bool) -> (SolcContract -> [(Test, [AbiType])])
unitTestMethodsFiltered matcher c =
  let
    testName method = c.contractName <> "." <> (extractSig (fst method))
  in
    filter (matcher . testName) (unitTestMethods c)

unitTestMethods :: SolcContract -> [(Test, [AbiType])]
unitTestMethods =
  (.abiMap)
  >>> Map.elems
  >>> map (\f -> (mkTest f.methodSignature, snd <$> f.inputs))
  >>> filter (isJust . fst)
  >>> fmap (first fromJust)

extractSig :: Test -> Text
extractSig (ConcreteTest sig) = sig
extractSig (SymbolicTest sig) = sig
extractSig (InvariantTest sig) = sig

traceSrcMap :: DappInfo -> Trace -> Maybe SrcMap
traceSrcMap dapp trace = srcMap dapp trace._traceContract trace._traceOpIx

srcMap :: DappInfo -> Contract -> Int -> Maybe SrcMap
srcMap dapp contr opIndex = do
  sol <- findSrc contr dapp
  case contr._contractcode of
    (InitCode _ _) ->
      Seq.lookup opIndex sol.creationSrcmap
    (RuntimeCode _) ->
      Seq.lookup opIndex sol.runtimeSrcmap

findSrc :: Contract -> DappInfo -> Maybe SolcContract
findSrc c dapp = do
  hash <- unlit c._codehash
  case Map.lookup hash dapp.solcByHash of
    Just (_, v) -> Just v
    Nothing -> lookupCode c._contractcode dapp


lookupCode :: ContractCode -> DappInfo -> Maybe SolcContract
lookupCode (InitCode c _) a =
  snd <$> Map.lookup (keccak' (stripBytecodeMetadata c)) a.solcByHash
lookupCode (RuntimeCode (ConcreteRuntimeCode c)) a =
  case snd <$> Map.lookup (keccak' (stripBytecodeMetadata c)) a.solcByHash of
    Just x -> return x
    Nothing -> snd <$> find (compareCode c . fst) a.solcByCode
lookupCode (RuntimeCode (SymbolicRuntimeCode c)) a = let
    code = BS.pack $ mapMaybe unlitByte $ V.toList c
  in case snd <$> Map.lookup (keccak' (stripBytecodeMetadata code)) a.solcByHash of
    Just x -> return x
    Nothing -> snd <$> find (compareCode code . fst) a.solcByCode

compareCode :: ByteString -> Code -> Bool
compareCode raw (Code template locs) =
  let holes' = sort [(start, len) | (Reference start len) <- locs]
      insert at' len' bs = writeMemory (BS.replicate len' 0) (fromIntegral len') 0 (fromIntegral at') bs
      refined = foldr (\(start, len) acc -> insert start len acc) raw holes'
  in BS.length raw == BS.length template && template == refined

showTraceLocation :: DappInfo -> Trace -> Either Text Text
showTraceLocation dapp trace =
  case traceSrcMap dapp trace of
    Nothing -> Left "<no source map>"
    Just sm ->
      case srcMapCodePos dapp.sources sm of
        Nothing -> Left "<source not found>"
        Just (fileName, lineIx) ->
          Right (fileName <> ":" <> pack (show lineIx))
