module EVM.StorageLayout where

-- Figures out the layout of storage slots for Solidity contracts.

import EVM.Dapp (DappInfo(..))
import EVM.Solidity (SolcContract, creationSrcmap, SlotType(..))
import EVM.ABI (AbiType (..), parseTypeName)

import Optics.Core
import Data.Aeson (Value (..))
import Data.Aeson.Optics
import Data.Foldable (toList)
import Data.List.NonEmpty qualified as NonEmpty
import Data.Map qualified as Map
import Data.Maybe (fromMaybe, isJust)
import Data.Sequence qualified as Seq
import Data.Text (Text, unpack, pack, words)
import EVM.Types (internalError)

import Prelude hiding (words)

-- A contract has all the slots of its inherited contracts.
--
-- The slot order is determined by the inheritance linearization order,
-- so we first have to calculate that.
--
-- This information is available in the abstract syntax tree.

findContractDefinition :: DappInfo -> SolcContract -> Maybe Value
findContractDefinition dapp solc =
  -- The first source mapping in the contract's creation code
  -- corresponds to the source field of the contract definition.
  case Seq.viewl solc.creationSrcmap of
    firstSrcMap Seq.:< _ ->
      dapp.astSrcMap firstSrcMap
    _ ->
      Nothing

storageLayout :: DappInfo -> SolcContract -> [Text]
storageLayout dapp solc =
  let
    root :: Value
    root =
      fromMaybe Null
        (findContractDefinition dapp solc)
  in
    case preview ( key "attributes"
                 % key "linearizedBaseContracts"
                 % _Array
                 ) root of
      Nothing ->
        []
      Just ((reverse . toList) -> linearizedBaseContracts) ->
        flip concatMap linearizedBaseContracts
          (\case
             Number i -> fromMaybe (error $ internalError "malformed AST JSON") $
               storageVariablesForContract =<<
                 Map.lookup (floor i) dapp.astIdMap
             _ ->
               error $ internalError "malformed AST JSON")

storageVariablesForContract :: Value -> Maybe [Text]
storageVariablesForContract node = do
  name <- preview (ix "attributes" % key "name" % _String) node
  vars <-
    fmap
      (filter isStorageVariableDeclaration . toList)
      (preview (ix "children" % _Array) node)

  pure . flip map vars $
    \x ->
      case preview (key "attributes" % key "name" % _String) x of
        Just variableName ->
          mconcat
            [ variableName
            , " (", name, ")"
            , "\n", "  Type: "
            , pack $ show (slotTypeForDeclaration x)
            ]
        Nothing ->
          error $ internalError "malformed variable declaration"

nodeIs :: Text -> Value -> Bool
nodeIs t x = isSourceNode && hasRightName
  where
    isSourceNode =
      isJust (preview (key "src") x)
    hasRightName =
      Just t == preview (key "name" % _String) x

isStorageVariableDeclaration :: Value -> Bool
isStorageVariableDeclaration x =
  nodeIs "VariableDeclaration" x
    && preview (key "attributes" % key "constant" % _Bool) x /= Just True

slotTypeForDeclaration :: Value -> SlotType
slotTypeForDeclaration node =
  case toList <$> preview (key "children" % _Array) node of
    Just (x:_) ->
      grokDeclarationType x
    _ ->
      error $ internalError "malformed AST"

grokDeclarationType :: Value -> SlotType
grokDeclarationType x =
  case preview (key "name" % _String) x of
    Just "Mapping" ->
      case preview (key "children" % _Array) x of
        Just (toList -> xs) ->
          grokMappingType xs
        _ ->
          error $ internalError "malformed AST"
    Just _ ->
      StorageValue (grokValueType x)
    _ ->
      error $ internalError ("malformed AST " ++ show x)

grokMappingType :: [Value] -> SlotType
grokMappingType [s, t] =
  case (grokDeclarationType s, grokDeclarationType t) of
    (StorageValue s', StorageMapping t' x) ->
      StorageMapping (NonEmpty.cons s' t') x
    (StorageValue s', StorageValue t') ->
      StorageMapping (pure s') t'
    (StorageMapping _ _, _) ->
      error $ internalError "unexpected mapping as mapping key"
grokMappingType _ =
  error $ internalError "unexpected AST child count for mapping"

grokValueType :: Value -> AbiType
grokValueType x =
  case ( preview (key "name" % _String) x
       , preview (key "children" % _Array) x
       , preview (key "attributes" % key "type" % _String) x
       ) of
    (Just "ElementaryTypeName", _, Just typeName) ->
      fromMaybe (error $ internalError "ungrokked value type: " ++ show typeName)
        (parseTypeName mempty (head (words typeName)))
    (Just "UserDefinedTypeName", _, _) ->
      AbiAddressType
    (Just "ArrayTypeName", fmap toList -> Just [t], _)->
      AbiArrayDynamicType (grokValueType t)
    (Just "ArrayTypeName", fmap toList -> Just [t, n], _)->
      case ( preview (key "name" % _String) n
           , preview (key "attributes" % key "value" % _String) n
           ) of
        (Just "Literal", Just ((read . unpack) -> i)) ->
          AbiArrayType i (grokValueType t)
        _ ->
          error $ internalError "malformed AST"
    _ ->
      error $ internalError ("unknown value type " ++ show x)
