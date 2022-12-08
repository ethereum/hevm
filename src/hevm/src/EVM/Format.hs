{-# Language DataKinds #-}
{-# Language ImplicitParams #-}


module EVM.Format
  ( formatExpr
  , contractNamePart
  , contractPathPart
  , showTree
  , showTraceTree
  , prettyvmresult
  , showCall
  , showWordExact
  , showWordExplanation
  , parenthesise
  , unindexed
  , showValue
  , textValues
  , showAbiValue
  , prettyIfConcreteWord
  , formatBytes
  , formatBinary
  , indent
  ) where

import Prelude hiding (Word)

import qualified EVM
import EVM.Dapp (DappInfo (..), dappSolcByHash, dappAbiMap, showTraceLocation, dappEventMap, dappErrorMap)
import EVM.Dapp (DappContext (..), contextInfo, contextEnv)
import EVM (VM, VMResult(..), cheatCode, traceForest, traceData, Error (..), result)
import EVM (Trace, TraceData (..), Query (..), FrameContext (..))
import EVM.Types (maybeLitWord, W256 (..), num, word, Expr(..), EType(..), hexByteString, word256Bytes)
import EVM.Types (Addr, ByteStringS(..))
import EVM.ABI (AbiValue (..), Event (..), AbiType (..), SolError (..))
import EVM.ABI (Indexed (NotIndexed), getAbiSeq)
import EVM.ABI (parseTypeName, formatString)
import EVM.SMT
import EVM.Solidity (SolcContract(..), contractName, abiMap)
import EVM.Solidity (methodOutput, methodSignature, methodName)
import EVM.Hexdump

import Control.Arrow ((>>>))
import Control.Lens (view, preview, ix, _2, to, makeLenses, over, each, (^?!))
import Data.Binary.Get (runGetOrFail)
import Data.Bits       (shiftR)
import Data.ByteString (ByteString)
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Lazy (toStrict, fromStrict)
import Data.DoubleWord (signedWord)
import Data.Foldable (toList)
import Data.Maybe (catMaybes, fromMaybe)
import Data.Text (Text, pack, unpack, intercalate)
import Data.Text (dropEnd, splitOn)
import Data.Text.Encoding (decodeUtf8, decodeUtf8')
import Data.Tree (Tree (Node))
import Data.Tree.View (showTree)
import Data.Vector (Vector)
import Data.Word (Word32)
import Data.Char (isSpace)
import Data.List (foldl')
import Numeric (showHex)

import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as BS16
import qualified Data.Char as Char
import qualified Data.Map as Map
import qualified Data.Text as Text
import qualified EVM.Expr as Expr
import qualified Data.Text as T

data Signedness = Signed | Unsigned
  deriving (Show)

showDec :: Signedness -> W256 -> Text
showDec signed (W256 w) =
  let
    i = case signed of
          Signed   -> num (signedWord w)
          Unsigned -> num w
  in
    if i == num cheatCode
    then "<hevm cheat address>"
    else if (i :: Integer) == 2 ^ (256 :: Integer) - 1
    then "MAX_UINT256"
    else Text.pack (show (i :: Integer))

showWordExact :: W256 -> Text
showWordExact w = humanizeInteger w

showWordExplanation :: W256 -> DappInfo -> Text
showWordExplanation w _ | w > 0xffffffff = showDec Unsigned w
showWordExplanation w dapp =
  case Map.lookup (fromIntegral w) (view dappAbiMap dapp) of
    Nothing -> showDec Unsigned w
    Just x  -> "keccak(\"" <> view methodSignature x <> "\")"

humanizeInteger :: (Num a, Integral a, Show a) => a -> Text
humanizeInteger =
  Text.intercalate ","
  . reverse
  . map Text.reverse
  . Text.chunksOf 3
  . Text.reverse
  . Text.pack
  . show

prettyIfConcreteWord :: Expr EWord -> Text
prettyIfConcreteWord = \case
  Lit w -> T.pack $ "0x" <> showHex w ""
  w -> T.pack $ show w

showAbiValue :: (?context :: DappContext) => AbiValue -> Text
showAbiValue (AbiBytes _ bs) =
  formatBytes bs  -- opportunistically decodes recognisable strings
showAbiValue (AbiAddress addr) =
  let dappinfo = view contextInfo ?context
      contracts = view contextEnv ?context
      name = case (Map.lookup addr contracts) of
        Nothing -> ""
        Just contract ->
          let hash = maybeLitWord $ view EVM.codehash contract
          in case hash of
               Just h -> maybeContractName' (preview (dappSolcByHash . ix h . _2) dappinfo)
               Nothing -> ""
  in
    name <> "@" <> (pack $ show addr)
showAbiValue v = pack $ show v

showAbiValues :: (?context :: DappContext) => Vector AbiValue -> Text
showAbiValues vs = parenthesise (textAbiValues vs)

textAbiValues :: (?context :: DappContext) => Vector AbiValue -> [Text]
textAbiValues vs = toList (fmap showAbiValue vs)

textValues :: (?context :: DappContext) => [AbiType] -> Expr Buf -> [Text]
textValues ts (ConcreteBuf bs) =
  case runGetOrFail (getAbiSeq (length ts) ts) (fromStrict bs) of
    Right (_, _, xs) -> textAbiValues xs
    Left (_, _, _)   -> [formatBinary bs]
textValues ts _ = fmap (const "<symbolic>") ts

parenthesise :: [Text] -> Text
parenthesise ts = "(" <> intercalate ", " ts <> ")"

showValues :: (?context :: DappContext) => [AbiType] -> Expr Buf -> Text
showValues ts b = parenthesise $ textValues ts b

showValue :: (?context :: DappContext) => AbiType -> Expr Buf -> Text
showValue t b = head $ textValues [t] b

showCall :: (?context :: DappContext) => [AbiType] -> Expr Buf -> Text
showCall ts (ConcreteBuf bs) = showValues ts $ ConcreteBuf (BS.drop 4 bs)
showCall _ _ = "<symbolic>"

showError :: (?context :: DappContext) => Expr Buf -> Text
showError (ConcreteBuf bs) =
  let dappinfo = view contextInfo ?context
      bs4 = BS.take 4 bs
  in case Map.lookup (word bs4) (view dappErrorMap dappinfo) of
      Just (SolError errName ts) -> errName <> " " <> showCall ts (ConcreteBuf bs)
      Nothing -> case bs4 of
                  -- Method ID for Error(string)
                  "\b\195y\160" -> showCall [AbiStringType] (ConcreteBuf bs)
                  -- Method ID for Panic(uint256)
                  "NH{q"        -> "Panic" <> showCall [AbiUIntType 256] (ConcreteBuf bs)
                  _             -> formatBinary bs
showError b = T.pack $ show b

-- the conditions under which bytes will be decoded and rendered as a string
isPrintable :: ByteString -> Bool
isPrintable =
  decodeUtf8' >>>
    either
      (const False)
      (Text.all (\c-> Char.isPrint c && (not . Char.isControl) c))

formatBytes :: ByteString -> Text
formatBytes b =
  let (s, _) = BS.spanEnd (== 0) b
  in
    if isPrintable s
    then formatBString s
    else formatBinary b

formatSBytes :: Expr Buf -> Text
formatSBytes = undefined
--formatSBytes (SymbolicBuffer b) = "<" <> pack (show (length b)) <> " symbolic bytes>"
--formatSBytes (ConcreteBuffer b) = formatBytes b

-- a string that came from bytes, displayed with special quotes
formatBString :: ByteString -> Text
formatBString b = mconcat [ "«",  Text.dropAround (=='"') (pack $ formatString b), "»" ]

formatSString :: Expr Buf -> Text
formatSString = undefined
--formatSString (SymbolicBuffer bs) = "<" <> pack (show (length bs)) <> " symbolic bytes (string)>"
--formatSString (ConcreteBuffer bs) = pack $ formatString bs

formatBinary :: ByteString -> Text
formatBinary =
  (<>) "0x" . decodeUtf8 . toStrict . toLazyByteString . byteStringHex

formatSBinary :: Expr Buf -> Text
formatSBinary (ConcreteBuf bs) = formatBinary bs
formatSBinary (AbstractBuf t) = "<" <> t <> " abstract buf>"
formatSBinary _ = error "formatSBinary: implement me"

showTraceTree :: DappInfo -> VM -> Text
showTraceTree dapp vm =
  let forest = traceForest vm
      traces = fmap (fmap (unpack . showTrace dapp vm)) forest
  in pack $ concatMap showTree traces

unindexed :: [(Text, AbiType, Indexed)] -> [AbiType]
unindexed ts = [t | (_, t, NotIndexed) <- ts]

showTrace :: DappInfo -> VM -> Trace -> Text
showTrace dapp vm trace =
  let ?context = DappContext { _contextInfo = dapp, _contextEnv = vm ^?! EVM.env . EVM.contracts }
  in let
    pos =
      case showTraceLocation dapp trace of
        Left x -> " \x1b[1m" <> x <> "\x1b[0m"
        Right x -> " \x1b[1m(" <> x <> ")\x1b[0m"
    fullAbiMap = view dappAbiMap dapp
  in case view traceData trace of
    EventTrace _ bytes topics ->
      let logn = mconcat
            [ "\x1b[36m"
            , "log" <> (pack (show (length topics)))
            , parenthesise ((map (pack . show) topics) ++ [formatSBinary bytes])
            , "\x1b[0m"
            ] <> pos
          knownTopic name types = mconcat
            [ "\x1b[36m"
            , name
            , showValues (unindexed types) bytes
            -- todo: show indexed
            , "\x1b[0m"
            ] <> pos
          lognote sig usr = mconcat
            [ "\x1b[36m"
            , "LogNote"
            , parenthesise [sig, usr, "..."]
            , "\x1b[0m"
            ] <> pos
      in case topics of
        [] ->
          logn
        (t1:_) ->
          case maybeLitWord t1 of
            Just topic ->
              case Map.lookup (topic) (view dappEventMap dapp) of
                Just (Event name _ types) ->
                  knownTopic name types
                Nothing ->
                  case topics of
                    [_, t2, _, _] ->
                      -- check for ds-note logs.. possibly catching false positives
                      -- event LogNote(
                      --     bytes4   indexed  sig,
                      --     address  indexed  usr,
                      --     bytes32  indexed  arg1,
                      --     bytes32  indexed  arg2,
                      --     bytes             data
                      -- ) anonymous;
                      let
                        sig = fromIntegral $ shiftR topic 224 :: Word32
                        usr = case maybeLitWord t2 of
                          Just w ->
                            pack $ show (fromIntegral w :: Addr)
                          Nothing  ->
                            "<symbolic>"
                      in
                        case Map.lookup sig (view dappAbiMap dapp) of
                          Just m ->
                            lognote (view methodSignature m) usr
                          Nothing ->
                            logn
                    _ ->
                      logn
            Nothing ->
              logn

    QueryTrace q ->
      case q of
        PleaseFetchContract addr _ ->
          "fetch contract " <> pack (show addr) <> pos
        PleaseFetchSlot addr slot _ ->
          "fetch storage slot " <> pack (show slot) <> " from " <> pack (show addr) <> pos
        --PleaseAskSMT {} ->
          --"ask smt" <> pos
        --PleaseMakeUnique {} ->
          --"make unique value" <> pos
        PleaseDoFFI cmd _ ->
          "execute ffi " <> pack (show cmd) <> pos

    ErrorTrace e ->
      case e of
        EVM.Revert out ->
          "\x1b[91merror\x1b[0m " <> "Revert " <> showError out <> pos
        _ ->
          "\x1b[91merror\x1b[0m " <> pack (show e) <> pos

    ReturnTrace out (CallContext _ _ _ _ _ (Just abi) _ _ _) ->
      "← " <>
        case Map.lookup (fromIntegral abi) fullAbiMap of
          Just m  ->
            case unzip (view methodOutput m) of
              ([], []) ->
                formatSBinary out
              (_, ts) ->
                showValues ts out
          Nothing ->
            formatSBinary out
    ReturnTrace out (CallContext {}) ->
      "← " <> formatSBinary out
    ReturnTrace out (CreationContext {}) ->
      let l = Expr.bufLength out
      in "← " <> formatExpr l <> " bytes of code"
    EntryTrace t ->
      t
    FrameTrace (CreationContext addr (Lit hash) _ _ ) -> -- FIXME: irrefutable pattern
      "create "
      <> maybeContractName (preview (dappSolcByHash . ix hash . _2) dapp)
      <> "@" <> pack (show addr)
      <> pos
    FrameTrace (CreationContext addr _ _ _ ) ->
      "create "
      <> "<unknown contract>"
      <> "@" <> pack (show addr)
      <> pos
    FrameTrace (CallContext target context _ _ hash abi calldata _ _) ->
      let calltype = if target == context
                     then "call "
                     else "delegatecall "
          Lit hash' = hash -- FIXME: irrefutable pattern, handle symbolic
      in case preview (dappSolcByHash . ix hash' . _2) dapp of
        Nothing ->
          calltype
            <> pack (show target)
            <> pack "::"
            <> case Map.lookup (fromIntegral (fromMaybe 0x00 abi)) fullAbiMap of
                 Just m  ->
                   "\x1b[1m"
                   <> view methodName m
                   <> "\x1b[0m"
                   <> showCall (catMaybes (getAbiTypes (view methodSignature m))) calldata
                 Nothing ->
                   formatSBinary calldata
            <> pos

        Just solc ->
          calltype
            <> "\x1b[1m"
            <> view (contractName . to contractNamePart) solc
            <> "::"
            <> maybe "[fallback function]"
                 (fromMaybe "[unknown method]" . maybeAbiName solc)
                 abi
            <> maybe ("(" <> formatSBinary calldata <> ")")
                 (\x -> showCall (catMaybes x) calldata)
                 (abi >>= fmap getAbiTypes . maybeAbiName solc)
            <> "\x1b[0m"
            <> pos

getAbiTypes :: Text -> [Maybe AbiType]
getAbiTypes abi = map (parseTypeName mempty) types
  where
    types =
      filter (/= "") $
        splitOn "," (dropEnd 1 (last (splitOn "(" abi)))

maybeContractName :: Maybe SolcContract -> Text
maybeContractName =
  maybe "<unknown contract>" (view (contractName . to contractNamePart))

maybeContractName' :: Maybe SolcContract -> Text
maybeContractName' =
  maybe "" (view (contractName . to contractNamePart))

maybeAbiName :: SolcContract -> W256 -> Maybe Text
maybeAbiName solc abi = preview (abiMap . ix (fromIntegral abi) . methodSignature) solc

contractNamePart :: Text -> Text
contractNamePart x = Text.split (== ':') x !! 1

contractPathPart :: Text -> Text
contractPathPart x = Text.split (== ':') x !! 0

prettyvmresult :: (?context :: DappContext) => Expr End -> String
prettyvmresult (EVM.Types.Revert _ (ConcreteBuf "")) = "Revert"
prettyvmresult (EVM.Types.Revert _ msg) = "Revert: " ++ (unpack $ showError msg)
prettyvmresult (EVM.Types.Invalid _) = "Invalid Opcode"
prettyvmresult (EVM.Types.Return _ (ConcreteBuf msg) _) =
  if BS.null msg
  then "Stop"
  else "Return: " <> show (ByteStringS msg)
prettyvmresult (EVM.Types.Return _ _ _) =
  "Return: <symbolic>"
prettyvmresult (EVM.Types.IllegalOverflow _) = "Illegal Overflow"
prettyvmresult (EVM.Types.SelfDestruct _) = "Self Destruct"
prettyvmresult e = error "Internal Error: Invalid Result: " <> show e

currentSolc :: DappInfo -> VM -> Maybe SolcContract
currentSolc dapp vm = undefined
  --let
    --this = vm ^?! EVM.env . EVM.contracts . ix (view (EVM.state . EVM.contract) vm)
    --h = view EVM.codehash this
  --in
    --preview (dappSolcByHash . ix h . _2) dapp

-- TODO: display in an 'act' format

indent :: Int -> Text -> Text
indent n = rstrip . T.unlines . fmap (T.replicate n (T.pack [' ']) <>) . T.lines

rstrip :: Text -> Text
rstrip = T.reverse . T.dropWhile (=='\n') . T.reverse

formatExpr :: Expr a -> Text
formatExpr = go
  where
    go :: Expr a -> Text
    go = \case
      Lit w -> T.pack $ show w
      LitByte w -> T.pack $ show w

      ITE c t f -> rstrip . T.unlines $
        [ "(ITE (" <> formatExpr c <> ")"
        , indent 2 (formatExpr t)
        , indent 2 (formatExpr f)
        , ")"]
      EVM.Types.Revert asserts buf -> case buf of
        ConcreteBuf "" -> "(Revert " <> formatExpr buf <> ")"
        _ -> T.unlines
          [ "(Revert"
          , indent 2 $ T.unlines
            [ "Code:"
            , indent 2 (formatExpr buf)
            , "Assertions:"
            , indent 2 $ T.pack $ show asserts
            ]
          , ")"
          ]
      Return asserts buf store -> T.unlines
        [ "(Return"
        , indent 2 $ T.unlines
          [ "Data:"
          , indent 2 $ formatExpr buf
          , ""
          , "Store:"
          , indent 2 $ formatExpr store
          , "Assertions:"
          , indent 2 $ T.pack $ show asserts
          ]
        , ")"
        ]

      IndexWord idx val -> T.unlines
        [ "(IndexWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "val: "
          , indent 2 $ formatExpr val
          ]
        , ")"
        ]
      ReadWord idx buf -> T.unlines
        [ "(ReadWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "buf: "
          , indent 2 $ formatExpr buf
          ]
        , ")"
        ]

      And a b -> T.unlines
        [ "(And"
        , indent 2 $ T.unlines
          [ formatExpr a
          , formatExpr b
          ]
        , ")"
        ]

      -- Stores
      SLoad addr slot store -> T.unlines
        [ "(SLoad"
        , indent 2 $ T.unlines
          [ "addr:"
          , indent 2 $ formatExpr addr
          , "slot:"
          , indent 2 $ formatExpr slot
          , "store:"
          , indent 2 $ formatExpr store
          ]
        , ")"
        ]
      SStore addr slot val prev -> T.unlines
        [ "(SStore"
        , indent 2 $ T.unlines
          [ "addr:"
          , indent 2 $ formatExpr addr
          , "slot:"
          , indent 2 $ formatExpr slot
          , "val:"
          , indent 2 $ formatExpr val
          ]
        , ")"
        , formatExpr prev
        ]
      ConcreteStore s -> T.unlines
        [ "(ConcreteStore"
        , indent 2 $ T.unlines $ fmap (T.pack . show) $ Map.toList $ fmap (T.pack . show . Map.toList) s
        , ")"
        ]

      -- Buffers

      CopySlice srcOff dstOff size src dst -> T.unlines
        [ "(CopySlice"
        , indent 2 $ T.unlines
          [ "srcOffset: " <> formatExpr srcOff
          , "dstOffset: " <> formatExpr dstOff
          , "size:      " <> formatExpr size
          , "src:"
          , indent 2 $ formatExpr src
          ]
        , ")"
        , formatExpr dst
        ]
      WriteWord idx val buf -> T.unlines
        [ "(WriteWord"
        , indent 2 $ T.unlines
          [ "idx:"
          , indent 2 $ formatExpr idx
          , "val:"
          , indent 2 $ formatExpr val
          ]
        , ")"
        , formatExpr buf
        ]
      WriteByte idx val buf -> T.unlines
        [ "(WriteByte"
        , indent 2 $ T.unlines
          [ "idx: " <> formatExpr idx
          , "val: " <> formatExpr val
          ]
        , ")"
        , formatExpr buf
        ]
      ConcreteBuf bs -> case bs of
        "" -> "(ConcreteBuf \"\")"
        _ -> T.unlines
          [ "(ConcreteBuf"
          , indent 2 $ T.pack $ prettyHex 0 bs
          , ")"
          ]


      -- Hashes
      Keccak b -> T.unlines
       [ "(Keccak"
       , indent 2 $ formatExpr b
       , ")"
       ]

      a -> T.pack $ show a
