{-# Language DataKinds #-}
{-# Language ImplicitParams #-}

module EVM.Format
  ( formatExpr
  , formatSomeExpr
  , formatPartial
  , contractNamePart
  , contractPathPart
  , showError
  , showTree
  , showTraceTree
  , showTraceTree'
  , showValues
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
  , strip0x
  , strip0x'
  , hexByteString
  , hexText
  , bsToHex
  ) where

import Prelude hiding (Word)

import EVM.Types
import EVM (traceForest, traceForest', traceContext)
import EVM.ABI (getAbiSeq, parseTypeName, AbiValue(..), AbiType(..), SolError(..), Indexed(..), Event(..))
import EVM.Dapp (DappContext(..), DappInfo(..), showTraceLocation)
import EVM.Expr qualified as Expr
import EVM.Hexdump (prettyHex, paddedShowHex)
import EVM.Solidity (SolcContract(..), Method(..), contractName, abiMap)

import Control.Arrow ((>>>))
import Optics.Core
import Data.Binary.Get (runGetOrFail)
import Data.Bits (shiftR)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder (byteStringHex, toLazyByteString)
import Data.ByteString.Lazy (toStrict, fromStrict)
import Data.Char qualified as Char
import Data.DoubleWord (signedWord)
import Data.Foldable (toList)
import Data.List (isPrefixOf)
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe (catMaybes, fromMaybe, fromJust)
import Data.Text (Text, pack, unpack, intercalate, dropEnd, splitOn)
import Data.Text qualified as T
import Data.Text.Encoding qualified as T
import Data.Tree.View (showTree)
import Data.Vector (Vector)
import Numeric (showHex)
import Data.ByteString.Char8 qualified as Char8
import Data.ByteString.Base16 qualified as BS16

data Signedness = Signed | Unsigned
  deriving (Show)

showDec :: Signedness -> W256 -> Text
showDec signed (W256 w)
  | (i :: Integer) == 2 ^ (256 :: Integer) - 1 = "MAX_UINT256"
  | otherwise = T.pack (show (i :: Integer))
  where
    i = case signed of
          Signed   -> num (signedWord w)
          Unsigned -> num w

showWordExact :: W256 -> Text
showWordExact w = humanizeInteger (toInteger w)

showWordExplanation :: W256 -> DappInfo -> Text
showWordExplanation w _ | w > 0xffffffff = showDec Unsigned w
showWordExplanation w dapp =
  case Map.lookup (fromIntegral w) dapp.abiMap of
    Nothing -> showDec Unsigned w
    Just x  -> "keccak(\"" <> x.methodSignature <> "\")"

humanizeInteger :: (Num a, Integral a, Show a) => a -> Text
humanizeInteger =
  T.intercalate ","
  . reverse
  . map T.reverse
  . T.chunksOf 3
  . T.reverse
  . T.pack
  . show

prettyIfConcreteWord :: Expr EWord -> Text
prettyIfConcreteWord = \case
  Lit w -> T.pack $ "0x" <> showHex w ""
  w -> T.pack $ show w

showAbiValue :: (?context :: DappContext) => AbiValue -> Text
showAbiValue (AbiString bs) = formatBytes bs
showAbiValue (AbiBytesDynamic bs) = formatBytes bs
showAbiValue (AbiBytes _ bs) = formatBinary bs
showAbiValue (AbiAddress addr) =
  let dappinfo = ?context.info
      contracts = ?context.env
      name = case Map.lookup (LitAddr addr) contracts of
        Nothing -> ""
        Just contract ->
          let hash = maybeLitWord contract.codehash
          in case hash of
               Just h -> maybeContractName' (preview (ix h % _2) dappinfo.solcByHash)
               Nothing -> ""
  in
    name <> "@" <> (pack $ show addr)
showAbiValue v = pack $ show v

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
  let dappinfo = ?context.info
      bs4 = BS.take 4 bs
  in case Map.lookup (word bs4) dappinfo.errorMap of
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
  T.decodeUtf8' >>>
    either
      (const False)
      (T.all (\c-> Char.isPrint c && (not . Char.isControl) c))

formatBytes :: ByteString -> Text
formatBytes b =
  let (s, _) = BS.spanEnd (== 0) b
  in
    if isPrintable s
    then formatBString s
    else formatBinary b

-- a string that came from bytes, displayed with special quotes
formatBString :: ByteString -> Text
formatBString b = mconcat [ "«",  T.dropAround (=='"') (pack $ formatString b), "»" ]

formatBinary :: ByteString -> Text
formatBinary =
  (<>) "0x" . T.decodeUtf8 . toStrict . toLazyByteString . byteStringHex

formatSBinary :: Expr Buf -> Text
formatSBinary (ConcreteBuf bs) = formatBinary bs
formatSBinary (AbstractBuf t) = "<" <> t <> " abstract buf>"
formatSBinary _ = error "formatSBinary: implement me"

showTraceTree :: DappInfo -> VM -> Text
showTraceTree dapp vm =
  let forest = traceForest vm
      traces = fmap (fmap (unpack . showTrace dapp (vm.env.contracts))) forest
  in pack $ concatMap showTree traces

showTraceTree' :: DappInfo -> Expr End -> Text
showTraceTree' _ (ITE {}) = error "Internal Error: ITE does not contain a trace"
showTraceTree' dapp leaf =
  let forest = traceForest' leaf
      traces = fmap (fmap (unpack . showTrace dapp (traceContext leaf))) forest
  in pack $ concatMap showTree traces

unindexed :: [(Text, AbiType, Indexed)] -> [AbiType]
unindexed ts = [t | (_, t, NotIndexed) <- ts]

showTrace :: DappInfo -> Map (Expr EAddr) Contract -> Trace -> Text
showTrace dapp env trace =
  let ?context = DappContext { info = dapp, env = env }
  in let
    pos =
      case showTraceLocation dapp trace of
        Left x -> " \x1b[1m" <> x <> "\x1b[0m"
        Right x -> " \x1b[1m(" <> x <> ")\x1b[0m"
    fullAbiMap = dapp.abiMap
  in case trace.tracedata of
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
              case Map.lookup topic dapp.eventMap of
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
                        sig = fromIntegral $ shiftR topic 224 :: FunctionSelector
                        usr = case maybeLitWord t2 of
                          Just w ->
                            pack $ show (fromIntegral w :: Addr)
                          Nothing  ->
                            "<symbolic>"
                      in
                        case Map.lookup sig dapp.abiMap of
                          Just m ->
                            lognote m.methodSignature usr
                          Nothing ->
                            logn
                    _ ->
                      logn
            Nothing ->
              logn

    ErrorTrace e ->
      case e of
        Revert out ->
          "\x1b[91merror\x1b[0m " <> "Revert " <> showError out <> pos
        _ ->
          "\x1b[91merror\x1b[0m " <> pack (show e) <> pos

    ReturnTrace out (CallContext _ _ _ _ _ (Just abi) _ _ _) ->
      "← " <>
        case Map.lookup (fromIntegral abi) fullAbiMap of
          Just m  ->
            case unzip m.output of
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
      <> maybeContractName (preview (ix hash % _2) dapp.solcByHash)
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
          hash' = fromJust $ maybeLitWord hash
      in case preview (ix hash' % _2) dapp.solcByHash of
        Nothing ->
          calltype
            <> case target of
                 LitAddr 0x7109709ECfa91a80626fF3989D68f67F5b1DD12D -> "HEVM"
                 _ -> pack (show target)
            <> pack "::"
            <> case Map.lookup (fromIntegral (fromMaybe 0x00 abi)) fullAbiMap of
                 Just m  ->
                   "\x1b[1m"
                   <> m.name
                   <> "\x1b[0m"
                   <> showCall (catMaybes (getAbiTypes m.methodSignature)) calldata
                 Nothing ->
                   formatSBinary calldata
            <> pos

        Just solc ->
          calltype
            <> "\x1b[1m"
            <> contractNamePart solc.contractName
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
  maybe "<unknown contract>" (contractNamePart . (.contractName))

maybeContractName' :: Maybe SolcContract -> Text
maybeContractName' =
  maybe "" (contractNamePart . (.contractName))

maybeAbiName :: SolcContract -> W256 -> Maybe Text
maybeAbiName solc abi = Map.lookup (fromIntegral abi) solc.abiMap <&> (.methodSignature)

contractNamePart :: Text -> Text
contractNamePart x = T.split (== ':') x !! 1

contractPathPart :: Text -> Text
contractPathPart x = T.split (== ':') x !! 0

prettyError :: EvmError -> String
prettyError = \case
  IllegalOverflow -> "Illegal overflow"
  SelfDestruction -> "Self destruct"
  StackLimitExceeded -> "Stack limit exceeded"
  InvalidMemoryAccess -> "Invalid memory access"
  BadJumpDestination -> "Bad jump destination"
  StackUnderrun -> "Stack underrun"
  BalanceTooLow a b -> "Balance too low. value: " <> show a <> " balance: " <> show b
  UnrecognizedOpcode a -> "Unrecognized opcode: " <> show a
  Revert (ConcreteBuf msg) -> "Revert: " <> (T.unpack $ formatBinary msg)
  Revert _ -> "Revert: <symbolic>"
  OutOfGas a b -> "Out of gas: have: " <> show a <> " need: " <> show b
  StateChangeWhileStatic -> "State change while static"
  CallDepthLimitReached -> "Call depth limit reached"
  MaxCodeSizeExceeded a b -> "Max code size exceeded: max: " <> show a <> " actual: " <> show b
  MaxInitCodeSizeExceeded a b -> "Max init code size exceeded: max: " <> show a <> " actual: " <> show b
  InvalidFormat -> "Invalid Format"
  PrecompileFailure -> "Precompile failure"
  ReturnDataOutOfBounds -> "Return data out of bounds"
  NonceOverflow -> "Nonce overflow"
  BadCheatCode a -> "Bad cheat code: sig: " <> show a

prettyvmresult :: Expr End -> String
prettyvmresult (Failure _ _ (Revert (ConcreteBuf ""))) = "Revert"
prettyvmresult (Success _ _ (ConcreteBuf msg) _) =
  if BS.null msg
  then "Stop"
  else "Return: " <> show (ByteStringS msg)
prettyvmresult (Success _ _ _ _) =
  "Return: <symbolic>"
prettyvmresult (Failure _ _ err) = prettyError err
prettyvmresult (Partial _ _ p) = T.unpack $ formatPartial p
prettyvmresult r = error $ "Internal Error: Invalid result: " <> show r

indent :: Int -> Text -> Text
indent n = rstrip . T.unlines . fmap (T.replicate n (T.pack [' ']) <>) . T.lines

rstrip :: Text -> Text
rstrip = T.reverse . T.dropWhile (=='\n') . T.reverse

formatError :: EvmError -> Text
formatError = \case
  Revert buf -> T.unlines
    [ "(Revert"
    , indent 2 $ formatExpr buf
    , ")"
    ]
  e -> T.pack $ show e

formatPartial :: PartialExec -> Text
formatPartial = \case
  (UnexpectedSymbolicArg pc msg args) -> T.unlines
    [ "Unexpected Symbolic Arguments to Opcode"
    , indent 2 $ T.unlines
      [ "msg: " <> T.pack (show msg)
      , "program counter: " <> T.pack (show pc)
      , "arguments: "
      , indent 2 $ T.unlines . fmap formatSomeExpr $ args
      ]
    ]
  MaxIterationsReached pc addr -> T.pack $ "Max Iterations Reached in contract: " <> show addr <> " pc: " <> show pc

formatSomeExpr :: SomeExpr -> Text
formatSomeExpr (SomeExpr e) = formatExpr e

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
      Success asserts _ buf store -> T.unlines
        [ "(Return"
        , indent 2 $ T.unlines
          [ "Data:"
          , indent 2 $ formatExpr buf
          , ""
          , "Store:"
          , indent 2 $ T.unlines (fmap (\(a,s) -> (formatExpr a) <> " : " <> (formatExpr s)) (Map.toList store))
          , "Assertions:"
          , indent 2 $ T.pack $ show asserts
          ]
        , ")"
        ]
      Failure asserts _ err -> T.unlines
        [ "(Failure"
        , indent 2 $ T.unlines
          [ "Error:"
          , indent 2 $ formatError err
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
      SLoad slot store -> T.unlines
        [ "(SLoad"
        , indent 2 $ T.unlines
          [ "slot:"
          , indent 2 $ formatExpr slot
          , "store:"
          , indent 2 $ formatExpr store
          ]
        , ")"
        ]
      SStore slot val prev -> T.unlines
        [ "(SStore"
        , indent 2 $ T.unlines
          [ "slot:"
          , indent 2 $ formatExpr slot
          , "val:"
          , indent 2 $ formatExpr val
          ]
        , ")"
        , formatExpr prev
        ]
      ConcreteStore a s -> T.unlines
        [ "(ConcreteStore"
        , indent 2 $ T.unlines
          [ "addr:"
          , indent 2 $ formatExpr a
          , "vals:"
          , indent 2 $ T.unlines $ fmap (T.pack . show) $ Map.toList s
          ]
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

strip0x :: ByteString -> ByteString
strip0x bs = if "0x" `Char8.isPrefixOf` bs then Char8.drop 2 bs else bs

strip0x' :: String -> String
strip0x' s = if "0x" `isPrefixOf` s then drop 2 s else s

hexByteString :: String -> ByteString -> ByteString
hexByteString msg bs =
  case BS16.decodeBase16 bs of
    Right x -> x
    _ -> error ("invalid hex bytestring for " ++ msg)

hexText :: Text -> ByteString
hexText t =
  case BS16.decodeBase16 (T.encodeUtf8 (T.drop 2 t)) of
    Right x -> x
    _ -> error ("invalid hex bytestring " ++ show t)

bsToHex :: ByteString -> String
bsToHex bs = concatMap (paddedShowHex 2) (BS.unpack bs)


