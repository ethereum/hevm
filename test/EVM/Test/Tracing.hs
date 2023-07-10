{-# LANGUAGE DataKinds #-}

{-|
Module      : Tracing
Description : Tests to fuzz concrete tracing, and symbolic execution

Functions here are used to generate traces for the concrete
execution of HEVM and check that against evmtool from go-ehereum. Re-using some
of this code, we also generate a symbolic expression then evaluate it
concretely through Expr.simplify, then check that against evmtool's output.
-}
module EVM.Test.Tracing where

import Control.Monad (when)
import Control.Monad.Operational qualified as Operational
import Control.Monad.State.Strict (StateT(..), liftIO, runState)
import Control.Monad.State.Strict qualified as State
import Data.Aeson ((.:), (.:?))
import Data.Aeson qualified as JSON
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Maybe (fromJust, isJust, isNothing)
import Data.Map.Strict qualified as Map
import Data.Text.IO qualified as T
import Data.Vector qualified as Vector
import Data.Word (Word8, Word64)
import GHC.Generics (Generic)
import GHC.IO.Exception (ExitCode(ExitSuccess))
import Numeric (showHex)
import Paths_hevm qualified as Paths
import System.Directory (removeFile)
import System.Process (readProcessWithExitCode)
import Test.QuickCheck (elements)
import Test.QuickCheck.Instances.Text()
import Test.QuickCheck.Instances.Natural()
import Test.QuickCheck.Instances.ByteString()
import Test.Tasty (testGroup, TestTree)
import Test.Tasty.HUnit (assertEqual)
import Test.Tasty.QuickCheck hiding (Failure, Success)
import Witch (into)

import Optics.Core hiding (pre)
import Optics.State
import Optics.Zoom

import EVM (makeVm, initialContract, exec1)
import EVM.Assembler (assemble)
import EVM.Expr qualified as Expr
import EVM.Exec (ethrunAddress)
import EVM.Fetch qualified as Fetch
import EVM.Format (bsToHex, formatBinary)
import EVM.Concrete (createAddress)
import EVM.FeeSchedule qualified as FeeSchedule
import EVM.Op (intToOpName)
import EVM.Sign (deriveAddr)
import EVM.Solvers
import EVM.Stepper qualified as Stepper
import EVM.SymExec
import EVM.Traversals (mapExpr)
import EVM.Transaction qualified
import EVM.Types

data VMTrace =
  VMTrace
  { tracePc      :: Int
  , traceOp      :: Int
  , traceStack   :: [W256]
  , traceMemSize :: Word64
  , traceDepth   :: Int
  , traceGas     :: Word64
  , traceError   :: Maybe String
  } deriving (Generic, Show)

instance JSON.ToJSON VMTrace where
  toEncoding = JSON.genericToEncoding JSON.defaultOptions
instance JSON.FromJSON VMTrace

data VMTraceResult =
  VMTraceResult
  { out  :: ByteStringS
  , gasUsed :: Data.Word.Word64
  } deriving (Generic, Show)

instance JSON.ToJSON VMTraceResult where
  toEncoding = JSON.genericToEncoding JSON.defaultOptions

data EVMToolTrace =
  EVMToolTrace
    { pc :: Int
    , op :: Int
    , gas :: W256
    , memSize :: Integer
    , depth :: Int
    , refund :: Int
    , opName :: String
    , stack :: [W256]
    , error :: Maybe String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolTrace where
  parseJSON = JSON.withObject "EVMToolTrace" $ \v -> EVMToolTrace
    <$> v .: "pc"
    <*> v .: "op"
    <*> v .: "gas"
    <*> v .: "memSize"
    <*> v .: "depth"
    <*> v .: "refund"
    <*> v .: "opName"
    <*> v .: "stack"
    <*> v .:? "error"

mkBlockHash:: Int -> Expr 'EWord
mkBlockHash x = (into x :: Integer) & show & Char8.pack & EVM.Types.keccak' & Lit

blockHashesDefault :: Map.Map Int W256
blockHashesDefault = Map.fromList [(x, forceLit $ mkBlockHash x) | x<- [1..256]]

data EVMToolOutput =
  EVMToolOutput
    { output :: ByteStringS
    , gasUsed :: W256
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolOutput

data EVMToolTraceOutput =
  EVMToolTraceOutput
    { trace :: [EVMToolTrace]
    , output :: EVMToolOutput
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolTraceOutput

data EVMToolEnv = EVMToolEnv
  { coinbase    :: Addr
  , timestamp   :: Expr EWord
  , number      :: W256
  , prevRandao  :: W256
  , gasLimit    :: Data.Word.Word64
  , baseFee     :: W256
  , maxCodeSize :: W256
  , schedule    :: FeeSchedule.FeeSchedule Data.Word.Word64
  , blockHashes :: Map.Map Int W256
  } deriving (Show, Generic)

instance JSON.ToJSON EVMToolEnv where
  toJSON b = JSON.object [ ("currentCoinBase"  , (JSON.toJSON $ b.coinbase))
                         , ("currentDifficulty", (JSON.toJSON $ b.prevRandao))
                         , ("currentGasLimit"  , (JSON.toJSON ("0x" ++ showHex (toInteger $ b.gasLimit) "")))
                         , ("currentNumber"    , (JSON.toJSON $ b.number))
                         , ("currentTimestamp" , (JSON.toJSON tstamp))
                         , ("currentBaseFee"   , (JSON.toJSON $ b.baseFee))
                         , ("blockHashes"      , (JSON.toJSON $ b.blockHashes))
                         ]
              where
                tstamp :: W256
                tstamp = case (b.timestamp) of
                              Lit a -> a
                              _ -> internalError "Timestamp needs to be a Lit"

emptyEvmToolEnv :: EVMToolEnv
emptyEvmToolEnv = EVMToolEnv { coinbase = 0
                             , timestamp = Lit 0
                             , number     = 0
                             , prevRandao = 42069
                             , gasLimit   = 0xffffffffffffffff
                             , baseFee    = 0
                             , maxCodeSize= 0xffffffff
                             , schedule   = FeeSchedule.berlin
                             , blockHashes = mempty
                             }

data EVMToolReceipt =
  EVMToolReceipt
    { _type :: String
    , root :: String
    , status :: String
    , cumulativeGasUsed :: String
    , logsBloom :: String
    , logs :: Maybe String
    , transactionHash :: String
    , contractAddress :: String
    , gasUsed :: String
    , blockHash :: String
    , transactionIndex :: String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMToolReceipt where
    parseJSON = JSON.withObject "EVMReceipt" $ \v -> EVMToolReceipt
        <$> v .: "type"
        <*> v .: "root"
        <*> v .: "status"
        <*> v .: "cumulativeGasUsed"
        <*> v .: "logsBloom"
        <*> v .: "logs"
        <*> v .: "transactionHash"
        <*> v .: "contractAddress"
        <*> v .: "gasUsed"
        <*> v .: "blockHash"
        <*> v .: "transactionIndex"

data EVMToolResult =
  EVMToolResult
  { stateRoot :: String
  , txRoot :: String
  , receiptsRoot :: String
  , logsHash :: String
  , logsBloom :: String
  , receipts :: [EVMToolReceipt]
  , currentDifficulty :: String
  , gasUsed :: String
  , rejected :: Maybe [EVMRejected]
  } deriving (Generic, Show)

instance JSON.FromJSON EVMToolResult

data EVMRejected =
  EVMRejected
    { index :: Int
    , err :: String
    } deriving (Generic, Show)

instance JSON.FromJSON EVMRejected where
  parseJSON = JSON.withObject "EVMRejected" $ \v -> EVMRejected
    <$> v .: "index"
    <*> v .: "error"

data EVMToolAlloc =
  EVMToolAlloc
  { balance :: W256
  , code :: ByteString
  , nonce :: W64
  } deriving (Generic)

instance JSON.ToJSON EVMToolAlloc where
  toJSON b = JSON.object [ ("balance" , (JSON.toJSON $ show b.balance))
                         , ("code", (JSON.toJSON $ ByteStringS b.code))
                         , ("nonce", (JSON.toJSON $ b.nonce))
                         ]

emptyEVMToolAlloc :: EVMToolAlloc
emptyEVMToolAlloc = EVMToolAlloc { balance = 0
                                 , code = mempty
                                 , nonce = 0
                                 }
-- Sets up common parts such as TX, origin contract, and environment that can
-- later be used to create & execute either an evmtool (from go-ethereum) or an
-- HEVM transaction. Some elements here are hard-coded such as the secret key,
-- which are currently not being fuzzed.
evmSetup :: OpContract -> ByteString -> Int -> (EVM.Transaction.Transaction, EVMToolEnv, EVMToolAlloc, Addr, Addr, Integer)
evmSetup contr txData gaslimitExec = (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk)
  where
    contrLits = assemble $ getOpData contr
    toW8fromLitB :: Expr 'Byte -> Word8
    toW8fromLitB (LitByte a) = a
    toW8fromLitB _ = internalError "Cannot convert non-litB"

    bitcode = BS.pack . Vector.toList $ toW8fromLitB <$> contrLits
    contrAlloc = EVMToolAlloc{ balance = 0xa493d65e20984bc
                             , code = bitcode
                             , nonce = 0x48
                             }
    txn = EVM.Transaction.Transaction
      { txdata     = txData
      , gasLimit = fromIntegral gaslimitExec
      , gasPrice = Just 1
      , nonce    = 172
      , toAddr   = Just 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192
      , r        = 0 -- will be fixed when we sign
      , s        = 0 -- will be fixed when we sign
      , v        = 0 -- will be fixed when we sign
      , value    = 0 -- setting this > 0 fails because HEVM doesn't handle value sent in toplevel transaction
      , txtype     = EVM.Transaction.EIP1559Transaction
      , accessList = []
      , maxPriorityFeeGas =  Just 1
      , maxFeePerGas = Just 1
      , chainId = 1
      }
    evmEnv = EVMToolEnv { coinbase   =  0xff
                        , timestamp   =  Lit 0x3e8
                        , number      =  0x0
                        , prevRandao  =  0x0
                        , gasLimit    =  fromIntegral gaslimitExec
                        , baseFee     =  0x0
                        , maxCodeSize =  0xfffff
                        , schedule    =  FeeSchedule.berlin
                        , blockHashes =  blockHashesDefault
                        }
    sk = 0xDC38EE117CAE37750EB1ECC5CFD3DE8E85963B481B93E732C5D0CB66EE6B0C9D
    fromAddress :: Addr
    fromAddress = fromJust $ deriveAddr sk
    toAddress :: Addr
    toAddress = 0x8A8eAFb1cf62BfBeb1741769DAE1a9dd47996192

getHEVMRet :: OpContract -> ByteString -> Int -> IO (Either (EvmError, [VMTrace]) (Expr 'End, [VMTrace], VMTraceResult))
getHEVMRet contr txData gaslimitExec = do
  let (txn, evmEnv, contrAlloc, fromAddress, toAddress, _) = evmSetup contr txData gaslimitExec
  hevmRun <- runCodeWithTrace Nothing evmEnv contrAlloc txn (fromAddress, toAddress)
  return hevmRun

getEVMToolRet :: OpContract -> ByteString -> Int -> IO (Maybe EVMToolResult)
getEVMToolRet contr txData gaslimitExec = do
  let (txn, evmEnv, contrAlloc, fromAddress, toAddress, sk) = evmSetup contr txData gaslimitExec
      txs = [EVM.Transaction.sign sk txn]
      walletAlloc = EVMToolAlloc{ balance = 0x5ffd4878be161d74
                                , code = BS.empty
                                , nonce = 0xac
                                }
      alloc :: Map.Map Addr EVMToolAlloc
      alloc = Map.fromList ([ (fromAddress, walletAlloc), (toAddress, contrAlloc)])
  JSON.encodeFile "txs.json" txs
  JSON.encodeFile "alloc.json" alloc
  JSON.encodeFile "env.json" evmEnv
  (exitCode, evmtoolStdout, evmtoolStderr) <- readProcessWithExitCode "evm" [ "transition"
                               ,"--input.alloc" , "alloc.json"
                               , "--input.env" , "env.json"
                               , "--input.txs" , "txs.json"
                               , "--output.alloc" , "alloc-out.json"
                               , "--trace.returndata=true"
                               , "--trace" , "trace.json"
                               , "--output.result", "result.json"
                               ] ""
  when (exitCode /= ExitSuccess) $ do
    putStrLn $ "evmtool exited with code " <> show exitCode
    putStrLn $ "evmtool stderr output:" <> show evmtoolStderr
    putStrLn $ "evmtool stdout output:" <> show evmtoolStdout
  evmtoolResult <- JSON.decodeFileStrict "result.json" :: IO (Maybe EVMToolResult)
  return evmtoolResult

-- Compares traces of evmtool (from go-ethereum) and HEVM
compareTraces :: [VMTrace] -> [EVMToolTrace] -> IO (Bool)
compareTraces hevmTrace evmTrace = go hevmTrace evmTrace
  where
    go :: [VMTrace] -> [EVMToolTrace] -> IO (Bool)
    go [] [] = pure True
    go (a:ax) (b:bx) = do
      let aOp = a.traceOp
          bOp = b.op
          aPc = a.tracePc
          bPc = b.pc
          aStack = a.traceStack
          bStack = b.stack
          aGas = fromIntegral a.traceGas
          bGas = b.gas
      if aGas /= bGas then do
                          putStrLn "GAS doesn't match:"
                          putStrLn $ "HEVM's gas   : " <> (show aGas)
                          putStrLn $ "evmtool's gas: " <> (show bGas)
                          else
                          -- putStrLn $ "Gas match   : " <> (show aGas)
                          return ()
      if aOp /= bOp || aPc /= bPc then
                          putStrLn $ "HEVM: " <> (intToOpName aOp) <> " (pc " <> (show aPc) <> ") --- evmtool " <> (intToOpName bOp) <> " (pc " <> (show bPc) <> ")"
                          else
                          -- putStrLn $ "trace element match. " <> (intToOpName aOp) <> " pc: " <> (show aPc)
                          return ()

      when (isJust b.error) $ do
        putStrLn $ "Error by evmtool: " <> (show b.error)
        putStrLn $ "Error by HEVM   : " <> (show a.traceError)

      when (aStack /= bStack) $ do
        putStrLn "stacks don't match:"
        putStrLn $ "HEVM's stack   : " <> (show aStack)
        putStrLn $ "evmtool's stack: " <> (show bStack)
      if aOp == bOp && aStack == bStack && aPc == bPc && aGas == bGas then go ax bx
      else pure False


    go a@(_:_) [] = do
      putStrLn $ "Traces don't match. HEVM's trace is longer by:" <> (show a)
      pure False
    go [] [b] = do
      -- evmtool produces ONE more trace element of the error
      -- hevm on the other hand stops and doens't produce one more
      if isJust b.error then pure True
                           else do
                             putStrLn $ "Traces don't match. HEVM's trace is longer by:" <> (show b)
                             pure False
    go [] b@(_:_) = do
      putStrLn $ "Traces don't match. evmtool's trace is longer by:" <> (show b)
      pure False

getTraceFileName :: EVMToolResult -> String
getTraceFileName evmtoolResult = traceFileName
  where
    txName = ((evmtoolResult.receipts) !! 0).transactionHash
    traceFileName = "trace-0-" ++ txName ++ ".jsonl"

getTraceOutput :: Maybe EVMToolResult -> IO (Maybe EVMToolTraceOutput)
getTraceOutput evmtoolResult =
  case evmtoolResult of
    Nothing -> pure Nothing
    Just res -> do
      let traceFileName = getTraceFileName res
      convertPath <- Paths.getDataFileName "test/scripts/convert_trace_to_json.sh"
      (exitcode, _, _) <- readProcessWithExitCode "bash" [convertPath, getTraceFileName res] ""
      case exitcode of
        ExitSuccess -> JSON.decodeFileStrict (traceFileName ++ ".json") :: IO (Maybe EVMToolTraceOutput)
        _ -> pure Nothing

deleteTraceOutputFiles :: Maybe EVMToolResult -> IO ()
deleteTraceOutputFiles evmtoolResult =
  case evmtoolResult of
    Nothing -> return ()
    Just res -> do
      let traceFileName = getTraceFileName res
      System.Directory.removeFile traceFileName
      System.Directory.removeFile (traceFileName ++ ".json")

-- Create symbolic VM from concrete VM
symbolify :: VM -> VM
symbolify vm = vm { state = vm.state { calldata = AbstractBuf "calldata" } }

-- | Takes a runtime code and calls it with the provided calldata
--   Uses evmtool's alloc and transaction to set up the VM correctly
runCodeWithTrace :: Fetch.RpcInfo -> EVMToolEnv -> EVMToolAlloc -> EVM.Transaction.Transaction -> (Addr, Addr) -> IO (Either (EvmError, [VMTrace]) ((Expr 'End, [VMTrace], VMTraceResult)))
runCodeWithTrace rpcinfo evmEnv alloc txn (fromAddr, toAddress) = withSolvers Z3 0 Nothing $ \solvers -> do
  let origVM = vmForRuntimeCode code' calldata' evmEnv alloc txn (fromAddr, toAddress)
      calldata' = ConcreteBuf txn.txdata
      code' = alloc.code
      buildExpr :: SolverGroup -> VM -> IO (Expr End)
      buildExpr s vm = interpret (Fetch.oracle s Nothing) Nothing 1 Naive vm runExpr

  expr <- buildExpr solvers $ symbolify origVM
  (res, (vm, trace)) <- runStateT (interpretWithTrace (Fetch.oracle solvers rpcinfo) Stepper.execFully) (origVM, [])
  case res of
    Left x -> pure $ Left (x, trace)
    Right _ -> pure $ Right (expr, trace, vmres vm)

vmForRuntimeCode :: ByteString -> Expr Buf -> EVMToolEnv -> EVMToolAlloc -> EVM.Transaction.Transaction -> (Addr, Addr) -> VM
vmForRuntimeCode runtimecode calldata' evmToolEnv alloc txn (fromAddr, toAddress) =
  let contr = initialContract (RuntimeCode (ConcreteRuntimeCode runtimecode))
      contrWithBal = (contr :: Contract) { balance = alloc.balance }
  in
  (makeVm $ VMOpts
    { contract = contrWithBal
    , calldata = (calldata', [])
    , value = Lit txn.value
    , initialStorage = EmptyStore
    , address =  toAddress
    , caller = Expr.litAddr fromAddr
    , origin = fromAddr
    , coinbase = evmToolEnv.coinbase
    , number = evmToolEnv.number
    , timestamp = evmToolEnv.timestamp
    , gasprice = fromJust txn.gasPrice
    , gas = txn.gasLimit - fromIntegral (EVM.Transaction.txGasCost evmToolEnv.schedule txn)
    , gaslimit = txn.gasLimit
    , blockGaslimit = evmToolEnv.gasLimit
    , prevRandao = evmToolEnv.prevRandao
    , baseFee = evmToolEnv.baseFee
    , priorityFee = fromJust txn.maxPriorityFeeGas
    , maxCodeSize = evmToolEnv.maxCodeSize
    , schedule = evmToolEnv.schedule
    , chainId = txn.chainId
    , create = False
    , txAccessList = mempty
    , allowFFI = False
    }) & set (#env % #contracts % at ethrunAddress)
             (Just (initialContract (RuntimeCode (ConcreteRuntimeCode BS.empty))))
       & set (#state % #calldata) calldata'

runCode :: Fetch.RpcInfo -> ByteString -> Expr Buf -> IO (Maybe (Expr Buf))
runCode rpcinfo code' calldata' = withSolvers Z3 0 Nothing $ \solvers -> do
  let origVM = vmForRuntimeCode code' calldata' emptyEvmToolEnv emptyEVMToolAlloc EVM.Transaction.emptyTransaction (ethrunAddress, createAddress ethrunAddress 1)
  res <- Stepper.interpret (Fetch.oracle solvers rpcinfo) origVM Stepper.execFully
  pure $ case res of
    Left _ -> Nothing
    Right b -> Just b

vmtrace :: VM -> VMTrace
vmtrace vm =
  let
    memsize = vm.state.memorySize
  in VMTrace { tracePc = vm.state.pc
             , traceOp = into $ getOp vm
             , traceGas = vm.state.gas
             , traceMemSize = memsize
             -- increment to match geth format
             , traceDepth = 1 + length (vm.frames)
             -- reverse to match geth format
             , traceStack = reverse $ forceLit <$> vm.state.stack
             , traceError = readoutError vm.result
             }
  where
    readoutError :: Maybe VMResult -> Maybe String
    readoutError (Just (VMFailure e)) = case e of
      -- NOTE: error text made to closely match go-ethereum's errors.go file
      OutOfGas {}             -> Just "out of gas"
      -- TODO "contract creation code storage out of gas" not handled
      CallDepthLimitReached   -> Just "max call depth exceeded"
      BalanceTooLow {}        -> Just "insufficient balance for transfer"
      -- TODO "contract address collision" not handled
      Revert {}           -> Just "execution reverted"
      -- TODO "max initcode size exceeded" not handled
      MaxCodeSizeExceeded {}  -> Just "max code size exceeded"
      BadJumpDestination  -> Just "invalid jump destination"
      StateChangeWhileStatic  -> Just "write protection"
      ReturnDataOutOfBounds   -> Just "return data out of bounds"
      IllegalOverflow     -> Just "gas uint64 overflow"
      UnrecognizedOpcode op   -> Just $ "invalid opcode: " <> show op
      NonceOverflow       -> Just "nonce uint64 overflow"
      StackUnderrun       -> Just "stack underflow"
      StackLimitExceeded  -> Just "stack limit reached"
      InvalidMemoryAccess -> Just "write protection"
      err                     -> Just $ "HEVM error: " <> show err
    readoutError _ = Nothing

vmres :: VM -> VMTraceResult
vmres vm =
  let
    gasUsed' = vm.tx.gaslimit - vm.state.gas
    res = case vm.result of
      Just (VMSuccess (ConcreteBuf b)) -> (ByteStringS b)
      Just (VMSuccess x) -> internalError $ "unhandled: " <> (show x)
      Just (VMFailure (Revert (ConcreteBuf b))) -> (ByteStringS b)
      Just (VMFailure _) -> ByteStringS mempty
      _ -> ByteStringS mempty
  in VMTraceResult
     { out = res
     , gasUsed = gasUsed'
     }

type TraceState = (VM, [VMTrace])

execWithTrace :: StateT TraceState IO VMResult
execWithTrace = do
  _ <- runWithTrace
  fromJust <$> use (_1 % #result)

runWithTrace :: StateT TraceState IO VM
runWithTrace = do
  -- This is just like `exec` except for every instruction evaluated,
  -- we also increment a counter indexed by the current code location.
  vm0 <- use _1
  case vm0.result of
    Nothing -> do
      State.modify (\(a, b) -> (a, b ++ [vmtrace vm0]))
      zoom _1 (State.state (runState exec1))
      runWithTrace
    Just (VMFailure _) -> do
      -- Update error text for last trace element
      (a, b) <- State.get
      let updatedElem = (last b) {traceError = (vmtrace vm0).traceError}
          updatedTraces = take (length b - 1) b ++ [updatedElem]
      State.put (a, updatedTraces)
      pure vm0
    Just _ -> pure vm0

interpretWithTrace
  :: Fetch.Fetcher
  -> Stepper.Stepper a
  -> StateT TraceState IO a
interpretWithTrace fetcher =
  eval . Operational.view

  where
    eval
      :: Operational.ProgramView Stepper.Action a
      -> StateT TraceState IO a

    eval (Operational.Return x) =
      pure x

    eval (action Operational.:>>= k) =
      case action of
        Stepper.Exec ->
          execWithTrace >>= interpretWithTrace fetcher . k
        Stepper.Run ->
          runWithTrace >>= interpretWithTrace fetcher . k
        Stepper.Wait q -> case q of
          PleaseAskSMT (Lit x) _ continue ->
            interpretWithTrace fetcher (Stepper.evm (continue (Case (x > 0))) >>= k)
          _ -> do
            m <- liftIO (fetcher q)
            zoom _1 (State.state (runState m)) >> interpretWithTrace fetcher (k ())
        Stepper.Ask _ ->
          internalError "cannot make choice in this interpreter"
        Stepper.IOAct q ->
          zoom _1 (StateT (runStateT q)) >>= interpretWithTrace fetcher . k
        Stepper.EVM m ->
          zoom _1 (State.state (runState m)) >>= interpretWithTrace fetcher . k

data OpContract = OpContract [Op]
instance Show OpContract where
  show (OpContract a) = "OpContract " ++ (show a)

getOpData :: OpContract-> [Op]
getOpData (OpContract x) = x

instance Arbitrary OpContract where
  arbitrary = fmap OpContract (sized genContract)

removeExtcalls :: OpContract -> OpContract
removeExtcalls (OpContract ops) = OpContract (filter (noStorageNoExtcalls) ops)
  where
    noStorageNoExtcalls :: Op -> Bool
    noStorageNoExtcalls o = case o of
                               -- Extrenal info functions
                               OpExtcodecopy -> False
                               OpExtcodehash -> False
                               OpExtcodesize -> False
                               OpAddress -> False
                               OpOrigin -> False
                               OpCaller -> False
                               OpCoinbase -> False
                               OpCreate -> False
                               OpCreate2 -> False
                               -- External call functions
                               OpDelegatecall -> False
                               OpStaticcall -> False
                               OpCall -> False
                               OpCallcode -> False
                               -- Not interesting
                               OpBalance -> False
                               OpSelfdestruct -> False
                               _ -> True

getJumpDests :: [Op] -> [Int]
getJumpDests ops = go ops 0 []
    where
      go :: [Op] -> Int -> [Int] -> [Int]
      go [] _ dests = dests
      go (a:ax) pos dests = case a of
                       OpJumpdest -> go ax (pos+1) (pos:dests)
                       OpPush _ -> go ax (pos+33) dests
                       -- We'll fix these up later to add a Push in between, hence they are 34 bytes
                       OpJump -> go ax (pos+34) dests
                       OpJumpi -> go ax (pos+34) dests
                       -- everything else is 1 byte
                       _ -> go ax (pos+1) dests

fixContractJumps :: OpContract -> IO OpContract
fixContractJumps (OpContract ops) = do
  let
    addedOps = ops++[OpJumpdest]
    jumpDests = getJumpDests addedOps
    -- always end on an OpJumpdest so we don't have an issue with a "later" position
    ops2 = fixup addedOps 0 []
    -- original set of operations, the set of jumpDests NOW valid, current position, return value
    fixup :: [Op] -> Int -> [Op] -> IO [Op]
    fixup [] _ ret = pure ret
    fixup (a:ax) pos ret = case a of
      OpJumpi -> do
        let filtDests = (filter (> pos) jumpDests)
        rndPos <- randItem filtDests
        fixup ax (pos+34) (ret++[(OpPush (Lit (fromInteger (fromIntegral rndPos)))), (OpJumpi)])
      OpJump -> do
        let filtDests = (filter (> pos) jumpDests)
        rndPos <- randItem filtDests
        fixup ax (pos+34) (ret++[(OpPush (Lit (fromInteger (fromIntegral rndPos)))), (OpJump)])
      myop@(OpPush _) -> fixup ax (pos+33) (ret++[myop])
      myop -> fixup ax (pos+1) (ret++[myop])
  fmap OpContract ops2

genPush :: Int -> Gen [Op]
genPush n = vectorOf n onePush
  where
    onePush :: Gen Op
    onePush  = do
      p <- chooseInt (1, 10)
      pure $ OpPush (Lit (fromIntegral p))

genContract :: Int -> Gen [Op]
genContract n = do
    y <- chooseInt (3, 6)
    pushes <- genPush y
    normalOps <- vectorOf (3*n+40) genOne
    addReturn <- chooseInt (0, 10)
    let contr = pushes ++ normalOps
    if addReturn < 10 then pure $ contr++[OpPush (Lit 0x40), OpPush (Lit 0x0), OpReturn]
                      else pure contr
  where
    genOne :: Gen Op
    genOne = frequency [
      -- math ops
      (200, frequency [
          (1, pure OpAdd)
        , (1, pure OpMul)
        , (1, pure OpSub)
        , (1, pure OpDiv)
        , (1, pure OpSdiv)
        , (1, pure OpMod)
        , (1, pure OpSmod)
        , (1, pure OpAddmod)
        , (1, pure OpMulmod)
        , (1, pure OpExp)
        , (1, pure OpSignextend)
        , (1, pure OpLt)
        , (1, pure OpGt)
        , (1, pure OpSlt)
        , (1, pure OpSgt)
        , (1, pure OpSha3)
      ])
      -- Comparison & binary ops
      , (200, frequency [
          (1, pure OpEq)
        , (1, pure OpIszero)
        , (1, pure OpAnd)
        , (1, pure OpOr)
        , (1, pure OpXor)
        , (1, pure OpNot)
        , (1, pure OpByte)
        , (1, pure OpShl)
        , (1, pure OpShr)
        , (1, pure OpSar)
      ])
      -- calldata
      , (800, pure OpCalldataload)
      , (200, pure OpCalldatacopy)
      -- Get some info
      , (100, frequency [
          (10, pure OpAddress)
        , (10, pure OpBalance)
        , (10, pure OpOrigin)
        , (10, pure OpCaller)
        , (10, pure OpCallvalue)
        , (10, pure OpCalldatasize)
        , (10, pure OpCodesize)
        , (10, pure OpGasprice)
        , (10, pure OpReturndatasize)
        , (10, pure OpReturndatacopy)
        , (10, pure OpExtcodehash)
        , (10, pure OpBlockhash)
        , (10, pure OpCoinbase)
        , (10, pure OpTimestamp)
        , (10, pure OpNumber)
        , (10, pure OpPrevRandao)
        , (10, pure OpGaslimit)
        , (10, pure OpChainid)
        , (10, pure OpSelfbalance)
        , (10, pure OpBaseFee)
        , (10, pure OpPc)
        , (10, pure OpMsize)
        , (10, pure OpGas)
        , (10, pure OpExtcodesize)
        , (10, pure OpCodecopy)
        , (10, pure OpExtcodecopy)
      ])
      -- memory manip
      , (1200, frequency [
          (50, pure OpMload)
        , (50, pure OpMstore)
        , (1, pure OpMstore8)
      ])
      -- storage manip
      , (100, frequency [
          (1, pure OpSload)
        , (1, pure OpSstore)
      ])
      -- Jumping around
      , (20, frequency [
            (1, pure OpJump)
          , (10, pure OpJumpi)
      ])
      -- calling out
      , (1, frequency [
          (1, pure OpStaticcall)
        , (1, pure OpCall)
        , (1, pure OpCallcode)
        , (1, pure OpDelegatecall)
        , (1, pure OpCreate)
        , (1, pure OpCreate2)
        , (1, pure OpSelfdestruct)
      ])
      -- manipulate stack
      , (13000, frequency [
          (1, pure OpPop)
        , (400, do
            -- x <- arbitrary
            large <- chooseInt (0, 100)
            x <- if large == 0 then chooseBoundedIntegral (0::W256, (2::W256)^(256::W256)-1)
                               else chooseBoundedIntegral (0, 10)
            pure $ OpPush (Lit (fromIntegral x)))
        , (10, do
            x <- chooseInt (1, 10)
            pure $ OpDup (fromIntegral x))
        , (10, do
            x <- chooseInt (1, 10)
            pure $ OpSwap (fromIntegral x))
      ])]
      -- End states
      -- , (1, frequency [
      --    (1, pure OpStop)
      --  , (10, pure OpReturn)
      --  , (10, pure OpRevert)
      -- ])

forceLit :: Expr EWord -> W256
forceLit (Lit x) = x
forceLit _ = undefined

randItem :: [a] -> IO a
randItem = generate . Test.QuickCheck.elements

getOp :: VM -> Word8
getOp vm =
  let pcpos  = vm ^. #state % #pc
      code' = vm ^. #state % #code
      xs = case code' of
        InitCode _ _ -> internalError "InitCode instead of RuntimeCode"
        RuntimeCode (ConcreteRuntimeCode xs') -> BS.drop pcpos xs'
        RuntimeCode (SymbolicRuntimeCode _) -> internalError "RuntimeCode is symbolic"
  in if xs == BS.empty then 0
                       else BS.head xs

tests :: TestTree
tests = testGroup "contract-quickcheck-run"
    [ testProperty "random-contract-concrete-call" $ \(contr :: OpContract) -> ioProperty $ do
        txDataRaw <- generate $ sized $ \n -> vectorOf (10*n+5) $ chooseInt (0,255)
        gaslimitExec <- generate $ chooseInt (40000, 0xffff)
        let txData = BS.pack $ toEnum <$> txDataRaw
        -- TODO: By removing external calls, we fuzz less
        --       It should work also when we external calls. Removing for now.
        contrFixed <- fixContractJumps $ removeExtcalls contr
        evmtoolResult <- getEVMToolRet contrFixed txData gaslimitExec
        hevmRun <- getHEVMRet contrFixed txData gaslimitExec
        (Just evmtoolTraceOutput) <- getTraceOutput evmtoolResult
        case hevmRun of
          (Right (expr, hevmTrace, hevmTraceResult)) -> do
            let
              concretize :: Expr a -> Expr Buf -> Expr a
              concretize a c = mapExpr go a
                where
                  go :: Expr a -> Expr a
                  go = \case
                             AbstractBuf "calldata" -> c
                             y -> y
              concretizedExpr = concretize expr (ConcreteBuf txData)
              simplConcExpr = Expr.simplify concretizedExpr
              getReturnVal :: Expr End -> Maybe ByteString
              getReturnVal (Success _ _ (ConcreteBuf bs) _) = Just bs
              getReturnVal _ = Nothing
              simplConcrExprRetval = getReturnVal simplConcExpr
            traceOK <- compareTraces hevmTrace (evmtoolTraceOutput.trace)
            -- putStrLn $ "HEVM trace   : " <> show hevmTrace
            -- putStrLn $ "evmtool trace: " <> show (evmtoolTraceOutput.toTrace)
            assertEqual "Traces and gas must match" traceOK True
            let resultOK = evmtoolTraceOutput.output.output == hevmTraceResult.out
            if resultOK then do
              putStrLn $ "HEVM & evmtool's outputs match: '" <> (bsToHex $ bssToBs evmtoolTraceOutput.output.output) <> "'"
              if isNothing simplConcrExprRetval || (fromJust simplConcrExprRetval) == (bssToBs hevmTraceResult.out)
                 then do
                   putStr "OK, symbolic interpretation -> concrete calldata -> Expr.simplify gives the same answer."
                   if isNothing simplConcrExprRetval then putStrLn ", but it was a Nothing, so not strong equivalence"
                                                     else putStrLn ""
                 else do
                   putStrLn $ "concretized expr           : " <> (show concretizedExpr)
                   putStrLn $ "simplified concretized expr: " <> (show simplConcExpr)
                   putStrLn $ "return value computed      : " <> (show simplConcrExprRetval)
                   putStrLn $ "evmtool's return value     : " <> (show hevmTraceResult.out)
                   assertEqual "Simplified, concretized expression must match evmtool's output." True False
            else do
              putStrLn $ "Name of trace file: " <> (getTraceFileName $ fromJust evmtoolResult)
              putStrLn $ "HEVM result  :" <> (show hevmTraceResult)
              T.putStrLn $ "HEVM result: " <> (formatBinary $ bssToBs hevmTraceResult.out)
              T.putStrLn $ "evm result : " <> (formatBinary $ bssToBs evmtoolTraceOutput.output.output)
              putStrLn $ "HEVM result len: " <> (show (BS.length $ bssToBs hevmTraceResult.out))
              putStrLn $ "evm result  len: " <> (show (BS.length $ bssToBs evmtoolTraceOutput.output.output))
            assertEqual "Contract exec successful. HEVM & evmtool's outputs must match" resultOK True
          Left (evmerr, hevmTrace) -> do
            putStrLn $ "HEVM contract exec issue: " <> (show evmerr)
            -- putStrLn $ "evmtool result was: " <> show (fromJust evmtoolResult)
            -- putStrLn $ "output by evmtool is: '" <> bsToHex evmtoolTraceOutput.toOutput.output <> "'"
            traceOK <- compareTraces hevmTrace (evmtoolTraceOutput.trace)
            assertEqual "Traces and gas must match" traceOK True
        System.Directory.removeFile "txs.json"
        System.Directory.removeFile "alloc-out.json"
        System.Directory.removeFile "alloc.json"
        System.Directory.removeFile "result.json"
        System.Directory.removeFile "env.json"
        deleteTraceOutputFiles evmtoolResult
    ]
