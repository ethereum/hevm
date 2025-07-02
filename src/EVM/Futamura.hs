{-# LANGUAGE ImpredicativeTypes #-}

module EVM.Futamura where

import Control.Monad.State.Strict
import Control.Monad.ST
import System.Directory (getTemporaryDirectory)
import System.IO.Temp (createTempDirectory)
import System.FilePath
import System.Process (readProcess)
import Control.Exception (catch, IOException)
import Data.Word (Word8)
import Data.List (isPrefixOf, dropWhileEnd, intercalate)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Char (isSpace)
import Unsafe.Coerce

import GHC (SuccessFlag(..), compileExpr, mkModuleName, simpleImportDecl, InteractiveImport(..), setContext, LoadHowMuch(..), load, setTargets, guessTarget, setSessionDynFlags, getSessionDynFlags, runGhc)
import GHC.Paths (libdir)
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Driver.Session --(PackageFlag(..), PackageArg(..), ModRenaming(..), PackageDBFlag(..), PkgDbRef(..), xopt_set)

import EVM.Opcodes (opcodesImpl)
import EVM (currentContract)
import EVM.Op (getOp)
import EVM.Types (VM, GenericOp(..), ContractCode(..), RuntimeCode(..), contract, code)

import qualified Data.ByteString as BS

-- Code from Halive

-- | Extract the sandbox package db directory from the cabal.sandbox.config file.
--   Exception is thrown if the sandbox config file is broken.
extractKey :: String -> String -> Maybe FilePath
extractKey key conf = extractValue <$> parse conf
  where
    keyLen = length key

    parse = listToMaybe . filter (key `isPrefixOf`) . lines
    extractValue = dropWhileEnd isSpace . dropWhile isSpace . drop keyLen

------------------------
---------- Stack project
------------------------

-- | Get path to the project's snapshot and local package DBs via 'stack path'
getStackDb :: IO (Maybe [FilePath])
getStackDb = do
    pathInfo <- readProcess "stack" ["path"] "" `catch` (\(_e::IOException) -> return [])
    return . Just . catMaybes $ map (flip extractKey pathInfo)
        ["global-pkg-db:", "local-pkg-db:", "snapshot-pkg-db:"]

updateDynFlagsWithStackDB :: MonadIO m => DynFlags -> m DynFlags
updateDynFlagsWithStackDB dflags =
    liftIO getStackDb >>= \case
        Nothing -> error "Failed to get stack package DBs. Ensure you are in a Stack project."
        Just stackDBs -> do
            liftIO $ putStrLn $ "Using Stack package DBs: " ++ show stackDBs
            let pkgs = map (PackageDB . PkgDbPath) stackDBs
            return dflags { packageDBFlags = pkgs ++ packageDBFlags dflags }

--------------------------------------------------------------------------------
-- | Generate Haskell Code From a List of Opcodes
--------------------------------------------------------------------------------

generateHaskellCode :: [(BasicBlockRange, [GenericOp Word8])] -> String
generateHaskellCode bbs =
  unlines $
    [ "{-# LANGUAGE ImplicitParams #-}"
    , "module Generated where"
    , "import Optics.Core"
    , "import Optics.State"
    , "import Optics.State.Operators"
    , "import Optics.Zoom"
    , "import Optics.Operators.Unsafe"
    , ""
    , "import Control.Monad.State.Strict"
    , "import Control.Monad.ST"
    , "import Data.Word (Word8)"
    , "import Witch.From (From)"
    , "import Witch (into)"
    , ""
    , "import EVM"
    , "import EVM.Types"
    , "import EVM.Op"
    , "import EVM.Expr qualified as Expr"
    , "import EVM.FeeSchedule (FeeSchedule (..))"
    , "" ]
    ++ map genOpImpl opcodesImpl
    ++ [""] ++ concatMap genBasicBlockImpl bbs
    -- ++ genBasicBlockList [bb]

--genBasicBlockList :: [(BasicBlockRange, [GenericOp Word8])] -> [String]
--genBasicBlockList [] = []
--genBasicBlockList bbs = [
--   "basicBlocks :: (VMOps t, ?op::Word8) => [((Int, Int), StateT (VM t s) (ST s) ())]",
--   "basicBlocks = [" ++ (intercalate " ," $ map genBasicBlockName bbs) ++ "]"
--  ]

genBasicBlockFuncName :: (BasicBlockRange, [GenericOp Word8]) -> String
genBasicBlockFuncName ((start, end), _) = "runBasicBlock_" ++ show start ++ "_" ++ show end

genBasicBlockImpl :: (BasicBlockRange, [GenericOp Word8]) -> [String]
genBasicBlockImpl bb@(_, ops) =
  let blockFuncName = genBasicBlockFuncName bb
  in [
     blockFuncName ++ " :: StateT (VM Concrete s) (ST s) ()",
     blockFuncName ++ " = do"
     ] ++ map (checkIfVmResulted . genOp) ops

genOpImpl :: (String, String, String, String) -> String
genOpImpl (opName, opParams, typeSig, src) =
  "runOpcode" ++ opName ++ " :: " ++ typeSig ++ "\n" ++
  "runOpcode" ++ opName ++ opParams ++ " = " ++ src ++ "\n"

checkIfVmResulted :: String -> String
checkIfVmResulted op =
  " get >>= \\vm ->\n" ++
  "   case vm.result of\n" ++
  "     Nothing ->" ++ op ++ "\n" ++
  "     Just r -> return ()"

genOp :: GenericOp Word8 -> String
genOp (OpPush0)   = " let ?op = 1 in runOpcodePush0"
genOp (OpRevert)  = " let ?op = 1 in runOpcodeRevert"
genOp (OpStop)    = " let ?op = 1 in runOpcodeStop"
genOp (OpAdd)     = " let ?op = 1 in runOpcodeAdd"
genOp (OpDup i)   = " let ?op = 1 in runOpcodeDup (" ++ show i ++ " :: Int)"
genOp (OpSwap i)  = " let ?op = 1 in runOpcodeSwap (" ++ show i ++ " :: Int)"
-- Add more opcodes as needed
genOp other       = error $ "Opcode not supported in specialization: " ++ show other

-- | Compile and return a function that runs the specialized VM
--   This function will generate Haskell code based on the current contract's opcodes,
--   compile it using GHC API, and return a function that can be used to run
--   the specialized VM.
--   The generated code will be placed in a temporary directory.
compileAndRunSpecialized :: VM t s -> IO (VM t s -> VM t s)
compileAndRunSpecialized vm = do
  tmpDir <- getTemporaryDirectory >>= \tmp -> createTempDirectory tmp "evmjit"
  let contract = currentContract vm
  let ops = case contract of
              Nothing -> error "No current contract found in VM"
              Just c -> map getOp $ BS.unpack $ extractCode $ c.code

  let bb = splitBasicBlocks ops
  putStrLn $ "Splitting into basic blocks: " ++ show bb
  let hsPath = tmpDir </> "Generated.hs"
  putStrLn $ "Generating Haskell code for EVM specialization in: " ++ hsPath
  writeFile hsPath (generateHaskellCode bb)

  let bbFuncNames = map genBasicBlockFuncName bb
  dynCompileAndRun hsPath bbFuncNames
   where extractCode (RuntimeCode (ConcreteRuntimeCode ops)) = ops
         extractCode _ = error "Expected ConcreteRuntimeCode"

type BasicBlockRange = (Int, Int)

-- | Split bytecode into basic blocks with their ranges.
splitBasicBlocks :: [GenericOp Word8] -> [(BasicBlockRange, [GenericOp Word8])]
splitBasicBlocks ops =
  let blocks = splitBasicBlocks' ops
      -- Filter out any empty blocks that might be generated by the splitting logic.
      nonEmptyBlocks = filter (not . null) blocks
      -- Calculate ranges based on the cumulative lengths of the blocks
      lengths = map length nonEmptyBlocks
      starts = scanl (+) 0 lengths
      ranges = zip starts (tail starts)
  in zip ranges nonEmptyBlocks

-- | The core function to split opcodes into a list of basic blocks.
splitBasicBlocks' :: [GenericOp Word8] -> [[GenericOp Word8]]
splitBasicBlocks' [] = []
splitBasicBlocks' ops =
  -- Process the opcodes sequentially, splitting on both leaders and terminators
  let (block, rest) = takeBasicBlock ops
  in block : splitBasicBlocks' rest

-- | Take one basic block from the front of the opcode list
takeBasicBlock :: [GenericOp Word8] -> ([GenericOp Word8], [GenericOp Word8])
takeBasicBlock [] = ([], [])
takeBasicBlock ops =
    if isLeaderOp (head ops)
    then takeBlockStartingWithLeader ops
    else takeBlockWithoutLeader ops

-- | Take a block starting with a leader until a terminator or next leader
takeBlockStartingWithLeader :: [GenericOp Word8] -> ([GenericOp Word8], [GenericOp Word8])
takeBlockStartingWithLeader [] = ([], [])
takeBlockStartingWithLeader (leader:rest) =
    let (block, remaining) = takeUntilTerminatorOrLeader rest
    in ([leader] ++ block, remaining)

-- | Take a block not starting with a leader until a terminator or next leader
takeBlockWithoutLeader :: [GenericOp Word8] -> ([GenericOp Word8], [GenericOp Word8])
takeBlockWithoutLeader ops = takeUntilTerminatorOrLeader ops

-- | Take opcodes until hitting a terminator (inclusive) or leader (exclusive)
takeUntilTerminatorOrLeader :: [GenericOp Word8] -> ([GenericOp Word8], [GenericOp Word8])
takeUntilTerminatorOrLeader [] = ([], [])
takeUntilTerminatorOrLeader (op:rest)
    | isTerminatorOp op = ([op], rest)  -- Include terminator, stop here
    | isLeaderOp op = ([], op:rest)     -- Don't include leader, it starts next block
    | otherwise =
        let (block, remaining) = takeUntilTerminatorOrLeader rest
        in (op:block, remaining)

-- | Identifies opcodes that *start* a new basic block.
isLeaderOp :: GenericOp Word8 -> Bool
isLeaderOp OpJumpdest = True
isLeaderOp _         = False

-- | Identifies opcodes that *end* a basic block.
isTerminatorOp :: GenericOp Word8 -> Bool
isTerminatorOp OpJump   = True
isTerminatorOp OpJumpi  = True
isTerminatorOp OpStop   = True
isTerminatorOp OpRevert = True
isTerminatorOp OpReturn = True
-- Note: Other terminators like SELFDESTRUCT or INVALID could be added here.
isTerminatorOp _        = False

--------------------------------------------------------------------------------
-- | Use GHC API to Compile and Run the Generated Code
--------------------------------------------------------------------------------

neededExtensionFlags :: [Extension]
neededExtensionFlags =
    [ DuplicateRecordFields
    , LambdaCase
    , OverloadedRecordDot
    , OverloadedStrings
    , OverloadedLabels
    , RecordWildCards
    , TypeFamilies
    , ViewPatterns
    , DataKinds
    , ImportQualifiedPost
    , TraditionalRecordSyntax
    , ImplicitParams
    , FlexibleInstances
    , ConstraintKinds
    , DisambiguateRecordFields
    ]

dynCompileAndRun :: forall t s. FilePath -> [String] -> IO (VM t s -> VM t s)
dynCompileAndRun filePath bbNames = runGhc (Just libdir) $ do
  dflags0 <- getSessionDynFlags
  dflags1 <- updateDynFlagsWithStackDB dflags0
  let dflags = foldl xopt_set dflags1 neededExtensionFlags
  _ <- setSessionDynFlags $ updOptLevel 2 $ dflags {
    language = Just GHC2021,
    verbosity = 1,
    debugLevel = 1
  }

  target <- guessTarget filePath Nothing Nothing
  setTargets [target]
  result <- load LoadAllTargets
  case result of
    Failed -> liftIO $ error "Failed to load targets"
    Succeeded -> return ()

  setContext [IIDecl $ simpleImportDecl (mkModuleName "Generated")]

  let firstBlock = head bbNames
  liftIO $ putStrLn $ "Getting basic block: " ++ firstBlock
  value <- compileExpr ("Generated." ++ firstBlock)

  let specialized :: forall s1. StateT (VM t s) (ST s1) ()
      specialized = unsafeCoerce value

  return $ \vm -> runST (execStateT specialized vm)
