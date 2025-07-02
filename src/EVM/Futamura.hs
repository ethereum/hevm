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
import GHC.Driver.Monad (Ghc)

import EVM.Opcodes (opcodesImpl)
import EVM (currentContract, opslen)
import EVM.Op (getOp)
import EVM.Types (VM, GenericOp(..), ContractCode(..), RuntimeCode(..), contract, code, result, state, pc, VMResult(..), Expr(ConcreteBuf), EvmError(..))

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
    , "import Witch (into, tryInto)"
    , "import Data.ByteString qualified as BS"
    , "import Data.Vector qualified as V"
    , ""
    , "import EVM"
    , "import EVM.Types"
    , "import EVM.Op"
    , "import EVM.Expr qualified as Expr"
    , "import EVM.Effects (defaultConfig, maxDepth)"
    , "import EVM.FeeSchedule (FeeSchedule (..))"
    , "" ]
    ++ map genOpImpl opcodesImpl
    ++ [""]
    ++ concatMap genBasicBlockImpl bbs

genBasicBlockFuncName :: (BasicBlockRange, [GenericOp Word8]) -> String
genBasicBlockFuncName ((start, end), _) = "runBasicBlock_" ++ show start ++ "_" ++ show end

genBasicBlockImpl :: (BasicBlockRange, [GenericOp Word8]) -> [String]
genBasicBlockImpl bb@(_, ops) =
  let blockFuncName = genBasicBlockFuncName bb
  in [
     blockFuncName ++ " :: StateT (VM Concrete s) (ST s) ()",
     blockFuncName ++ " = do"
     ] ++ map (checkIfVmResulted . genOp) ops

isBasicBlockInvalid :: (BasicBlockRange, [GenericOp Word8]) -> Bool
isBasicBlockInvalid (_, []) = True
isBasicBlockInvalid (_, ((OpUnknown _):ops)) = length ops > 0
isBasicBlockInvalid _ = False

-- | Filter out basic blocks that are empty or contain only unknown opcodes.
-- After it finds a basic block with an unknown opcode, it stops processing further blocks.
filterBasicBlocks :: [(BasicBlockRange, [GenericOp Word8])] -> [(BasicBlockRange, [GenericOp Word8])]
filterBasicBlocks = takeWhile (not . isBasicBlockInvalid)

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
genOp (OpMul)     = " let ?op = 1 in runOpcodeMul"
genOp (OpSub)     = " let ?op = 1 in runOpcodeSub"
genOp (OpDiv)     = " let ?op = 1 in runOpcodeDiv"
genOp (OpMod)     = " let ?op = 1 in runOpcodeMod"
genOp (OpJumpi)    = " let ?op = opToWord8(OpJumpi) in runOpcodeJumpi"
genOp (OpJump)   = " let ?op = opToWord8(OpJump) in runOpcodeJump"
genOp (OpJumpdest) = " let ?op = opToWord8(OpJumpdest) in runOpcodeJumpdest"
genOp (OpPush n)  = " let ?op = opToWord8(OpPush " ++ show n ++ ") in runOpcodePush (" ++ show n ++ " :: Int)"
genOp (OpPop)     = " let ?op = opToWord8(OpPop) in runOpcodePop"
genOp (OpMstore)  = " let ?op = opToWord8(OpMstore) in runOpcodeMStore"
genOp (OpMload)   = " let ?op = opToWord8(OpMload) in runOpcodeMLoad"
genOp (OpSlt)     = " let ?op = opToWord8(OpSlt) in runOpcodeSlt"
genOp (OpIszero)  = " let ?op = opToWord8(OpIszero) in runOpcodeIsZero"
genOp (OpEq)      = " let ?op = opToWord8(OpEq) in runOpcodeEq"
genOp (OpUnknown n) = "error \"Unknown opcode: " ++ show n ++ "\""
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
  let bs = case contract of
              Nothing -> error "No current contract found in VM"
              Just c -> extractCode $ c.code

  let bb = filterBasicBlocks $ splitBasicBlocks bs
  putStrLn $ "Splitting into basic blocks: " ++ show bb
  let hsPath = tmpDir </> "Generated.hs"
  putStrLn $ "Generating Haskell code for EVM specialization in: " ++ hsPath
  writeFile hsPath (generateHaskellCode bb)

  let bbFuncNames = map genBasicBlockFuncName bb
  fs <- dynCompileAndRun hsPath bbFuncNames
  return (\x -> runSpecialized (zip (map fst bb) fs) x)

   where extractCode (RuntimeCode (ConcreteRuntimeCode ops)) = ops
         extractCode _ = error "Expected ConcreteRuntimeCode"

type BasicBlockRange = (Int, Int)

-- | Split bytecode into basic blocks with their ranges, properly disassembling first.
splitBasicBlocks :: BS.ByteString -> [(BasicBlockRange, [GenericOp Word8])]
splitBasicBlocks bytecode =
  let ops = disassemble bytecode
      blocks = splitBasicBlocks' ops
      -- Filter out any empty blocks that might be generated by the splitting logic.
      nonEmptyBlocks = filter (not . null) blocks
      -- Calculate ranges based on the actual byte positions in original bytecode
      ranges = calculateRanges ops nonEmptyBlocks
  in zip ranges nonEmptyBlocks

-- | Disassemble bytecode into a list of opcodes with their byte positions
disassemble :: BS.ByteString -> [(Int, GenericOp Word8)]
disassemble bs = disassemble' (BS.unpack bs) 0
  where
    disassemble' [] _ = []
    disassemble' (b:rest) pos =
      let op = getOp b
          size = opcodeByteSize op
          remaining = drop (size - 1) rest  -- Skip the data bytes for PUSH instructions
      in (pos, op) : disassemble' remaining (pos + size)

-- | Calculate the byte size of an opcode
opcodeByteSize :: GenericOp Word8 -> Int
opcodeByteSize (OpPush n) = fromIntegral n + 1  -- n data bytes + 1 opcode byte
opcodeByteSize _          = 1

-- | Calculate byte ranges for basic blocks in the original bytecode
calculateRanges :: [(Int, GenericOp Word8)] -> [[GenericOp Word8]] -> [BasicBlockRange]
calculateRanges _ blocks =
  let blockSizes = map (sum . map opcodeByteSize) blocks
      starts = scanl (+) 0 blockSizes
  in zip starts (tail starts)

-- | The core function to split opcodes into a list of basic blocks.
splitBasicBlocks' :: [(Int, GenericOp Word8)] -> [[GenericOp Word8]]
splitBasicBlocks' posOps =
  let ops = map snd posOps  -- Extract just the opcodes for splitting logic
  in splitBasicBlocks'' ops

splitBasicBlocks'' :: [GenericOp Word8] -> [[GenericOp Word8]]
splitBasicBlocks'' [] = []
splitBasicBlocks'' ops = let (block, rest) = takeBasicBlock ops
                         in block : splitBasicBlocks'' rest

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

dynCompileAndRun :: forall t s. FilePath -> [String] -> IO [(VM t s -> VM t s)]
dynCompileAndRun filePath bbFuncNames = runGhc (Just libdir) $ do
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

  -- Compile each basic block function
  compiledBlocks <- mapM extractBasicBlockFunction bbFuncNames
  liftIO $ putStrLn "Compilation successful, returning functions."
  return compiledBlocks

 where
  extractBasicBlockFunction bbName = do
    value <- compileExpr ("Generated." ++ bbName)
    let specialized :: forall s1. StateT (VM t s) (ST s1) ()
        specialized = unsafeCoerce value
    return $ \vm -> runST (execStateT specialized vm)

-- | Run the specialized VM for each basic block
--   This function takes a VM and a list of basic blocks with their ranges,
--   and returns a VM that has executed until vm.result is not Nothing.
--   It should use the state.pc to determine which block to run next.
runSpecialized :: [(BasicBlockRange, VM t s -> VM t s)] -> VM t s -> VM t s
runSpecialized bbs vm =
  -- The execution loop continues as long as the VM has not produced a result.
  -- This also serves as the base case for the recursion.
  case vm.result of
    Just _ -> vm
    Nothing ->
      -- Find the compiled function for the basic block at the current program counter.
      -- In the EVM, valid jump destinations must be a JUMPDEST opcode.
      -- Our `splitBasicBlocks` logic ensures that every JUMPDEST starts a new
      -- basic block. Therefore, we can find the correct block by matching
      -- vm.pc with the starting address of a block.
      let
        currentPc = fromIntegral vm.state.pc
        -- We can use `lookup` for an efficient search by converting the list of
        -- blocks into an association list of (startAddress, function).
        blockAssocList = map (\((start, _), f) -> (start, f)) bbs
        maybeBlockFunc = lookup currentPc blockAssocList
      in
        case maybeBlockFunc of
          -- If a matching block is found, execute its compiled function.
          Just blockFunc ->
            -- The `blockFunc` takes the current VM state and returns the new
            -- state after executing the opcodes in that block.
            let newVm = blockFunc vm
            -- Continue execution from the new VM state by making a recursive call.
            in runSpecialized bbs newVm

          -- If no block starts at the current PC, it means we've jumped to an
          -- invalid location (i.e., not a JUMPDEST).
          Nothing -> if (vm.state.pc >= opslen vm.state.code) then
                      error $ "Invalid jump destination: " ++ show vm.state.pc
                      --vm {result = Just (VMSuccess $ ConcreteBuf $ BS.fromString $ show vm.state.pc)}
                     else
                      vm {result = Just (VMFailure $ BadJumpDestination)}
