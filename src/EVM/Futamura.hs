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
import Data.List (isPrefixOf, dropWhileEnd, intercalate, foldl', find)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Char (isSpace)
import Data.Map qualified as Map
import Data.IntSet qualified as IntSet
import Data.IntMap.Lazy (IntMap, lookup, fromList)
import Data.Bits (shiftL)
import Prelude hiding (lookup)
import Unsafe.Coerce

import GHC (SuccessFlag(..), compileExpr, mkModuleName, simpleImportDecl, InteractiveImport(..), setContext, LoadHowMuch(..), load, setTargets, guessTarget, setSessionDynFlags, getSessionDynFlags, runGhc)
import GHC.Paths (libdir)
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Driver.Session --(PackageFlag(..), PackageArg(..), ModRenaming(..), PackageDBFlag(..), PkgDbRef(..), xopt_set)
import GHC.Driver.Monad (Ghc)

import EVM.Opcodes (opcodesImpl)
import EVM (currentContract, opslen)
import EVM.Op (getOp, opToWord8)
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

generateHaskellCode :: Map.Map Int BasicBlock -> String
generateHaskellCode cfg =
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
    , "import Data.Word (Word8, Word64)"
    , "import Witch.From (From)"
    , "import Witch (into, tryInto)"
    , "import Data.ByteString qualified as BS"
    , "import Data.Vector qualified as V"
    , ""
    , "import EVM hiding (stackOp2)"
    , "import EVM.Types"
    , "import EVM.Op"
    , "import EVM.Expr qualified as Expr"
    , "import EVM.Effects (defaultConfig, maxDepth)"
    , "import EVM.FeeSchedule (FeeSchedule (..))"
    , "" ]
    ++ map genOpImpl opcodesImpl
    ++ [""]
    ++ map (genBasicBlockImpl cfg) (Map.elems cfg)

-- | Generates a function name for a basic block based on its start PC.
genBasicBlockFuncName :: BasicBlock -> String
genBasicBlockFuncName block = "runBlock_" ++ show (fst block.bbRange)

-- | Generates the Haskell code for a single BasicBlock.
genBasicBlockImpl :: Map.Map Int BasicBlock -> BasicBlock -> String
genBasicBlockImpl cfg block =
  let
    funcName = genBasicBlockFuncName block
    -- Generate a `runOpcode` call for ALL opcodes in the block.
    opCodeStmts = map (("  " ++) . genOp) block.bbOps
    -- Generate the final control-flow transfer statement.
    successorStmt = "  " ++ genSuccessorDispatch cfg block
  in
    unlines $
      [ "{-# INLINE " ++ funcName ++ " #-}",
        funcName ++ " :: StateT (VM Concrete s) (ST s) ()",
        funcName ++ " = do"
      ] ++ opCodeStmts ++ [successorStmt]

-- | Generates the final line of a block function, which dispatches to the next block.
-- This code runs AFTER all opcodes in the block have been executed.
genSuccessorDispatch :: Map.Map Int BasicBlock -> BasicBlock -> String
genSuccessorDispatch cfg block = case block.bbSuccessor of
  -- The last opcode was not a terminator. Directly call the next block's function.
  -- This overrides any PC change from the last opcode.
  FallthroughTo pc   -> if Map.member pc cfg then genBasicBlockFuncName (cfg Map.! pc) else "pure ()"

  -- The JUMP opcode was executed (consuming gas & stack), but we ignore its
  -- effect on the PC and instead make a direct call to the static destination.
  StaticJump pc      -> genBasicBlockFuncName (cfg Map.! pc)

  -- The JUMPI opcode was executed (consuming gas & stack). We then check the
  -- vm.result to see if it failed (e.g., stack underrun). If not, we know
  -- the pc was set to one of two values, but we ignore that and make our own
  -- direct call based on the *original* condition, which is now gone from the stack.
  -- This is a flaw. The logic must be to check the PC set by the JUMPI.
  --
  -- CORRECTED LOGIC: The `runOpcode OpJumpi` has already set the PC to either
  -- the destination or pc+1. We now read that PC and dispatch accordingly.
  ConditionalJump truePc falsePc ->
    unlines
      [ "vm <- get"
      , "  if vm.state.pc == " ++ show truePc
      , "  then " ++ genBasicBlockFuncName (cfg Map.! truePc)
      , "  else " ++ genBasicBlockFuncName (cfg Map.! falsePc)
      ]

  DynamicJump ->
    "error \"JIT Error: Dynamic jumps are not supported.\""

  Terminal ->
    -- The last executed opcode (e.g., runOpcode OpStop) has set vm.result.
    -- There is nothing more to do, the machine has halted.
    "pure ()"

-- | Generates a call to the original `runOpcode` interpreter function.
genOpCall :: GenericOp Word8 -> String
genOpCall op =
  let opcodeByte = opToWord8 op
  in "do { vm <- get; case vm.result of Just _ -> pure (); Nothing -> runOpcode " ++ show opcodeByte ++ " }"

-- | Data Structures for the Control Flow Graph
type BasicBlockRange = (Int, Int)

-- A single node in our Control Flow Graph.
data BasicBlock = BasicBlock
  { bbRange     :: (Int, Int)          -- (start_pc, end_pc_exclusive)
  , bbOps       :: [GenericOp Word8]   -- Opcodes within the block
  , bbSuccessor :: Successor           -- How this block connects to others
  } deriving (Show, Eq)

-- Represents where control flows after a basic block finishes.
data Successor
  = FallthroughTo Int     -- Statically known PC of the next instruction
  | StaticJump Int        -- A JUMP to a constant, known destination PC
  | ConditionalJump Int Int -- A JUMPI to a constant destination and a fallthrough PC
  | DynamicJump           -- A JUMP or JUMPI to an unknown (dynamic) destination
  | Terminal              -- Block ends with STOP, REVERT, RETURN, etc.
  deriving (Show, Eq)

-- A fully decoded instruction with its position and raw data.
data Instruction = Instruction
  { instrPC   :: Int
  , instrOp   :: GenericOp Word8
  , instrData :: BS.ByteString -- The raw bytes for a PUSH, otherwise empty
  } deriving (Show)

-- | Core CFG Construction Logic

-- The main function to build the CFG.
-- Returns a map from a block's starting PC to the BasicBlock itself.
buildCFG :: BS.ByteString -> Map.Map Int BasicBlock
buildCFG bytecode =
  let
    instrs = disassemble bytecode
    leaders = findLeaders instrs
    -- 1. Form the complete CFG for the entire bytecode.
    fullCfg = formBlocks instrs leaders
    -- 2. Filter out the data section at the end.
    filteredCfg = filterDataSection fullCfg
  in
    filteredCfg

-- ... (The rest of your CFG functions: disassemble, findLeaders, formBlocks, etc., remain the same)

-- Disassembles bytecode into a stream of instructions.
disassemble :: BS.ByteString -> [Instruction]
disassemble bs = go 0
  where
    go pc
      | pc >= BS.length bs = []
      | otherwise =
          let opcodeByte = BS.index bs pc
              op = getOp opcodeByte
          in case op of
               OpPush n ->
                 let numBytes = fromIntegral n
                     start = pc + 1
                     end = start + numBytes
                 in if end > BS.length bs then
                      -- This PUSH reads past the end of the bytecode. It's an invalid instruction.
                      let invalidInstr = Instruction pc (OpUnknown opcodeByte) BS.empty
                      in invalidInstr : go (pc + 1)
                    else
                      let pushData = BS.take numBytes (BS.drop start bs)
                          instr = Instruction pc op pushData
                          nextPc = pc + 1 + numBytes
                      in instr : go nextPc
               _ ->
                 let instr = Instruction pc op BS.empty
                     nextPc = pc + 1
                 in instr : go nextPc

-- Finds all "leaders" - instructions that start a basic block.
findLeaders :: [Instruction] -> IntSet.IntSet
findLeaders instrs = IntSet.insert 0 $ fst $ foldl' go (IntSet.empty, False) instrs
  where
    go (leaders, wasTerminator) instr =
      let currentPc = instr.instrPC
          -- If the previous instruction was a terminator, this one is a leader.
          leaders' = if wasTerminator then IntSet.insert currentPc leaders else leaders
          -- If this instruction is a JUMPDEST, it's a leader.
          finalLeaders = if isLeaderOp instr.instrOp then IntSet.insert currentPc leaders' else leaders'
      in (finalLeaders, isTerminatorOp instr.instrOp)

-- Forms a Map of BasicBlocks from the instruction stream and leader set.
formBlocks :: [Instruction] -> IntSet.IntSet -> Map.Map Int BasicBlock
formBlocks [] _ = Map.empty
formBlocks instrs leaders =
  let (blockInstrs, restInstrs) = span (not . isLeaderAfterFirst) (tail instrs)
      firstInstr = head instrs
      -- The first block always starts at PC 0.
      currentBlock = firstInstr : blockInstrs
      startPc = firstInstr.instrPC
      -- The block ends right before the next leader (or at the end of the code).
      endPc = case restInstrs of
                [] -> let lastI = last currentBlock in lastI.instrPC + instructionByteSize lastI
                (nextLeader:_) -> nextLeader.instrPC
      block = BasicBlock
        { bbRange = (startPc, endPc)
        , bbOps = map (.instrOp) currentBlock
        , bbSuccessor = analyzeSuccessor currentBlock
        }
  in Map.insert startPc block (formBlocks restInstrs leaders)
  where
    isLeaderAfterFirst instr = IntSet.member (instr.instrPC) leaders

-- Analyzes the last instruction(s) of a block to find its successor type.
analyzeSuccessor :: [Instruction] -> Successor
analyzeSuccessor instrs =
  case reverse instrs of
    [] -> Terminal -- Should not happen for a non-empty block

    -- JUMP case: Look for a preceding PUSH
    (jumpInstr : pushInstr : _)
      | jumpInstr.instrOp == OpJump, isPush pushInstr.instrOp ->
          let dest = bytesToInteger (BS.unpack pushInstr.instrData)
          in StaticJump (fromInteger dest)

    -- JUMPI case: Look for a preceding PUSH
    (jumpiInstr : pushInstr : _)
      | jumpiInstr.instrOp == OpJumpi, isPush pushInstr.instrOp ->
          let dest = bytesToInteger (BS.unpack pushInstr.instrData)
              -- CORRECTED: Fallthrough is the PC of the instruction *after* the JUMPI
              fallthroughPc = jumpiInstr.instrPC + instructionByteSize jumpiInstr
          in ConditionalJump (fromInteger dest) fallthroughPc

    -- Default cases for dynamic jumps and terminators
    (lastInstr : _) ->
      let op = lastInstr.instrOp
          pc = lastInstr.instrPC
          size = instructionByteSize lastInstr
      in case op of
        OpJump -> DynamicJump
        OpJumpi -> DynamicJump
        _ | isTerminatorOp op -> Terminal
          | otherwise         -> FallthroughTo (pc + size)

-- | Helper Functions

instructionByteSize :: Instruction -> Int
instructionByteSize instr = case instr.instrOp of
  OpPush n -> 1 + fromIntegral n
  _        -> 1

isPush :: GenericOp a -> Bool
isPush (OpPush _) = True
isPush _          = False

bytesToInteger :: [Word8] -> Integer
bytesToInteger = foldl' (\acc byte -> (acc `shiftL` 8) + fromIntegral byte) 0

isLeaderOp :: GenericOp Word8 -> Bool
isLeaderOp OpJumpdest = True
isLeaderOp _         = False

isTerminatorOp :: GenericOp Word8 -> Bool
isTerminatorOp op = case op of
  OpJump         -> True
  OpJumpi        -> True
  OpStop         -> True
  OpRevert       -> True
  OpReturn       -> True
  OpSelfdestruct -> True -- FIX: Was missing
  OpUnknown _    -> True -- FIX: Was missing
  _              -> False


-- | Determines if a basic block is the start of the non-executable data section.
-- According to the pattern, this is a block that starts with an unknown/invalid
-- opcode but is not a simple, single invalid instruction.
isDataSectionBlock :: BasicBlock -> Bool
isDataSectionBlock block =
  case block.bbOps of
    -- An empty block isn't the pattern, but it's good to consider it invalid.
    [] -> True
    -- The key pattern: starts with OpUnknown but has more content.
    (OpUnknown _ : _ : _) -> True
    -- Any other case is a valid executable block.
    _ -> False

-- | Filters the CFG to remove blocks that are part of the contract's metadata section.
-- It finds the first block that looks like a data section marker and removes
-- it and all blocks that come after it.
filterDataSection :: Map.Map Int BasicBlock -> Map.Map Int BasicBlock
filterDataSection cfg =
  -- Find the first block that matches our data section pattern.
  -- `find` on a Map returns the first element in key-order.
  case find isDataSectionBlock (Map.elems cfg) of
    -- No data section block was found; the entire CFG is valid.
    Nothing -> cfg
    -- We found a data section block. Its starting PC is the cutoff point.
    Just invalidBlock ->
      let
        (startPc, _) = invalidBlock.bbRange
        -- `split` divides the map into elements < separator and >= separator.
        -- We just want the part that comes before the invalid block.
        (executableBlocks, _) = Map.split startPc cfg
      in
        executableBlocks

-- | Generate Haskell code for each opcode implementation.

genOpImpl :: (String, String, String, String, Bool) -> String
genOpImpl (opName, opParams, typeSig, src, True) =
  "{-# INLINE runOpcode" ++ opName ++ " #-}\n" ++
  "runOpcode" ++ opName ++ " :: " ++ typeSig ++ "\n" ++
  "runOpcode" ++ opName ++ opParams ++ " = " ++ src ++ "\n"

genOpImpl (opName, opParams, typeSig, src, False) =
  "{-# INLINE " ++ opName ++ " #-}\n" ++
  opName ++ " :: " ++ typeSig ++ "\n" ++
  opName ++ opParams ++ " = " ++ src ++ "\n"

checkIfVmResulted :: String -> String
checkIfVmResulted op =
  " get >>= \\vm ->\n" ++
  "   case vm.result of\n" ++
  "     Nothing ->" ++ op ++ "\n" ++
  "     Just r -> return ()"

genOp :: GenericOp Word8 -> String
genOp (OpPush0)   = "let ?op = 1 in runOpcodePush0"
genOp (OpRevert)  = "let ?op = 1 in runOpcodeRevert"
genOp (OpStop)    = "let ?op = 1 in runOpcodeStop"
genOp (OpAdd)     = "let ?op = 1 in runOpcodeAdd"
genOp (OpDup i)   = "let ?op = 1 in runOpcodeDup (" ++ show i ++ " :: Int)"
genOp (OpSwap i)  = "let ?op = opToWord8(OpSwap " ++ show i ++") in runOpcodeSwap (" ++ show i ++ " :: Int)"
genOp (OpMul)     = "let ?op = opToWord8(OpMul) in runOpcodeMul"
genOp (OpSub)     = "let ?op = opToWord8(OpSub) in runOpcodeSub"
genOp (OpDiv)     = "let ?op = opToWord8(OpDiv) in runOpcodeDiv"
genOp (OpMod)     = "let ?op = opToWord8(OpMod) in runOpcodeMod"
genOp (OpJumpi)    = "let ?op = opToWord8(OpJumpi) in runOpcodeJumpi"
genOp (OpJump)   = "let ?op = opToWord8(OpJump) in runOpcodeJump"
genOp (OpJumpdest) = "let ?op = opToWord8(OpJumpdest) in runOpcodeJumpdest"
genOp (OpPush n)  = "let ?op = opToWord8(OpPush " ++ show n ++ ") in runOpcodePush (" ++ show n ++ " :: Int)"
genOp (OpPop)     = "let ?op = opToWord8(OpPop) in runOpcodePop"
genOp (OpMstore)  = "let ?op = opToWord8(OpMstore) in runOpcodeMStore"
genOp (OpMload)   = "let ?op = opToWord8(OpMload) in runOpcodeMLoad"
genOp (OpSlt)     = "let ?op = opToWord8(OpSlt) in runOpcodeSlt"
genOp (OpIszero)  = "let ?op = opToWord8(OpIszero) in runOpcodeIsZero"
genOp (OpEq)      = "let ?op = opToWord8(OpEq) in runOpcodeEq"
genOp (OpUnknown _) = "let ?op = 1 in runOpcodeRevert" --"error \"Unknown opcode: " ++ show n ++ "\""
-- Add more opcodes as needed
genOp other       = "pure ()" --error $ "Opcode not supported in specialization: " ++ show other

-- | Compile and return a function that runs the specialized VM
--   This function will generate Haskell code based on the current contract's opcodes,
--   compile it using GHC API, and return a function that can be used to run
--   the specialized VM.
--   The generated code will be placed in a temporary directory.
compileAndRunSpecialized :: forall t s. VM t s -> IO (VM t s -> VM t s)
compileAndRunSpecialized vm = do
  tmpDir <- getTemporaryDirectory >>= \tmp -> createTempDirectory tmp "evmjit"
  let contract = currentContract vm
  let bs = case contract of
              Nothing -> error "No current contract found in VM"
              Just c -> extractCode $ c.code

  let cfg = buildCFG bs --filterBasicBlocks $ splitBasicBlocks bs
  putStrLn $ "Splitting into basic blocks: " ++ show cfg
  let hsPath = tmpDir </> "Generated.hs"
  putStrLn $ "Generating Haskell code for EVM specialization in: " ++ hsPath
  writeFile hsPath (generateHaskellCode cfg)

  f <- dynCompileAndRun hsPath "runBlock_0"
  return $ \x -> runST (unsafeCoerce $ execStateT f x)
  where extractCode (RuntimeCode (ConcreteRuntimeCode ops)) = ops
        extractCode _ = error "Expected ConcreteRuntimeCode"

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

dynCompileAndRun :: forall t s. FilePath -> String -> IO (StateT (VM t s) (ST s) ())
dynCompileAndRun filePath startBlockName = runGhc (Just libdir) $ do
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
  -- Compile the file with the GHC API.
  result <- load LoadAllTargets
  case result of
    Failed -> liftIO $ error "Failed to load targets"
    Succeeded -> return ()

  setContext [IIDecl $ simpleImportDecl (mkModuleName "Generated")]
  liftIO $ putStrLn "Compilation successful, returning start function."
  startBlock <- extractBasicBlockFunction startBlockName

  return startBlock

 where
  extractBasicBlockFunction bbName = do
    value <- compileExpr ("Generated." ++ bbName)
    let specialized :: forall s1. StateT (VM t s) (ST s1) ()
        specialized = unsafeCoerce value
    return specialized