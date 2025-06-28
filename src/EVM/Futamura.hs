{-# LANGUAGE ImplicitParams, FlexibleContexts, GADTs #-}

module EVM.Futamura where

import Control.Monad.State.Strict
import Control.Monad.ST
import System.Directory (getTemporaryDirectory)
import System.IO.Temp (createTempDirectory)
import System.FilePath
import Data.Word (Word8)
import GHC
import GHC.Paths (libdir)
import Unsafe.Coerce

-- Adjust imports to your project
import EVM.Op
import EVM.Types

--------------------------------------------------------------------------------
-- | Generate Haskell Code From a List of Opcodes
--------------------------------------------------------------------------------

generateHaskellCode :: [GenericOp Word8] -> String
generateHaskellCode ops =
  unlines $
    [ "{-# LANGUAGE ImplicitParams, FlexibleContexts #-}"
    , "module Generated where"
    , "import Control.Monad.State.Strict"
    , "import Control.Monad.ST"
    , "import EVM"
    , "import EVM.Types"
    , "import EVM.Op"
    , "runSpecialized :: (VMOps t, ?op :: Word8) => StateT (VM t s) (ST s) ()"
    , "runSpecialized = do"
    ] ++ map genOp ops

genOp :: GenericOp Word8 -> String
genOp (OpPush n)  = "  runOpcodePush " ++ show n
genOp (OpAdd)     = "  runOpcodeAdd"
genOp (OpDup i)   = "  runOpcodeDup " ++ show i
-- Add more opcodes as needed
genOp other       = error $ "Opcode not supported in specialization: " ++ show other

--------------------------------------------------------------------------------
-- | Compile and Run a Specialized EVM Program at Runtime
--------------------------------------------------------------------------------

compileAndRunSpecialized :: [GenericOp Word8] -> VM t s -> IO (VM t s)
compileAndRunSpecialized ops vmState = do
  tmpDir <- getTemporaryDirectory >>= \tmp -> createTempDirectory tmp "evmjit"
  let hsPath = tmpDir </> "Generated.hs"
  writeFile hsPath (generateHaskellCode ops)
  dynCompileAndRun hsPath vmState

--------------------------------------------------------------------------------
-- | Use GHC API to Compile and Run the Generated Code
--------------------------------------------------------------------------------

dynCompileAndRun :: forall t s. FilePath -> VM t s -> IO (VM t s)
dynCompileAndRun filePath vmState = runGhc (Just libdir) $ do
  dflags <- getSessionDynFlags
  _ <- setSessionDynFlags dflags

  target <- guessTarget filePath Nothing Nothing
  setTargets [target]
  _ <- load LoadAllTargets

  setContext [IIDecl $ simpleImportDecl (mkModuleName "Generated")]

  value <- compileExpr "Generated.runSpecialized"

  -- Move annotation outside of `let` to avoid scoped type var issue
  let specialized :: forall s1. StateT (VM t s) (ST s1) ()
      specialized = unsafeCoerce value

  -- Wrap runST inside IO to unify the lifetimes of `s1` and `s`
  return $ runST (execStateT specialized vmState)