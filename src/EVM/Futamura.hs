{-# LANGUAGE ImplicitParams, FlexibleContexts, GADTs #-}

module EVM.Futamura where

import Prelude
import Control.Monad.State.Strict
import Control.Monad.ST
import System.Directory (getTemporaryDirectory)
import System.IO.Temp (createTempDirectory)
import System.FilePath
import Data.Word (Word8)
import Unsafe.Coerce

import GHC
import GHC.Paths (libdir)
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Driver.Flags (Language(..))
import GHC.Data.EnumSet (fromList)

-- Adjust imports to your project
import EVM.Op
import EVM.Types

--------------------------------------------------------------------------------
-- | Generate Haskell Code From a List of Opcodes
--------------------------------------------------------------------------------

generateHaskellCode :: [GenericOp Word8] -> String
generateHaskellCode ops =
  unlines $
    [ "module Generated where"
    , "import Prelude"
    , "import Control.Monad.State.Strict"
    , "import Control.Monad.ST"
    , "import EVM (runOpcodePush0)"
    , ""
    , "runSpecialized :: (VMOps t, ?op :: Word8) => StateT (VM t s) (ST s) ()"
    , "runSpecialized = do"
    ] ++ map genOp ops

genOp :: GenericOp Word8 -> String
genOp (OpPush n)  = "  runOpcodePush " ++ show n
genOp (OpPush0)   = "  runOpcodePush0"
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
  putStrLn $ "Generating Haskell code for EVM specialization in: " ++ hsPath
  writeFile hsPath (generateHaskellCode ops)
  dynCompileAndRun hsPath vmState

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
    ]

dynCompileAndRun :: forall t s. FilePath -> VM t s -> IO (VM t s)
dynCompileAndRun filePath vmState = runGhc (Just libdir) $ do
  dflags <- getSessionDynFlags  
  _ <- setSessionDynFlags dflags { importPaths = importPaths dflags ++ ["src", filePath], extensionFlags = fromList neededExtensionFlags, language = Just GHC2021 }

  target <- guessTarget filePath Nothing Nothing
  setTargets [target]
  _ <- load LoadAllTargets

  setContext [IIDecl $ simpleImportDecl (mkModuleName "Generated")]

  value <- compileExpr "Generated.runSpecialized"

  let specialized :: forall s1. StateT (VM t s) (ST s1) ()
      specialized = unsafeCoerce value

  return $ runST (execStateT specialized vmState)
