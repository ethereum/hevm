module EVM.Futamura where

import Control.Monad.State.Strict
import Control.Monad.ST
import System.Directory (getTemporaryDirectory)
import System.IO.Temp (createTempDirectory)
import System.FilePath
import System.Process (readProcess)
import Control.Exception (catch, IOException)
import Data.Word (Word8)
import Data.List (isPrefixOf, dropWhileEnd)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Char (isSpace)
import Unsafe.Coerce

import GHC (SuccessFlag(..), compileExpr, mkModuleName, simpleImportDecl, InteractiveImport(..), setContext, LoadHowMuch(..), load, setTargets, guessTarget, setSessionDynFlags, getSessionDynFlags, runGhc)
import GHC.Paths (libdir)
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Driver.Session --(PackageFlag(..), PackageArg(..), ModRenaming(..), PackageDBFlag(..), PkgDbRef(..), xopt_set)

import EVM.Opcodes
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

generateHaskellCode :: [GenericOp Word8] -> String
generateHaskellCode ops =
  unlines $
    [ "{-# LANGUAGE ImplicitParams #-}"
    , "module Generated where"
    , "import Control.Monad.State.Strict"
    , "import Control.Monad.ST"
    , "import Data.Word (Word8)"
    , "import EVM"
    , "import EVM.Types"
    , "import EVM.Op"
    , "import EVM.Expr qualified as Expr"
    , "import EVM.FeeSchedule (FeeSchedule (..))"
    , ""
    , "runOpcodeAdd :: " ++ runOpcodeAddType
    , "runOpcodeAdd = " ++ runOpcodeAddSrc
    , "runOpcodePush0 ::" ++ runOpcodePush0Type
    , "runOpcodePush0 = " ++ runOpcodePush0Src
    , "runOpcodeStop :: " ++ runOpcodeStopType
    , "runOpcodeStop = " ++ runOpcodeStopSrc
    , "runOpcodeRevert :: " ++ runOpcodeRevertType
    , "runOpcodeRevert = " ++ runOpcodeRevertSrc
    , ""
    , "runSpecialized :: StateT (VM Concrete s) (ST s) ()"
    , "runSpecialized = do"
    ] ++ map (checkIfVmResulted . genOp) ops -- ++ [" doStop"]

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
genOp (OpDup i)   = "  runOpcodeDup " ++ show i
-- Add more opcodes as needed
genOp other       = error $ "Opcode not supported in specialization: " ++ show other

--------------------------------------------------------------------------------
-- | Compile and Run a Specialized EVM Program at Runtime
--------------------------------------------------------------------------------

compileAndRunSpecialized :: VM t s -> IO (VM t s)
compileAndRunSpecialized vm = do
  tmpDir <- getTemporaryDirectory >>= \tmp -> createTempDirectory tmp "evmjit"
  let contract = currentContract vm
  let ops = case contract of
              Nothing -> error "No current contract found in VM"
              Just c -> map getOp $ BS.unpack $ extractCode $ c.code
  let hsPath = tmpDir </> "Generated.hs"
  putStrLn $ "Generating Haskell code for EVM specialization in: " ++ hsPath
  writeFile hsPath (generateHaskellCode ops)
  dynCompileAndRun hsPath vm
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

dynCompileAndRun :: forall t s. FilePath -> VM t s -> IO (VM t s)
dynCompileAndRun filePath vmState = runGhc (Just libdir) $ do
  dflags0 <- getSessionDynFlags
  dflags1 <- updateDynFlagsWithStackDB dflags0
  let dflags = foldl xopt_set dflags1 neededExtensionFlags
  _ <- setSessionDynFlags dflags {
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

  value <- compileExpr "Generated.runSpecialized"

  let specialized :: forall s1. StateT (VM t s) (ST s1) ()
      specialized = unsafeCoerce value

  return $ runST (execStateT specialized vmState)
