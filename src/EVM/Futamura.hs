{-# LANGUAGE ImplicitParams, FlexibleContexts, GADTs #-}

module EVM.Futamura where

import Control.Monad.State.Strict
import Control.Monad.ST
import System.Directory (getTemporaryDirectory, doesFileExist)
import System.IO.Temp (createTempDirectory)
import System.FilePath
import System.Process (readProcess)
import Control.Exception (catch, IOException)
import Data.Word (Word8)
import Data.List (isPrefixOf, dropWhileEnd)
import Data.Maybe (catMaybes, listToMaybe)
import Data.Char (isSpace)
import Unsafe.Coerce

import GHC
import GHC.Paths (libdir)
import GHC.LanguageExtensions.Type (Extension(..))
import GHC.Driver.Flags (Language(..))
import GHC.Driver.Session (PackageFlag(..), PackageArg(..), ModRenaming(..), PackageDBFlag(..), PkgDbRef(..), xopt_set)

-- Adjust imports to your project
import EVM.Op
import EVM.Types

projectPackages :: [String]
projectPackages =
  [ "ghc"
  , "ghc-paths"
  , "ghc-boot-th"
  , "directory"
  , "temporary"
  , "system-cxx-std-lib"
  , "QuickCheck"
  , "Decimal"
  , "containers"
  , "transformers"
  , "tree-view"
  , "aeson"
  , "bytestring"
  , "scientific"
  , "binary"
  , "text"
  , "unordered-containers"
  , "vector"
  , "base16"
  , "megaparsec"
  , "mtl"
  , "filepath"
  , "cereal"
  , "cryptonite"
  , "memory"
  , "data-dword"
  , "process"
  , "optics-core"
  , "optics-extra"
  , "optics-th"
  , "aeson-optics"
  , "async"
  , "operational"
  , "optparse-generic"
  , "pretty-hex"
  , "rosezipper"
  , "wreq"
  , "regex-tdfa"
  , "base"
  , "here"
  , "smt2-parser"
  , "spool"
  , "stm"
  , "spawn"
  , "filepattern"
  , "witch"
  , "unliftio-core"
  , "split"
  , "template-haskell"
  , "extra"
  ]

-- Code from Halive

-- | Extract the sandbox package db directory from the cabal.sandbox.config file.
--   Exception is thrown if the sandbox config file is broken.
extractKey :: String -> String -> Maybe FilePath
extractKey key conf = extractValue <$> parse conf
  where
    keyLen = length key

    parse = listToMaybe . filter (key `isPrefixOf`) . lines
    extractValue = dropWhileEnd isSpace . dropWhile isSpace . drop keyLen
-- From ghc-mod
mightExist :: FilePath -> IO (Maybe FilePath)
mightExist f = do
    exists <- doesFileExist f
    return $ if exists then (Just f) else (Nothing)

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

addPackageFlags :: [String] -> DynFlags -> DynFlags
addPackageFlags pkgs df =
    df{packageFlags = packageFlags df ++ expose `map` pkgs}
  where
    expose pkg = ExposePackage pkg (PackageArg pkg) (ModRenaming True [])

addPackageHides :: [String] -> DynFlags -> DynFlags
addPackageHides pkgs df =
    df{packageFlags = packageFlags df ++ hide `map` pkgs}
    where
        hide pkg = HidePackage pkg

--------------------------------------------------------------------------------
-- | Generate Haskell Code From a List of Opcodes
--------------------------------------------------------------------------------

generateHaskellCode :: [GenericOp Word8] -> String
generateHaskellCode ops =
  unlines $
    [ "module Generated where"
    , "import Control.Monad.State.Strict"
    , "import Control.Monad.ST"
    , "import EVM (runOpcodePush0)"
    , "import Data.Word (Word8)"
    , "import EVM.Types"
    , "import EVM.Op"
    , ""
    , "runSpecialized :: StateT (VM Concrete s) (ST s) ()"
    , "runSpecialized = do"
    ] ++ map genOp ops

genOp :: GenericOp Word8 -> String
genOp (OpPush n)  = " let ?op = 1 in runOpcodePush " ++ show n
genOp (OpPush0)   = " let ?op = 1 in runOpcodePush0"
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
    , ImplicitParams
    , FlexibleInstances
    , ConstraintKinds
    , DisambiguateRecordFields
    ]

dynCompileAndRun :: forall t s. FilePath -> VM t s -> IO (VM t s)
dynCompileAndRun filePath vmState = runGhc (Just libdir) $ do
  dflags0 <- getSessionDynFlags
  dflags1 <- updateDynFlagsWithStackDB dflags0
  let dflags2 = foldl xopt_set dflags1 neededExtensionFlags
  let dflags3 = addPackageFlags projectPackages dflags2
  let dflags4 = addPackageHides ["base16-bytestring", "crypton"] dflags3
  _ <- setSessionDynFlags dflags4 { 
    importPaths = importPaths dflags1, -- ++ ["/Users/g/Code/echidna/hevm"], 
    language = Just GHC2021,
    ghcLink   = LinkBinary,      -- Link everything in memory
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
