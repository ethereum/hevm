{-# LANGUAGE PatternSynonyms #-}

-- Converts between Ethereum contract states and simple trees of
-- texts.  Dumps and loads such trees as Git repositories (the state
-- gets serialized as commits with folders and files).
--
-- Example state file hierarchy:
--
--   /0123...abc/balance      says "0x500"
--   /0123...abc/code         says "60023429..."
--   /0123...abc/nonce        says "0x3"
--   /0123...abc/storage/0x1  says "0x1"
--   /0123...abc/storage/0x2  says "0x0"
--
-- This format could easily be serialized into any nested record
-- syntax, e.g. JSON.

module EVM.Facts
  ( File (..)
  , Fact (..)
  , Data (..)
  , Path (..)
  , apply
  , applyCache
  , cacheFacts
  , contractFacts
  , vmFacts
  , factToFile
  , fileToFact
  ) where

import EVM (bytecode)
import EVM qualified
import EVM.Expr (writeStorage, litAddr)
import EVM.Types

import Optics.Core
import Optics.State

import Control.Monad.State.Strict (execState, when)
import Data.ByteString (ByteString)
import Data.ByteString.Base16 qualified as BS16
import Data.ByteString qualified as BS
import Data.ByteString.Char8 qualified as Char8
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Ord (comparing)
import Text.Read (readMaybe)

-- We treat everything as ASCII byte strings because
-- we only use hex digits (and the letter 'x').
type ASCII = ByteString

-- When using string literals, default to infer the ASCII type.
default (ASCII)

-- We use the word "fact" to mean one piece of serializable
-- information about the state.
--
-- Note that Haskell allows this kind of union of records.
-- It's convenient here, but typically avoided.
data Fact
  = BalanceFact { addr :: Addr, what :: W256 }
  | NonceFact   { addr :: Addr, what :: W256 }
  | StorageFact { addr :: Addr, what :: W256, which :: W256 }
  | CodeFact    { addr :: Addr, blob :: ByteString }
  deriving (Eq, Show)

-- A fact path means something like "/0123...abc/storage/0x1",
-- or alternatively "contracts['0123...abc'].storage['0x1']".
data Path = Path [ASCII] ASCII
  deriving (Eq, Ord, Show)

-- A fact data is the content of a file.  We encapsulate it
-- with a newtype to make it easier to change the representation
-- (to use bytestrings, some sum type, or whatever).
newtype Data = Data { dataASCII :: ASCII }
  deriving (Eq, Ord, Show)

-- We use the word "file" to denote a serialized value at a path.
data File = File { filePath :: Path, fileData :: Data }
  deriving (Eq, Ord, Show)

class AsASCII a where
  dump :: a -> ASCII
  load :: ASCII -> Maybe a

instance AsASCII Addr where
  dump = Char8.pack . show
  load = readMaybe . Char8.unpack

instance AsASCII W256 where
  dump = Char8.pack . show
  load = readMaybe . Char8.unpack

instance AsASCII ByteString where
  dump x = BS16.encodeBase16' x <> "\n"
  load x =
    case BS16.decodeBase16 . mconcat . BS.split 10 $ x of
      Right y -> Just y
      _       -> Nothing

contractFacts :: Addr -> Contract -> Map W256 (Map W256 W256) -> [Fact]
contractFacts a x store = case view bytecode x of
  ConcreteBuf b ->
    storageFacts a store ++
    [ BalanceFact a x.balance
    , NonceFact   a x.nonce
    , CodeFact    a b
    ]
  _ ->
    -- here simply ignore storing the bytecode
    storageFacts a store ++
    [ BalanceFact a x.balance
    , NonceFact   a x.nonce
    ]


storageFacts :: Addr -> Map W256 (Map W256 W256) -> [Fact]
storageFacts a store = map f (Map.toList (Map.findWithDefault Map.empty (num a) store))
  where
    f :: (W256, W256) -> Fact
    f (k, v) = StorageFact
      { addr  = a
      , what  = fromIntegral v
      , which = fromIntegral k
      }

cacheFacts :: Cache -> Set Fact
cacheFacts c = Set.fromList $ do
  (k, v) <- Map.toList c.fetchedContracts
  contractFacts k v c.fetchedStorage

vmFacts :: VM -> Set Fact
vmFacts vm = Set.fromList $ do
  (k, v) <- Map.toList vm.env.contracts
  case vm.env.storage of
    EmptyStore -> contractFacts k v Map.empty
    ConcreteStore s -> contractFacts k v s
    _ -> error $ internalError "cannot serialize an abstract store"

-- Somewhat stupidly, this function demands that for each contract,
-- the code fact for that contract comes before the other facts for
-- that contract.  This is an incidental thing because right now we
-- always initialize contracts starting with the code (to calculate
-- the code hash and so on).
--
-- Therefore, we need to make sure to sort the fact set in such a way.
apply1 :: VM -> Fact -> VM
apply1 vm fact =
  case fact of
    CodeFact    {..} -> flip execState vm $ do
      assign (#env % #contracts % at addr) (Just (EVM.initialContract (RuntimeCode (ConcreteRuntimeCode blob))))
      when (vm.state.contract == addr) $ EVM.loadContract addr
    StorageFact {..} ->
      vm & over (#env % #storage) (writeStorage (litAddr addr) (Lit which) (Lit what))
    BalanceFact {..} ->
      vm & set (#env % #contracts % ix addr % #balance) what
    NonceFact   {..} ->
      vm & set (#env % #contracts % ix addr % #nonce) what

apply2 :: VM -> Fact -> VM
apply2 vm fact =
  case fact of
    CodeFact    {..} -> flip execState vm $ do
      assign (#cache % #fetchedContracts % at addr) (Just (EVM.initialContract (RuntimeCode (ConcreteRuntimeCode blob))))
      when (vm.state.contract == addr) $ EVM.loadContract addr
    StorageFact {..} -> let
        store = vm.cache.fetchedStorage
        ctrct = Map.findWithDefault Map.empty (num addr) store
      in
        vm & set (#cache % #fetchedStorage) (Map.insert (num addr) (Map.insert which what ctrct) store)
    BalanceFact {..} ->
      vm & set (#cache % #fetchedContracts % ix addr % #balance) what
    NonceFact   {..} ->
      vm & set (#cache % #fetchedContracts % ix addr % #nonce) what

-- Sort facts in the right order for `apply1` to work.
instance Ord Fact where
  compare = comparing f
    where
    f :: Fact -> (Int, Addr, W256)
    f (CodeFact a _)      = (0, a, 0)
    f (BalanceFact a _)   = (1, a, 0)
    f (NonceFact a _)     = (2, a, 0)
    f (StorageFact a _ x) = (3, a, x)

-- Applies a set of facts to a VM.
apply :: VM -> Set Fact -> VM
apply =
  -- The set's ordering is relevant; see `apply1`.
  foldl apply1
--
-- Applies a set of facts to a VM.
applyCache :: VM -> Set Fact -> VM
applyCache =
  -- The set's ordering is relevant; see `apply1`.
  foldl apply2

factToFile :: Fact -> File
factToFile fact = case fact of
  StorageFact {..} -> mk ["storage"] (dump which) what
  BalanceFact {..} -> mk []          "balance"    what
  NonceFact   {..} -> mk []          "nonce"      what
  CodeFact    {..} -> mk []          "code"       blob
  where
    mk :: AsASCII a => [ASCII] -> ASCII -> a -> File
    mk prefix base a =
      File (Path (dump fact.addr : prefix) base)
           (Data $ dump a)

-- This lets us easier pattern match on serialized things.
-- Uses language extensions: `PatternSynonyms` and `ViewPatterns`.
pattern Load :: AsASCII a => a -> ASCII
pattern Load x <- (load -> Just x)

fileToFact :: File -> Maybe Fact
fileToFact = \case
  File (Path [Load a] "code")    (Data (Load x))
    -> Just (CodeFact a x)
  File (Path [Load a] "balance") (Data (Load x))
    -> Just (BalanceFact a x)
  File (Path [Load a] "nonce")   (Data (Load x))
    -> Just (NonceFact a x)
  File (Path [Load a, "storage"] (Load x)) (Data (Load y))
    -> Just (StorageFact a y x)
  _
    -> Nothing
