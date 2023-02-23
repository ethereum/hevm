{-# Language DataKinds #-}
{-# Language GADTs #-}
{-# Language PolyKinds #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeApplications #-}
{-# Language QuasiQuotes #-}

{- |
    Module: EVM.SMT
    Description: Utilities for building and executing SMT queries from Expr instances
-}
module EVM.SMT where

import Prelude hiding (LT, GT)

import Control.Monad
import Data.Containers.ListUtils (nubOrd)
import Language.SMT2.Parser (getValueRes, parseCommentFreeFileMsg)
import Language.SMT2.Syntax (Symbol, SpecConstant(..), GeneralRes(..), Term(..), QualIdentifier(..), Identifier(..), Sort(..), Index(..), VarBinding(..))
import Data.Word
import Numeric (readHex, readBin)
import Data.ByteString (ByteString)

import qualified Data.ByteString as BS
import qualified Data.List as List
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import Data.String.Here
import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text.Lazy (Text)
import qualified Data.Text as TS
import qualified Data.Text.Lazy as T
import Data.Text.Lazy.Builder
import Data.Bifunctor (second)

import EVM.Types
import EVM.Traversals
import EVM.CSE
import EVM.Keccak
import EVM.Expr hiding (copySlice, writeWord, op1, op2, op3, drop)

-- ** Encoding ** ----------------------------------------------------------------------------------
-- variable names in SMT that we want to get values for
data CexVars = CexVars
  { calldataV :: [Text]
  , buffersV :: [Text]
  , storeReads :: [(Expr EWord, Expr EWord)] -- a list of relevant store reads
  , blockContextV :: [Text]
  , txContextV :: [Text]
  }
  deriving (Eq, Show)

instance Semigroup CexVars where
  (CexVars a b c d e) <> (CexVars a2 b2 c2 d2 e2) = CexVars (a <> a2) (b <> b2) (c <> c2) (d <> d2) (e <> e2)

instance Monoid CexVars where
    mempty = CexVars
      { calldataV = mempty
      , buffersV = mempty
      , storeReads = mempty
      , blockContextV = mempty
      , txContextV = mempty
      }

data SMTCex = SMTCex
  { vars :: Map (Expr EWord) W256
  , buffers :: Map (Expr Buf) ByteString
  , store :: Map W256 (Map W256 W256)
  , blockContext :: Map (Expr EWord) W256
  , txContext :: Map (Expr EWord) W256
  }
  deriving (Eq, Show)

getVar :: EVM.SMT.SMTCex -> TS.Text -> W256
getVar cex name = fromJust $ Map.lookup (Var name) cex.vars

data SMT2 = SMT2 [Builder] CexVars
  deriving (Eq, Show)

instance Semigroup SMT2 where
  (SMT2 a b) <> (SMT2 a2 b2) = SMT2 (a <> a2) (b <> b2)

instance Monoid SMT2 where
  mempty = SMT2 mempty mempty

formatSMT2 :: SMT2 -> Text
formatSMT2 (SMT2 ls _) = T.unlines (fmap toLazyText ls)

-- | Reads all intermediate variables from the builder state and produces SMT declaring them as constants
declareIntermediates :: BufEnv -> StoreEnv -> SMT2
declareIntermediates bufs stores =
  let encSs = Map.mapWithKey encodeStore stores
      encBs = Map.mapWithKey encodeBuf bufs
      sorted = List.sortBy compareFst $ Map.toList $ encSs <> encBs
      decls = fmap snd sorted
  in SMT2 ([fromText "; intermediate buffers & stores"] <> decls) mempty
  where
    compareFst (l, _) (r, _) = compare l r
    encodeBuf n expr =
       fromLazyText ("(define-const buf" <> (T.pack . show $ n) <> " Buf ") <> exprToSMT expr <> ")"
    encodeStore n expr =
       fromLazyText ("(define-const store" <> (T.pack . show $ n) <> " Storage ") <> exprToSMT expr <> ")"

assertProps :: [Prop] -> SMT2
assertProps ps =
  let encs = map propToSMT ps_elim
      intermediates = declareIntermediates bufs stores in
  prelude
  <> (declareBufs . nubOrd $ foldl (<>) [] allBufs)
  <> SMT2 [""] mempty
  <> (declareVars . nubOrd $ foldl (<>) [] allVars)
  <> SMT2 [""] mempty
  <> (declareFrameContext . nubOrd $ foldl (<>) [] frameCtx)
  <> SMT2 [""] mempty
  <> (declareBlockContext . nubOrd $ foldl (<>) [] blockCtx)
  <> SMT2 [""] mempty
  <> intermediates
  <> SMT2 [""] mempty
  <> keccakAssumes
  <> readAssumes
  <> SMT2 [""] mempty
  <> SMT2 (fmap (\p -> "(assert " <> p <> ")") encs) mempty
  <> SMT2 [] mempty{storeReads = storageReads}

  where
    (ps_elim, bufs, stores) = eliminateProps ps

    allBufs = fmap referencedBufs' ps_elim <> fmap referencedBufs bufVals <> fmap referencedBufs storeVals
    allVars = fmap referencedVars' ps_elim <> fmap referencedVars bufVals <> fmap referencedVars storeVals
    frameCtx = fmap referencedFrameContext' ps_elim <> fmap referencedFrameContext bufVals <> fmap referencedFrameContext storeVals
    blockCtx = fmap referencedBlockContext' ps_elim <> fmap referencedBlockContext bufVals <> fmap referencedBlockContext storeVals

    bufVals = Map.elems bufs
    storeVals = Map.elems stores

    storageReads = nubOrd $ concatMap findStorageReads ps

    keccakAssumes
      = SMT2 ["; keccak assumptions"] mempty
      <> SMT2 (fmap (\p -> "(assert " <> propToSMT p <> ")") (keccakAssumptions ps_elim bufVals storeVals)) mempty

    readAssumes
      = SMT2 ["; read assumptions"] mempty
        <> SMT2 (fmap (\p -> "(assert " <> propToSMT p <> ")") (assertReads ps_elim bufs stores)) mempty


referencedBufsGo :: Expr a -> [Builder]
referencedBufsGo = \case
  AbstractBuf s -> [fromText s]
  _ -> []

referencedBufs :: Expr a -> [Builder]
referencedBufs expr = nubOrd $ foldExpr referencedBufsGo [] expr

referencedBufs' :: Prop -> [Builder]
referencedBufs' prop = nubOrd $ foldProp referencedBufsGo [] prop


referencedVarsGo :: Expr a -> [Builder]
referencedVarsGo = \case
  Var s -> [fromText s]
  _ -> []

referencedVars :: Expr a -> [Builder]
referencedVars expr = nubOrd $ foldExpr referencedVarsGo [] expr

referencedVars' :: Prop -> [Builder]
referencedVars' prop = nubOrd $ foldProp referencedVarsGo [] prop


referencedFrameContextGo :: Expr a -> [Builder]
referencedFrameContextGo = \case
  CallValue a -> [fromLazyText $ T.append "callvalue_" (T.pack . show $ a)]
  Caller a -> [fromLazyText $ T.append "caller_" (T.pack . show $ a)]
  Address a -> [fromLazyText $ T.append "address_" (T.pack . show $ a)]
  Balance {} -> error "TODO: BALANCE"
  SelfBalance {} -> error "TODO: SELFBALANCE"
  Gas {} -> error "TODO: GAS"
  _ -> []

referencedFrameContext :: Expr a -> [Builder]
referencedFrameContext expr = nubOrd $ foldExpr referencedFrameContextGo [] expr

referencedFrameContext' :: Prop -> [Builder]
referencedFrameContext' prop = nubOrd $ foldProp referencedFrameContextGo [] prop


referencedBlockContextGo :: Expr a -> [Builder]
referencedBlockContextGo = \case
  Origin -> ["origin"]
  Coinbase -> ["coinbase"]
  Timestamp -> ["timestamp"]
  BlockNumber -> ["blocknumber"]
  PrevRandao -> ["prevrandao"]
  GasLimit -> ["gaslimit"]
  ChainId -> ["chainid"]
  BaseFee -> ["basefee"]
  _ -> []

referencedBlockContext :: Expr a -> [Builder]
referencedBlockContext expr = nubOrd $ foldExpr referencedBlockContextGo [] expr

referencedBlockContext' :: Prop -> [Builder]
referencedBlockContext' prop = nubOrd $ foldProp referencedBlockContextGo [] prop

-- | This function overapproximates the reads from the abstract
-- storage. Potentially, it can return locations that do not read a
-- slot directly from the abstract store but from subsequent writes on
-- the store (e.g, SLoad addr idx (SStore addr idx val AbstractStore)).
-- However, we expect that most of such reads will have been
-- simplified away.
findStorageReads :: Prop -> [(Expr EWord, Expr EWord)]
findStorageReads = foldProp go []
  where
    go :: Expr a -> [(Expr EWord, Expr EWord)]
    go = \case
      SLoad addr slot storage -> [(addr, slot) | containsNode isAbstractStore storage]
      _ -> []

    isAbstractStore AbstractStore = True
    isAbstractStore _ = False


findBufferAccess :: TraversableTerm a => [a] -> [(Expr EWord, Expr EWord, Expr Buf)]
findBufferAccess = foldl (\acc p -> foldTerm go acc p) mempty
  where
    go :: Expr a -> [(Expr EWord, Expr EWord, Expr Buf)]
    go = \case
      ReadWord idx buf -> [(idx, Lit 32, buf)]
      ReadByte idx buf -> [(idx, Lit 1, buf)]
      CopySlice srcOff _ size src _  -> [(srcOff, size, src)]
      _ -> mempty


-- | Asserts that buffer reads beyond the size of the buffer are equal
-- to zero. Looks for buffer reads in the a list of given predicates
-- and the buffer and storage environments.
assertReads :: [Prop] -> BufEnv -> StoreEnv -> [Prop]
assertReads props benv senv = concat $ fmap assertRead allReads
  where
    assertRead :: (Expr EWord, Expr EWord, Expr Buf) -> [Prop]
    assertRead (idx, Lit 32, buf) = [PImpl (PGEq idx (bufLength buf)) (PEq (ReadWord idx buf) (Lit 0))]
    assertRead (idx, Lit sz, buf) = fmap (\s -> PImpl (PGEq idx (bufLength buf)) (PEq (ReadByte idx buf) (LitByte (num s)))) [(0::Int)..num sz-1]
    assertRead (_, _, _) = error "Cannot generate assertions for accesses of symbolic size"

    allReads = filter keepRead $ nubOrd $ findBufferAccess props <> findBufferAccess (Map.elems benv) <> findBufferAccess (Map.elems senv)

    -- discard constraints if we can statically determine that read is less than the buffer length
    keepRead (Lit idx, Lit size, buf) =
      case minLength benv buf of
        Just l | num (idx + size) <= l -> False
        _ -> True
    keepRead _ = True


declareBufs :: [Builder] -> SMT2
declareBufs names = SMT2 ("; buffers" : fmap declareBuf names <> ("; buffer lengths" : fmap declareLength names)) cexvars
  where
    declareBuf n = "(declare-const " <> n <> " (Array (_ BitVec 256) (_ BitVec 8)))"
    declareLength n = "(define-const " <> n <> "_length" <> " (_ BitVec 256) (bufLength " <> n <> "))"
    cexvars = mempty{buffersV = fmap toLazyText names}


-- Given a list of 256b VM variable names, create an SMT2 object with the variables declared
declareVars :: [Builder] -> SMT2
declareVars names = SMT2 (["; variables"] <> fmap declare names) cexvars
  where
    declare n = "(declare-const " <> n <> " (_ BitVec 256))"
    cexvars = mempty{calldataV = fmap toLazyText names}


declareFrameContext :: [Builder] -> SMT2
declareFrameContext names = SMT2 (["; frame context"] <> fmap declare names) cexvars
  where
    declare n = "(declare-const " <> n <> " (_ BitVec 256))"
    cexvars = mempty{txContextV = fmap toLazyText names}


declareBlockContext :: [Builder] -> SMT2
declareBlockContext names = SMT2 (["; block context"] <> fmap declare names) cexvars
  where
    declare n = "(declare-const " <> n <> " (_ BitVec 256))"
    cexvars = mempty{blockContextV = fmap toLazyText names}


prelude :: SMT2
prelude =  (flip SMT2) mempty $ fmap (fromLazyText . T.drop 2) . T.lines $ [i|
  ; logic
  ; TODO: this creates an error when used with z3?
  ;(set-logic QF_AUFBV)
  (set-logic ALL)

  ; types
  (define-sort Byte () (_ BitVec 8))
  (define-sort Word () (_ BitVec 256))
  (define-sort Buf () (Array Word Byte))

  ; address -> slot -> value
  (define-sort Storage () (Array Word (Array Word Word)))

  ; hash functions
  (declare-fun keccak (Buf) Word)
  (declare-fun sha256 (Buf) Word)

  ; word indexing
  (define-fun indexWord31 ((w Word)) Byte ((_ extract 7 0) w))
  (define-fun indexWord30 ((w Word)) Byte ((_ extract 15 8) w))
  (define-fun indexWord29 ((w Word)) Byte ((_ extract 23 16) w))
  (define-fun indexWord28 ((w Word)) Byte ((_ extract 31 24) w))
  (define-fun indexWord27 ((w Word)) Byte ((_ extract 39 32) w))
  (define-fun indexWord26 ((w Word)) Byte ((_ extract 47 40) w))
  (define-fun indexWord25 ((w Word)) Byte ((_ extract 55 48) w))
  (define-fun indexWord24 ((w Word)) Byte ((_ extract 63 56) w))
  (define-fun indexWord23 ((w Word)) Byte ((_ extract 71 64) w))
  (define-fun indexWord22 ((w Word)) Byte ((_ extract 79 72) w))
  (define-fun indexWord21 ((w Word)) Byte ((_ extract 87 80) w))
  (define-fun indexWord20 ((w Word)) Byte ((_ extract 95 88) w))
  (define-fun indexWord19 ((w Word)) Byte ((_ extract 103 96) w))
  (define-fun indexWord18 ((w Word)) Byte ((_ extract 111 104) w))
  (define-fun indexWord17 ((w Word)) Byte ((_ extract 119 112) w))
  (define-fun indexWord16 ((w Word)) Byte ((_ extract 127 120) w))
  (define-fun indexWord15 ((w Word)) Byte ((_ extract 135 128) w))
  (define-fun indexWord14 ((w Word)) Byte ((_ extract 143 136) w))
  (define-fun indexWord13 ((w Word)) Byte ((_ extract 151 144) w))
  (define-fun indexWord12 ((w Word)) Byte ((_ extract 159 152) w))
  (define-fun indexWord11 ((w Word)) Byte ((_ extract 167 160) w))
  (define-fun indexWord10 ((w Word)) Byte ((_ extract 175 168) w))
  (define-fun indexWord9 ((w Word)) Byte ((_ extract 183 176) w))
  (define-fun indexWord8 ((w Word)) Byte ((_ extract 191 184) w))
  (define-fun indexWord7 ((w Word)) Byte ((_ extract 199 192) w))
  (define-fun indexWord6 ((w Word)) Byte ((_ extract 207 200) w))
  (define-fun indexWord5 ((w Word)) Byte ((_ extract 215 208) w))
  (define-fun indexWord4 ((w Word)) Byte ((_ extract 223 216) w))
  (define-fun indexWord3 ((w Word)) Byte ((_ extract 231 224) w))
  (define-fun indexWord2 ((w Word)) Byte ((_ extract 239 232) w))
  (define-fun indexWord1 ((w Word)) Byte ((_ extract 247 240) w))
  (define-fun indexWord0 ((w Word)) Byte ((_ extract 255 248) w))

  ; symbolic word indexing
  ; a bitshift based version might be more performant here...
  (define-fun indexWord ((idx Word) (w Word)) Byte
    (ite (bvuge idx (_ bv32 256)) (_ bv0 8)
    (ite (= idx (_ bv31 256)) (indexWord31 w)
    (ite (= idx (_ bv30 256)) (indexWord30 w)
    (ite (= idx (_ bv29 256)) (indexWord29 w)
    (ite (= idx (_ bv28 256)) (indexWord28 w)
    (ite (= idx (_ bv27 256)) (indexWord27 w)
    (ite (= idx (_ bv26 256)) (indexWord26 w)
    (ite (= idx (_ bv25 256)) (indexWord25 w)
    (ite (= idx (_ bv24 256)) (indexWord24 w)
    (ite (= idx (_ bv23 256)) (indexWord23 w)
    (ite (= idx (_ bv22 256)) (indexWord22 w)
    (ite (= idx (_ bv21 256)) (indexWord21 w)
    (ite (= idx (_ bv20 256)) (indexWord20 w)
    (ite (= idx (_ bv19 256)) (indexWord19 w)
    (ite (= idx (_ bv18 256)) (indexWord18 w)
    (ite (= idx (_ bv17 256)) (indexWord17 w)
    (ite (= idx (_ bv16 256)) (indexWord16 w)
    (ite (= idx (_ bv15 256)) (indexWord15 w)
    (ite (= idx (_ bv14 256)) (indexWord14 w)
    (ite (= idx (_ bv13 256)) (indexWord13 w)
    (ite (= idx (_ bv12 256)) (indexWord12 w)
    (ite (= idx (_ bv11 256)) (indexWord11 w)
    (ite (= idx (_ bv10 256)) (indexWord10 w)
    (ite (= idx (_ bv9 256)) (indexWord9 w)
    (ite (= idx (_ bv8 256)) (indexWord8 w)
    (ite (= idx (_ bv7 256)) (indexWord7 w)
    (ite (= idx (_ bv6 256)) (indexWord6 w)
    (ite (= idx (_ bv5 256)) (indexWord5 w)
    (ite (= idx (_ bv4 256)) (indexWord4 w)
    (ite (= idx (_ bv3 256)) (indexWord3 w)
    (ite (= idx (_ bv2 256)) (indexWord2 w)
    (ite (= idx (_ bv1 256)) (indexWord1 w)
    (indexWord0 w)
    ))))))))))))))))))))))))))))))))
  )

  ; buffers
  (declare-fun bufLength (Buf) Word)
  (define-const emptyBuf Buf ((as const Buf) #b00000000))

  (define-fun readWord ((idx Word) (buf Buf)) Word
    (concat
      (select buf idx)
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018))
      (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f))
    )
  )

  (define-fun writeWord ((idx Word) (val Word) (buf Buf)) Buf
      (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store
      (store (store (store (store (store (store (store (store (store (store (store (store (store (store (store buf
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f) (indexWord31 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e) (indexWord30 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d) (indexWord29 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c) (indexWord28 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b) (indexWord27 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a) (indexWord26 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019) (indexWord25 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018) (indexWord24 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017) (indexWord23 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016) (indexWord22 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015) (indexWord21 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014) (indexWord20 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013) (indexWord19 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012) (indexWord18 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011) (indexWord17 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010) (indexWord16 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f) (indexWord15 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e) (indexWord14 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d) (indexWord13 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c) (indexWord12 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b) (indexWord11 val))
      (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a) (indexWord10 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009) (indexWord9 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008) (indexWord8 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007) (indexWord7 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006) (indexWord6 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005) (indexWord5 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004) (indexWord4 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003) (indexWord3 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002) (indexWord2 val))
      (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001) (indexWord1 val))
      idx (indexWord0 val))
  )

  ; block context
  (declare-fun blockhash (Word) Word)

  ; macros
  (define-fun signext ( (b Word) (val Word)) Word
    (ite (= b (_ bv0  256)) ((_ sign_extend 248) ((_ extract 7    0) val))
    (ite (= b (_ bv1  256)) ((_ sign_extend 240) ((_ extract 15   0) val))
    (ite (= b (_ bv2  256)) ((_ sign_extend 232) ((_ extract 23   0) val))
    (ite (= b (_ bv3  256)) ((_ sign_extend 224) ((_ extract 31   0) val))
    (ite (= b (_ bv4  256)) ((_ sign_extend 216) ((_ extract 39   0) val))
    (ite (= b (_ bv5  256)) ((_ sign_extend 208) ((_ extract 47   0) val))
    (ite (= b (_ bv6  256)) ((_ sign_extend 200) ((_ extract 55   0) val))
    (ite (= b (_ bv7  256)) ((_ sign_extend 192) ((_ extract 63   0) val))
    (ite (= b (_ bv8  256)) ((_ sign_extend 184) ((_ extract 71   0) val))
    (ite (= b (_ bv9  256)) ((_ sign_extend 176) ((_ extract 79   0) val))
    (ite (= b (_ bv10 256)) ((_ sign_extend 168) ((_ extract 87   0) val))
    (ite (= b (_ bv11 256)) ((_ sign_extend 160) ((_ extract 95   0) val))
    (ite (= b (_ bv12 256)) ((_ sign_extend 152) ((_ extract 103  0) val))
    (ite (= b (_ bv13 256)) ((_ sign_extend 144) ((_ extract 111  0) val))
    (ite (= b (_ bv14 256)) ((_ sign_extend 136) ((_ extract 119  0) val))
    (ite (= b (_ bv15 256)) ((_ sign_extend 128) ((_ extract 127  0) val))
    (ite (= b (_ bv16 256)) ((_ sign_extend 120) ((_ extract 135  0) val))
    (ite (= b (_ bv17 256)) ((_ sign_extend 112) ((_ extract 143  0) val))
    (ite (= b (_ bv18 256)) ((_ sign_extend 104) ((_ extract 151  0) val))
    (ite (= b (_ bv19 256)) ((_ sign_extend 96 ) ((_ extract 159  0) val))
    (ite (= b (_ bv20 256)) ((_ sign_extend 88 ) ((_ extract 167  0) val))
    (ite (= b (_ bv21 256)) ((_ sign_extend 80 ) ((_ extract 175  0) val))
    (ite (= b (_ bv22 256)) ((_ sign_extend 72 ) ((_ extract 183  0) val))
    (ite (= b (_ bv23 256)) ((_ sign_extend 64 ) ((_ extract 191  0) val))
    (ite (= b (_ bv24 256)) ((_ sign_extend 56 ) ((_ extract 199  0) val))
    (ite (= b (_ bv25 256)) ((_ sign_extend 48 ) ((_ extract 207  0) val))
    (ite (= b (_ bv26 256)) ((_ sign_extend 40 ) ((_ extract 215  0) val))
    (ite (= b (_ bv27 256)) ((_ sign_extend 32 ) ((_ extract 223  0) val))
    (ite (= b (_ bv28 256)) ((_ sign_extend 24 ) ((_ extract 231  0) val))
    (ite (= b (_ bv29 256)) ((_ sign_extend 16 ) ((_ extract 239  0) val))
    (ite (= b (_ bv30 256)) ((_ sign_extend 8  ) ((_ extract 247  0) val)) val))))))))))))))))))))))))))))))))

  ; storage
  (declare-const abstractStore Storage)
  (define-const emptyStore Storage ((as const Storage) ((as const (Array (_ BitVec 256) (_ BitVec 256))) #x0000000000000000000000000000000000000000000000000000000000000000)))

  (define-fun sstore ((addr Word) (key Word) (val Word) (storage Storage)) Storage (store storage addr (store (select storage addr) key val)))

  (define-fun sload ((addr Word) (key Word) (storage Storage)) Word (select (select storage addr) key))
  |]


exprToSMT :: Expr a -> Builder
exprToSMT = \case
  Lit w -> fromLazyText $ "(_ bv" <> (T.pack $ show (num w :: Integer)) <> " 256)"
  Var s -> fromText s
  GVar (BufVar n) -> fromLazyText $ "buf" <> (T.pack . show $ n)
  GVar (StoreVar n) -> fromLazyText $ "store" <> (T.pack . show $ n)
  JoinBytes
    z o two three four five six seven
    eight nine ten eleven twelve thirteen fourteen fifteen
    sixteen seventeen eighteen nineteen twenty twentyone twentytwo twentythree
    twentyfour twentyfive twentysix twentyseven twentyeight twentynine thirty thirtyone
    -> concatBytes [
        z, o, two, three, four, five, six, seven
        , eight, nine, ten, eleven, twelve, thirteen, fourteen, fifteen
        , sixteen, seventeen, eighteen, nineteen, twenty, twentyone, twentytwo, twentythree
        , twentyfour, twentyfive, twentysix, twentyseven, twentyeight, twentynine, thirty, thirtyone]

  Add a b -> op2 "bvadd" a b
  Sub a b -> op2 "bvsub" a b
  Mul a b -> op2 "bvmul" a b
  Exp a b -> case b of
               Lit b' -> expandExp a b'
               _ -> error "cannot encode symbolic exponentation into SMT"
  Min a b ->
    let aenc = exprToSMT a
        benc = exprToSMT b in
    "(ite (bvule " <> aenc `sp` benc <> ") " <> aenc `sp` benc <> ")"
  LT a b ->
    let cond = op2 "bvult" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  SLT a b ->
    let cond = op2 "bvslt" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  GT a b ->
    let cond = op2 "bvugt" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  LEq a b ->
    let cond = op2 "bvule" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  GEq a b ->
    let cond = op2 "bvuge" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  Eq a b ->
    let cond = op2 "=" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  IsZero a ->
    let cond = op2 "=" a (Lit 0) in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  And a b -> op2 "bvand" a b
  Or a b -> op2 "bvor" a b
  Xor a b -> op2 "bvxor" a b
  Not a -> op1 "bvnot" a
  SHL a b -> op2 "bvshl" b a
  SHR a b -> op2 "bvlshr" b a
  SAR a b -> op2 "bvashr" b a
  SEx a b -> op2 "signext" a b
  Div a b -> op2CheckZero "bvudiv" a b
  SDiv a b -> op2CheckZero "bvsdiv" a b
  Mod a b -> op2CheckZero "bvurem" a b
  SMod a b -> op2CheckZero "bvsrem" a b
  -- NOTE: this needs to do the MUL at a higher precision, then MOD, then downcast
  MulMod a b c ->
    let aExp = exprToSMT a
        bExp = exprToSMT b
        cExp = exprToSMT c
        aLift = "(concat (_ bv0 256) " <> aExp <> ")"
        bLift = "(concat (_ bv0 256) " <> bExp <> ")"
        cLift = "(concat (_ bv0 256) " <> cExp <> ")"
    in  "((_ extract 255 0) (ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 512) (bvurem (bvmul " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
  AddMod a b c ->
    let aExp = exprToSMT a
        bExp = exprToSMT b
        cExp = exprToSMT c
        aLift = "(concat (_ bv0 256) " <> aExp <> ")"
        bLift = "(concat (_ bv0 256) " <> bExp <> ")"
        cLift = "(concat (_ bv0 256) " <> cExp <> ")"
    in  "((_ extract 255 0) (ite (= " <> cExp <> " (_ bv0 256)) (_ bv0 512) (bvurem (bvadd " <> aLift `sp` bLift <> ")" <> cLift <> ")))"
  EqByte a b ->
    let cond = op2 "=" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  Keccak a ->
    let enc = exprToSMT a in
    "(keccak " <> enc <> ")"
  SHA256 a ->
    let enc = exprToSMT a in
    "(sha256 " <> enc <> ")"

  CallValue a -> fromLazyText $ T.append "callvalue_" (T.pack . show $ a)
  Caller a -> fromLazyText $ T.append "caller_" (T.pack . show $ a)
  Address a -> fromLazyText $ T.append "address_" (T.pack . show $ a)

  Origin ->  "origin"
  BlockHash a ->
    let enc = exprToSMT a in
    "(blockhash " <> enc <> ")"
  Coinbase -> "coinbase"
  Timestamp -> "timestamp"
  BlockNumber -> "blocknumber"
  PrevRandao -> "prevrandao"
  GasLimit -> "gaslimit"
  ChainId -> "chainid"
  BaseFee -> "basefee"

  -- TODO: make me binary...
  LitByte b -> fromLazyText $ "(_ bv" <> T.pack (show (num b :: Integer)) <> " 8)"
  IndexWord idx w -> case idx of
    Lit n -> if n >= 0 && n < 32
             then
               let enc = exprToSMT w in
               fromLazyText ("(indexWord" <> T.pack (show (num n :: Integer))) `sp` enc <> ")"
             else exprToSMT (LitByte 0)
    _ -> op2 "indexWord" idx w
  ReadByte idx src -> op2 "select" src idx

  ConcreteBuf "" -> "emptyBuf"
  ConcreteBuf bs -> writeBytes bs mempty
  AbstractBuf s -> fromText s
  ReadWord idx prev -> op2 "readWord" idx prev
  BufLength b -> op1 "bufLength" b
  WriteByte idx val prev ->
    let encIdx = exprToSMT idx
        encVal = exprToSMT val
        encPrev = exprToSMT prev in
    "(store " <> encPrev `sp` encIdx `sp` encVal <> ")"
  WriteWord idx val prev ->
    let encIdx = exprToSMT idx
        encVal = exprToSMT val
        encPrev = exprToSMT prev in
    "(writeWord " <> encIdx `sp` encVal `sp` encPrev <> ")"
  CopySlice srcIdx dstIdx size src dst ->
    copySlice srcIdx dstIdx size (exprToSMT src) (exprToSMT dst)
  EmptyStore -> "emptyStore"
  ConcreteStore s -> encodeConcreteStore s
  AbstractStore -> "abstractStore"
  SStore addr idx val prev ->
    let encAddr = exprToSMT addr
        encIdx = exprToSMT idx
        encVal = exprToSMT val
        encPrev = exprToSMT prev in
    "(sstore" `sp` encAddr `sp` encIdx `sp` encVal `sp` encPrev <> ")"
  SLoad addr idx store -> op3 "sload" addr idx store

  a -> error $ "TODO: implement: " <> show a
  where
    op1 op a =
      let enc =  exprToSMT a in
      "(" <> op `sp` enc <> ")"
    op2 op a b =
      let aenc = exprToSMT a
          benc = exprToSMT b in
      "(" <> op `sp` aenc `sp` benc <> ")"
    op3 op a b c =
      let aenc = exprToSMT a
          benc = exprToSMT b
          cenc = exprToSMT c in
      "(" <> op `sp` aenc `sp` benc `sp` cenc <> ")"
    op2CheckZero op a b =
      let aenc = exprToSMT a
          benc = exprToSMT b in
      "(ite (= " <> benc <> " (_ bv0 256)) (_ bv0 256) " <>  "(" <> op `sp` aenc `sp` benc <> "))"

sp :: Builder -> Builder -> Builder
a `sp` b = a <> (fromText " ") <> b

zero :: Builder
zero = "(_ bv0 256)"

one :: Builder
one = "(_ bv1 256)"

propToSMT :: Prop -> Builder
propToSMT = \case
  PEq a b -> op2 "=" a b
  PLT a b -> op2 "bvult" a b
  PGT a b -> op2 "bvugt" a b
  PLEq a b -> op2 "bvule" a b
  PGEq a b -> op2 "bvuge" a b
  PNeg a ->
    let enc = propToSMT a in
    "(not " <> enc <> ")"
  PAnd a b ->
    let aenc = propToSMT a
        benc = propToSMT b in
    "(and " <> aenc <> " " <> benc <> ")"
  POr a b ->
    let aenc = propToSMT a
        benc = propToSMT b in
    "(or " <> aenc <> " " <> benc <> ")"
  PImpl a b ->
    let aenc = propToSMT a
        benc = propToSMT b in
    "(=> " <> aenc <> " " <> benc <> ")"
  PBool b -> if b then "true" else "false"
  where
    op2 op a b =
      let aenc = exprToSMT a
          benc = exprToSMT b in
      "(" <> op <> " " <> aenc <> " " <> benc <> ")"



-- ** Helpers ** ---------------------------------------------------------------------------------


-- | Stores a region of src into dst
copySlice :: Expr EWord -> Expr EWord -> Expr EWord -> Builder -> Builder -> Builder
copySlice srcOffset dstOffset size@(Lit _) src dst
  | size == (Lit 0) = dst
  | otherwise =
    let size' = (sub size (Lit 1))
        encDstOff = exprToSMT (add dstOffset size')
        encSrcOff = exprToSMT (add srcOffset size')
        child = copySlice srcOffset dstOffset size' src dst in
    "(store " <> child `sp` encDstOff `sp` "(select " <> src `sp` encSrcOff <> "))"
copySlice _ _ _ _ _ = error "TODO: implement copySlice with a symbolically sized region"

-- | Unrolls an exponentiation into a series of multiplications
expandExp :: Expr EWord -> W256 -> Builder
expandExp base expnt
  | expnt == 1 = exprToSMT base
  | otherwise =
    let b = exprToSMT base
        n = expandExp base (expnt - 1) in
    "(bvmul " <> b `sp` n <> ")"

-- | Concatenates a list of bytes into a larger bitvector
concatBytes :: [Expr Byte] -> Builder
concatBytes bytes =
  let bytesRev = reverse bytes
      a2 = exprToSMT (head bytesRev) in
  foldl wrap a2 $ tail bytesRev
  where
    wrap inner byte =
      let byteSMT = exprToSMT byte in
      "(concat " <> byteSMT `sp` inner <> ")"

-- | Concatenates a list of bytes into a larger bitvector
writeBytes :: ByteString -> Expr Buf -> Builder
writeBytes bytes buf = snd $ BS.foldl' wrap (0, exprToSMT buf) bytes
  where
    -- we don't need to store zeros if the base buffer is empty
    skipZeros = buf == mempty
    wrap :: (Int, Builder) -> Word8 -> (Int, Builder)
    wrap (idx, inner) byte =
      if skipZeros && byte == 0
      then (idx + 1, inner)
      else let
          byteSMT = exprToSMT (LitByte byte)
          idxSMT = exprToSMT . Lit . num $ idx
        in (idx + 1, "(store " <> inner `sp` idxSMT `sp` byteSMT <> ")")

encodeConcreteStore :: Map W256 (Map W256 W256) -> Builder
encodeConcreteStore s = foldl encodeWrite "emptyStore" writes
  where
    asList = fmap (second Map.toList) $ Map.toList s
    writes = concatMap (\(addr, ws) -> fmap (\(k, v) -> (addr, k, v)) ws) asList
    encodeWrite prev (addr, key, val) = let
        encAddr = exprToSMT (Lit addr)
        encKey = exprToSMT (Lit key)
        encVal = exprToSMT (Lit val)
      in "(sstore " <> encAddr `sp` encKey `sp` encVal `sp` prev <> ")"


-- ** Cex parsing ** --------------------------------------------------------------------------------

parseW256 :: SpecConstant -> W256
parseW256 = parseSC

parseInteger :: SpecConstant -> Integer
parseInteger = parseSC

parseW8 :: SpecConstant -> Word8
parseW8 = parseSC

parseSC :: (Num a, Eq a) => SpecConstant -> a
parseSC (SCHexadecimal a) = fst . head . Numeric.readHex . T.unpack . T.fromStrict $ a
parseSC (SCBinary a) = fst . head . Numeric.readBin . T.unpack . T.fromStrict $ a
parseSC sc = error $ "Internal Error: cannot parse: " <> show sc

parseErr :: (Show a) => a -> b
parseErr res = error $ "Internal Error: cannot parse solver response: " <> show res

parseVar :: TS.Text -> Expr EWord
parseVar = Var

parseBlockCtx :: TS.Text -> Expr EWord
parseBlockCtx "origin" = Origin
parseBlockCtx "coinbase" = Coinbase
parseBlockCtx "timestamp" = Timestamp
parseBlockCtx "blocknumber" = BlockNumber
parseBlockCtx "prevrandao" = PrevRandao
parseBlockCtx "gaslimit" = GasLimit
parseBlockCtx "chainid" = ChainId
parseBlockCtx "basefee" = BaseFee
parseBlockCtx t = error $ "Internal Error: cannot parse " <> (TS.unpack t) <> " into an Expr"

parseFrameCtx :: TS.Text -> Expr EWord
parseFrameCtx name = case TS.unpack name of
  ('c':'a':'l':'l':'v':'a':'l':'u':'e':'_':frame) -> CallValue (read frame)
  ('c':'a':'l':'l':'e':'r':'_':frame) -> Caller (read frame)
  ('a':'d':'d':'r':'e':'s':'s':'_':frame) -> Address (read frame)
  t -> error $ "Internal Error: cannot parse " <> t <> " into an Expr"

getVars :: (TS.Text -> Expr EWord) -> (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr EWord) W256)
getVars parseFn getVal names = Map.mapKeys parseFn <$> foldM getOne mempty names
  where
    getOne :: Map TS.Text W256 -> TS.Text -> IO (Map TS.Text W256)
    getOne acc name = do
      raw <- getVal (T.fromStrict name)
      let
        parsed = case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
          Right (ResSpecific (valParsed :| [])) -> valParsed
          r -> parseErr r
        val = case parsed of
          (TermQualIdentifier (
            Unqualified (IdSymbol symbol)),
            TermSpecConstant sc)
              -> if symbol == name
                 then parseW256 sc
                 else error "Internal Error: solver did not return model for requested value"
          r -> parseErr r
      pure $ Map.insert name val acc

getBufs :: (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr Buf) ByteString)
getBufs getVal names = foldM getBuf mempty names
  where
    getLength :: TS.Text -> IO Int
    getLength name = do
      val <- getVal (T.fromStrict name <> "_length")
      len <- case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (parsed :| [])) -> case parsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), (TermSpecConstant sc))
            -> if symbol == (name <> "_length")
               then pure $ parseW256 sc
               else error "Internal Error: solver did not return model for requested value"
          res -> parseErr res
        res -> parseErr res
      pure $ if len <= num (maxBound :: Int)
             then fromIntegral len
             else error $ "Internal Error: buffer: "
                       <> (TS.unpack name)
                       <> " is too large to be represented in a ByteString. Length: "
                       <> show len

    getBuf :: Map (Expr Buf) ByteString -> TS.Text -> IO (Map (Expr Buf) ByteString)
    getBuf acc name = do
      -- Sometimes the solver gives us back a model for a Buffer that has every
      -- element set to some concrete value. This is impossible to represent as
      -- a concrete ByteString in haskell (or in any existing computer hardware :D),
      -- so we ask the solver to give us back a model for the length of
      -- this buffer and then use that to produce a shorter counterexample (by
      -- replicating the constant byte up to the length).
      len <- getLength name
      val <- getVal (T.fromStrict name)

      buf <- case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (valParsed :| [])) -> case valParsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), term)
            -> if symbol == name
               then pure $ parseBuf len term
               else error "Internal Error: solver did not return model for requested value"
          res -> error $ "Internal Error: cannot parse solver response: " <> show res
        res -> error $ "Internal Error: cannot parse solver response: " <> show res
      let bs = case simplify buf of
                 ConcreteBuf b -> b
                 p -> error $ "Internal Error: unable to parse solver response into a concrete buffer: " <> show p
      pure $ Map.insert (AbstractBuf name) bs acc

    parseBuf :: Int -> Term -> Expr Buf
    parseBuf len = go mempty
      where
        go env = \case
          -- constant arrays
          (TermApplication (
            Qualified (IdSymbol "const") (
              SortParameter (IdSymbol "Array") (
                SortSymbol (IdIndexed "BitVec" (IxNumeral "256" :| []))
                :| [SortSymbol (IdIndexed "BitVec" (IxNumeral "8" :| []))]
              )
            )) ((TermSpecConstant val :| [])))
            -> case val of
                 SCHexadecimal "00" -> mempty
                 v -> ConcreteBuf $ BS.replicate len (parseW8 v)

          -- writing a byte over some array
          (TermApplication
            (Unqualified (IdSymbol "store"))
            (base :| [TermSpecConstant idx, TermSpecConstant val])
            ) -> let
              pbase = go env base
              pidx = parseW256 idx
              pval = parseW8 val
            in writeByte (Lit pidx) (LitByte pval) pbase

          -- binding a new name
          (TermLet ((VarBinding name bound) :| []) term) -> let
              pbound = go env bound
            in go (Map.insert name pbound env) term

          -- looking up a bound name
          (TermQualIdentifier (Unqualified (IdSymbol name))) -> case Map.lookup name env of
            Just t -> t
            Nothing -> error $ "Internal error: could not find "
                            <> (TS.unpack name)
                            <> " in environment mapping"
          p -> parseErr p

getStore :: (Text -> IO Text) -> [(Expr EWord, Expr EWord)] -> IO (Map W256 (Map W256 W256))
getStore getVal sreads = do
  raw <- getVal "abstractStore"
  let parsed = case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
                 Right (ResSpecific (valParsed :| [])) -> valParsed
                 r -> parseErr r
      -- first interpret SMT term as a function
      fun = case parsed of
              (TermQualIdentifier (Unqualified (IdSymbol symbol)), term) ->
                if symbol == "abstractStore"
                then interpret2DArray Map.empty term
                else error "Internal Error: solver did not return model for requested value"
              r -> parseErr r

  -- then create a map by adding only the locations that are read by the program
  foldM (\m (addr, slot) -> do
            addr' <- queryValue addr
            slot' <- queryValue slot
            pure $ addElem addr' slot' m fun) Map.empty sreads

  where

    addElem :: W256 -> W256 -> Map W256 (Map W256 W256) -> (W256 -> W256 -> W256) -> Map W256 (Map W256 W256)
    addElem addr slot store fun =
      case Map.lookup addr store of
        Just m -> Map.insert addr (Map.insert slot (fun addr slot) m) store
        Nothing -> Map.insert addr (Map.singleton slot (fun addr slot)) store


    queryValue :: Expr EWord -> IO W256
    queryValue (Lit w) = pure w
    queryValue w = do
      let expr = toLazyText $ exprToSMT w
      raw <- getVal expr
      case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
        Right (ResSpecific (valParsed :| [])) ->
          case valParsed of
            (_, TermSpecConstant sc) -> pure $ parseW256 sc
            _ -> error "Internal Error: cannot parse model for storage index"
        r -> parseErr r



-- | Interpret an N-dimensional array as a value of type a.
-- Parameterized by an interpretation function for array values.
interpretNDArray :: (Map Symbol Term -> Term -> a) -> (Map Symbol Term) -> Term -> (W256 -> a)
interpretNDArray interp env = \case
  -- variable reference
  TermQualIdentifier (Unqualified (IdSymbol s)) ->
    case Map.lookup s env of
      Just t -> interpretNDArray interp env t
      Nothing -> error "Internal error: unknown identifier, cannot parse array"
  -- (let (x t') t)
  TermLet (VarBinding x t' :| []) t -> interpretNDArray interp (Map.insert x t' env) t
  TermLet (VarBinding x t' :| lets) t -> interpretNDArray interp (Map.insert x t' env) (TermLet (NonEmpty.fromList lets) t)
  -- (as const (Array (_ BitVec 256) (_ BitVec 256))) SpecConstant
  TermApplication asconst (val :| []) | isArrConst asconst ->
    \_ -> interp env val
  -- (store arr ind val)
  TermApplication store (arr :| [TermSpecConstant ind, val]) | isStore store ->
    \x -> if x == parseW256 ind then interp env val else interpretNDArray interp env arr x
  t -> error $ "Internal error: cannot parse array value. Unexpected term: " <> (show t)

  where
    isArrConst :: QualIdentifier -> Bool
    isArrConst = \case
      Qualified (IdSymbol "const") (SortParameter (IdSymbol "Array") _) -> True
      _ -> False

    isStore :: QualIdentifier -> Bool
    isStore t = t == Unqualified (IdSymbol "store")


-- | Interpret an 1-dimensional array as a function
interpret1DArray :: (Map Symbol Term) -> Term -> (W256 -> W256)
interpret1DArray = interpretNDArray interpretW256
  where
    interpretW256 :: (Map Symbol Term) -> Term -> W256
    interpretW256 _ (TermSpecConstant val) = parseW256 val
    interpretW256 env (TermQualIdentifier (Unqualified (IdSymbol s))) =
      case Map.lookup s env of
        Just t -> interpretW256 env t
        Nothing -> error "Internal error: unknown identifier, cannot parse array"
    interpretW256 _ t = error $ "Internal error: cannot parse array value. Unexpected term: " <> (show t)

-- | Interpret an 2-dimensional array as a function
interpret2DArray :: (Map Symbol Term) -> Term -> (W256 -> W256 -> W256)
interpret2DArray = interpretNDArray interpret1DArray
