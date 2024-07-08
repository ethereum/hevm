{-# LANGUAGE DataKinds #-}
{-# LANGUAGE QuasiQuotes #-}

{- |
    Module: EVM.SMT
    Description: Utilities for building and executing SMT queries from Expr instances
-}
module EVM.SMT where

import Prelude hiding (LT, GT)

import Control.Monad
import Data.Containers.ListUtils (nubOrd)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List qualified as List
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.String.Here
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Word (Word8)
import Data.Text.Lazy (Text)
import Data.Text qualified as TS
import Data.Text.Lazy qualified as T
import Data.Text.Lazy.Builder
import Language.SMT2.Parser (getValueRes, parseCommentFreeFileMsg)
import Language.SMT2.Syntax (Symbol, SpecConstant(..), GeneralRes(..), Term(..), QualIdentifier(..), Identifier(..), Sort(..), Index(..), VarBinding(..))
import Numeric (readHex, readBin)
import Witch (into, unsafeInto)
import Control.Monad.State (State, runState, get, put)
import EVM.Format (formatProp)

import EVM.CSE
import EVM.Expr (writeByte, bufLengthEnv, containsNode, bufLength, minLength, inRange)
import EVM.Expr qualified as Expr
import EVM.Keccak (keccakAssumptions, keccakCompute)
import EVM.Traversals
import EVM.Types
import EVM.Effects


-- ** Encoding ** ----------------------------------------------------------------------------------


-- | Data that we need to construct a nice counterexample
data CexVars = CexVars
  { -- | variable names that we need models for to reconstruct calldata
    calldata     :: [Text]
    -- | symbolic address names
  , addrs        :: [Text]
    -- | buffer names and guesses at their maximum size
  , buffers      :: Map Text (Expr EWord)
    -- | reads from abstract storage
  , storeReads   :: Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
    -- | the names of any block context variables
  , blockContext :: [Text]
    -- | the names of any tx context variables
  , txContext    :: [Text]
  }
  deriving (Eq, Show)

instance Semigroup CexVars where
  (CexVars a b c d e f) <> (CexVars a2 b2 c2 d2 e2 f2) = CexVars (a <> a2) (b <> b2) (c <> c2) (d <> d2) (e <> e2) (f <> f2)

instance Monoid CexVars where
    mempty = CexVars
      { calldata = mempty
      , addrs = mempty
      , buffers = mempty
      , storeReads = mempty
      , blockContext = mempty
      , txContext = mempty
      }

-- | A model for a buffer, either in it's compressed form (for storing parsed
-- models from a solver), or as a bytestring (for presentation to users)
data BufModel
  = Comp CompressedBuf
  | Flat ByteString
  deriving (Eq, Show)

-- | This representation lets us store buffers of arbitrary length without
-- exhausting the available memory, it closely matches the format used by
-- smt-lib when returning models for arrays
data CompressedBuf
  = Base { byte :: Word8, length :: W256}
  | Write { byte :: Word8, idx :: W256, next :: CompressedBuf }
  deriving (Eq, Show)


-- | a final post shrinking cex, buffers here are all represented as concrete bytestrings
data SMTCex = SMTCex
  { vars :: Map (Expr EWord) W256
  , addrs :: Map (Expr EAddr) Addr
  , buffers :: Map (Expr Buf) BufModel
  , store :: Map (Expr EAddr) (Map W256 W256)
  , blockContext :: Map (Expr EWord) W256
  , txContext :: Map (Expr EWord) W256
  }
  deriving (Eq, Show)


-- | Used for abstraction-refinement of the SMT formula. Contains assertions that make our query fully precise. These will be added to the assertion stack if we get `sat` with the abstracted query.
data RefinementEqs = RefinementEqs [Builder] [Prop]
  deriving (Eq, Show)

instance Semigroup RefinementEqs where
  (RefinementEqs a b) <> (RefinementEqs a2 b2) = RefinementEqs (a <> a2) (b <> b2)

instance Monoid RefinementEqs where
  mempty = RefinementEqs mempty mempty

flattenBufs :: SMTCex -> Maybe SMTCex
flattenBufs cex = do
  bs <- mapM collapse cex.buffers
  pure $ cex{ buffers = bs }

-- | Attempts to collapse a compressed buffer representation down to a flattened one
collapse :: BufModel -> Maybe BufModel
collapse model = case toBuf model of
  Just (ConcreteBuf b) -> Just $ Flat b
  _ -> Nothing
  where
    toBuf (Comp (Base b sz)) | sz <= 120_000_000 = Just . ConcreteBuf $ BS.replicate (unsafeInto sz) b
    toBuf (Comp (Write b idx next)) = fmap (writeByte (Lit idx) (LitByte b)) (toBuf $ Comp next)
    toBuf (Flat b) = Just . ConcreteBuf $ b
    toBuf _ = Nothing

getVar :: SMTCex -> TS.Text -> W256
getVar cex name = fromJust $ Map.lookup (Var name) cex.vars

data SMT2 = SMT2 [Builder] RefinementEqs CexVars [Prop]
  deriving (Eq, Show)

instance Semigroup SMT2 where
  (SMT2 a (RefinementEqs b refps) c d) <> (SMT2 a2 (RefinementEqs b2 refps2) c2 d2) = SMT2 (a <> a2) (RefinementEqs (b <> b2) (refps <> refps2)) (c <> c2) (d <> d2)

instance Monoid SMT2 where
  mempty = SMT2 mempty mempty mempty mempty

formatSMT2 :: SMT2 -> Text
formatSMT2 (SMT2 ls _ _ ps) = expr <> smt2
 where
 expr = T.concat [T.singleton ';', T.replace "\n" "\n;" $ T.pack . TS.unpack $  TS.unlines (fmap formatProp ps)]
 smt2 = T.unlines (fmap toLazyText ls)

-- | Reads all intermediate variables from the builder state and produces SMT declaring them as constants
declareIntermediates :: BufEnv -> StoreEnv -> SMT2
declareIntermediates bufs stores =
  let encSs = Map.mapWithKey encodeStore stores
      encBs = Map.mapWithKey encodeBuf bufs
      sorted = List.sortBy compareFst $ Map.toList $ encSs <> encBs
      decls = fmap snd sorted
      smt2 = (SMT2 [fromText "; intermediate buffers & stores"] mempty mempty mempty):decls
  in  foldr (<>) (SMT2[""] mempty mempty mempty) smt2
  where
    compareFst (l, _) (r, _) = compare l r
    encodeBuf n expr =
      SMT2 ["(define-fun buf" <> (fromString . show $ n) <> "() Buf " <> exprToSMT expr <> ")\n"]  mempty mempty mempty <> encodeBufLen n expr
    encodeBufLen n expr =
      SMT2 ["(define-fun buf" <> (fromString . show $ n) <>"_length () (_ BitVec 256) " <> exprToSMT (bufLengthEnv bufs True expr) <> ")"] mempty mempty mempty
    encodeStore n expr =
      SMT2 ["(define-fun store" <> (fromString . show $ n) <> " () Storage " <> exprToSMT expr <> ")"] mempty mempty mempty

data AbstState = AbstState
  { words :: Map (Expr EWord) Int
  , count :: Int
  }
  deriving (Show)

abstractAwayProps :: Config -> [Prop] -> ([Prop], AbstState)
abstractAwayProps conf ps = runState (mapM abstrAway ps) (AbstState mempty 0)
  where
    abstrAway :: Prop -> State AbstState Prop
    abstrAway prop = mapPropM go prop
    go :: Expr a -> State AbstState (Expr a)
    go x = case x of
        e@(Mod{})       | conf.abstRefineArith  -> abstrExpr e
        e@(SMod{})      | conf.abstRefineArith  -> abstrExpr e
        e@(MulMod{})    | conf.abstRefineArith  -> abstrExpr e
        e@(AddMod{})    | conf.abstRefineArith  -> abstrExpr e
        e@(Mul{})       | conf.abstRefineArith  -> abstrExpr e
        e@(Div{})       | conf.abstRefineArith  -> abstrExpr e
        e@(SDiv {})     | conf.abstRefineArith  -> abstrExpr e
        e@(ReadWord {}) | conf.abstRefineMem -> abstrExpr e
        e -> pure e
        where
            abstrExpr e = do
              s <- get
              case Map.lookup e s.words of
                Just v -> pure (Var (TS.pack ("abst_" ++ show v)))
                Nothing -> do
                  let
                    next = s.count
                    bs' = Map.insert e next s.words
                  put $ s{words=bs', count=next+1}
                  pure $ Var (TS.pack ("abst_" ++ show next))

smt2Line :: Builder -> SMT2
smt2Line txt = SMT2 [txt] mempty mempty mempty

assertProps :: Config -> [Prop] -> SMT2
-- simplify to rewrite sload/sstore combos
-- notice: it is VERY important not to concretize, because Keccak assumptions
--         will be generated by assertPropsNoSimp, and that needs unconcretized Props
assertProps conf ps = assertPropsNoSimp conf (decompose . Expr.simplifyProps $ ps)
  where
    decompose :: [Prop] -> [Prop]
    decompose props = if conf.decomposeStorage && safeExprs && safeProps
                      then fromMaybe props (mapM (mapPropM Expr.decomposeStorage) props)
                      else props
      where
        -- All in these lists must be a `Just ()` or we cannot decompose
        safeExprs = all (isJust . mapPropM_ Expr.safeToDecompose) props
        safeProps = all Expr.safeToDecomposeProp props

-- Note: we need a version that does NOT call simplify,
-- because we make use of it to verify the correctness of our simplification
-- passes through property-based testing.
assertPropsNoSimp :: Config -> [Prop] -> SMT2
assertPropsNoSimp config psPreConc =
  let encs = map propToSMT psElimAbst
      abstSMT = map propToSMT abstProps
      intermediates = declareIntermediates bufs stores in
  prelude
  <> (declareAbstractStores abstractStores)
  <> smt2Line ""
  <> (declareAddrs addresses)
  <> smt2Line ""
  <> (declareBufs toDeclarePsElim bufs stores)
  <> smt2Line ""
  <> (declareVars . nubOrd $ foldl (<>) [] allVars)
  <> smt2Line ""
  <> (declareFrameContext . nubOrd $ foldl (<>) [] frameCtx)
  <> smt2Line ""
  <> (declareBlockContext . nubOrd $ foldl (<>) [] blockCtx)
  <> smt2Line ""
  <> intermediates
  <> smt2Line ""
  <> keccakAssertions
  <> readAssumes
  <> smt2Line ""
  <> SMT2 (fmap (\p -> "(assert " <> p <> ")") encs) mempty mempty mempty
  <> SMT2 mempty (RefinementEqs (fmap (\p -> "(assert " <> p <> ")") abstSMT) (psElimAbst <> abstProps)) mempty mempty
  <> SMT2 mempty mempty mempty { storeReads = storageReads } mempty
  <> SMT2 mempty mempty mempty psPreConc

  where
    ps = Expr.concKeccakProps psPreConc
    (psElim, bufs, stores) = eliminateProps ps
    (psElimAbst, abst@(AbstState abstExprToInt _)) = if config.abstRefineArith || config.abstRefineMem
      then abstractAwayProps config psElim
      else (psElim, AbstState mempty 0)

    abstProps = map toProp (Map.toList abstExprToInt)
      where
      toProp :: (Expr EWord, Int) -> Prop
      toProp (e, num) = PEq e (Var (TS.pack ("abst_" ++ (show num))))

    -- Props storing info that need declaration(s)
    toDeclarePs     = ps <> keccAssump <> keccComp
    toDeclarePsElim = psElim <> keccAssump <> keccComp

    -- vars, frames, and block contexts in need of declaration
    allVars = fmap referencedVars toDeclarePsElim <> fmap referencedVars bufVals <> fmap referencedVars storeVals <> [abstrVars abst]
    frameCtx = fmap referencedFrameContext toDeclarePsElim <> fmap referencedFrameContext bufVals <> fmap referencedFrameContext storeVals
    blockCtx = fmap referencedBlockContext toDeclarePsElim <> fmap referencedBlockContext bufVals <> fmap referencedBlockContext storeVals

    abstrVars :: AbstState -> [Builder]
    abstrVars (AbstState b _) = map ((\v->fromString ("abst_" ++ show v)) . snd) (Map.toList b)

    -- Buf, Storage, etc. declarations needed
    bufVals = Map.elems bufs
    storeVals = Map.elems stores
    storageReads = Map.unionsWith (<>) $ fmap findStorageReads toDeclarePs
    abstractStores = Set.toList $ Set.unions (fmap referencedAbstractStores toDeclarePs)
    addresses = Set.toList $ Set.unions (fmap referencedWAddrs toDeclarePs)

    -- Keccak assertions: concrete values, distance between pairs, injectivity, etc.
    --      This will make sure concrete values of Keccak are asserted, if they can be computed (i.e. can be concretized)
    keccAssump = keccakAssumptions psPreConc bufVals storeVals
    keccComp = keccakCompute psPreConc bufVals storeVals
    keccakAssertions
      = smt2Line "; keccak assumptions"
      <> SMT2 (fmap (\p -> "(assert " <> propToSMT p <> ")") keccAssump) mempty mempty mempty
      <> smt2Line "; keccak computations"
      <> SMT2 (fmap (\p -> "(assert " <> propToSMT p <> ")") keccComp) mempty mempty mempty

    -- assert that reads beyond size of buffer & storage is zero
    readAssumes
      = smt2Line "; read assumptions"
        <> SMT2 (fmap (\p -> "(assert " <> propToSMT p <> ")") (assertReads psElim bufs stores)) mempty mempty mempty

referencedAbstractStores :: TraversableTerm a => a -> Set Builder
referencedAbstractStores term = foldTerm go mempty term
  where
    go = \case
      AbstractStore s idx -> Set.singleton (storeName s idx)
      _ -> mempty

referencedWAddrs :: TraversableTerm a => a -> Set Builder
referencedWAddrs term = foldTerm go mempty term
  where
    go = \case
      WAddr(a@(SymAddr _)) -> Set.singleton (formatEAddr a)
      _ -> mempty

referencedBufs :: TraversableTerm a => a -> [Builder]
referencedBufs expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [Builder]
    go = \case
      AbstractBuf s -> [fromText s]
      _ -> []

referencedVars :: TraversableTerm a => a -> [Builder]
referencedVars expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [Builder]
    go = \case
      Var s -> [fromText s]
      _ -> []

referencedFrameContext :: TraversableTerm a => a -> [(Builder, [Prop])]
referencedFrameContext expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [(Builder, [Prop])]
    go = \case
      TxValue -> [(fromString "txvalue", [])]
      v@(Balance a) -> [(fromString "balance_" <> formatEAddr a, [PLT v (Lit $ 2 ^ (96 :: Int))])]
      Gas {} -> internalError "TODO: GAS"
      _ -> []

referencedBlockContext :: TraversableTerm a => a -> [(Builder, [Prop])]
referencedBlockContext expr = nubOrd $ foldTerm go [] expr
  where
    go :: Expr a -> [(Builder, [Prop])]
    go = \case
      Origin -> [("origin", [inRange 160 Origin])]
      Coinbase -> [("coinbase", [inRange 160 Coinbase])]
      Timestamp -> [("timestamp", [])]
      BlockNumber -> [("blocknumber", [])]
      PrevRandao -> [("prevrandao", [])]
      GasLimit -> [("gaslimit", [])]
      ChainId -> [("chainid", [])]
      BaseFee -> [("basefee", [])]
      _ -> []

-- | This function overapproximates the reads from the abstract
-- storage. Potentially, it can return locations that do not read a
-- slot directly from the abstract store but from subsequent writes on
-- the store (e.g, SLoad addr idx (SStore addr idx val AbstractStore)).
-- However, we expect that most of such reads will have been
-- simplified away.
findStorageReads :: Prop -> Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
findStorageReads p = Map.fromListWith (<>) $ foldProp go mempty p
  where
    go :: Expr a -> [((Expr EAddr, Maybe W256), Set (Expr EWord))]
    go = \case
      SLoad slot store ->
        [((fromMaybe (internalError $ "could not extract address from: " <> show store) (Expr.getAddr store), Expr.getLogicalIdx store), Set.singleton slot) | containsNode isAbstractStore store]
      _ -> []

    isAbstractStore (AbstractStore _ _) = True
    isAbstractStore _ = False

findBufferAccess :: TraversableTerm a => [a] -> [(Expr EWord, Expr EWord, Expr Buf)]
findBufferAccess = foldl (foldTerm go) mempty
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
assertReads props benv senv = concatMap assertRead allReads
  where
    assertRead :: (Expr EWord, Expr EWord, Expr Buf) -> [Prop]
    assertRead (idx, Lit 32, buf) = [PImpl (PGEq idx (bufLength buf)) (PEq (ReadWord idx buf) (Lit 0))]
    assertRead (idx, Lit sz, buf) =
      fmap
        -- TODO: unsafeInto instead fromIntegral here makes symbolic tests fail
        (PImpl (PGEq idx (bufLength buf)) . PEq (ReadByte idx buf) . LitByte . fromIntegral)
        [(0::Int)..unsafeInto sz-1]
    assertRead (_, _, _) = internalError "Cannot generate assertions for accesses of symbolic size"

    allReads = filter keepRead $ nubOrd $ findBufferAccess props <> findBufferAccess (Map.elems benv) <> findBufferAccess (Map.elems senv)

    -- discard constraints if we can statically determine that read is less than the buffer length
    keepRead (Lit idx, Lit size, buf) =
      case minLength benv buf of
        Just l | into (idx + size) <= l -> False
        _ -> True
    keepRead _ = True

-- | Finds the maximum read index for each abstract buffer in the input props
discoverMaxReads :: [Prop] -> BufEnv -> StoreEnv -> Map Text (Expr EWord)
discoverMaxReads props benv senv = bufMap
  where
    allReads = nubOrd $ findBufferAccess props <> findBufferAccess (Map.elems benv) <> findBufferAccess (Map.elems senv)
    -- we can have buffers that are not read from but are still mentioned via BufLength in some branch condition
    -- we assign a default read hint of 4 to start with in these cases (since in most cases we will need at least 4 bytes to produce a counterexample)
    allBufs = Map.fromList . fmap (, Lit 4) . fmap toLazyText . nubOrd . concat $ fmap referencedBufs props <> fmap referencedBufs (Map.elems benv) <> fmap referencedBufs (Map.elems senv)

    bufMap = Map.unionWith Expr.max (foldl addBound mempty allReads) allBufs

    addBound m (idx, size, buf) =
      case baseBuf buf of
        AbstractBuf b -> Map.insertWith Expr.max (T.fromStrict b) (Expr.add idx size) m
        _ -> m

    baseBuf :: Expr Buf -> Expr Buf
    baseBuf (AbstractBuf b) = AbstractBuf b
    baseBuf (ConcreteBuf b) = ConcreteBuf b
    baseBuf (GVar (BufVar a)) =
      case Map.lookup a benv of
        Just b -> baseBuf b
        Nothing -> internalError "could not find buffer variable"
    baseBuf (WriteByte _ _ b) = baseBuf b
    baseBuf (WriteWord _ _ b) = baseBuf b
    baseBuf (CopySlice _ _ _ _ dst)= baseBuf dst

-- | Returns an SMT2 object with all buffers referenced from the input props declared, and with the appropriate cex extraction metadata attached
declareBufs :: [Prop] -> BufEnv -> StoreEnv -> SMT2
declareBufs props bufEnv storeEnv = SMT2 ("; buffers" : fmap declareBuf allBufs <> ("; buffer lengths" : fmap declareLength allBufs)) mempty cexvars mempty
  where
    cexvars = (mempty :: CexVars){ buffers = discoverMaxReads props bufEnv storeEnv }
    allBufs = fmap fromLazyText $ Map.keys cexvars.buffers
    declareBuf n = "(declare-fun " <> n <> " () (Array (_ BitVec 256) (_ BitVec 8)))"
    declareLength n = "(declare-fun " <> n <> "_length" <> " () (_ BitVec 256))"

-- Given a list of variable names, create an SMT2 object with the variables declared
declareVars :: [Builder] -> SMT2
declareVars names = SMT2 (["; variables"] <> fmap declare names) mempty cexvars mempty
  where
    declare n = "(declare-fun " <> n <> " () (_ BitVec 256))"
    cexvars = (mempty :: CexVars){ calldata = fmap toLazyText names }

-- Given a list of variable names, create an SMT2 object with the variables declared
declareAddrs :: [Builder] -> SMT2
declareAddrs names = SMT2 (["; symbolic addresseses"] <> fmap declare names) mempty cexvars mempty
  where
    declare n = "(declare-fun " <> n <> " () Addr)"
    cexvars = (mempty :: CexVars){ addrs = fmap toLazyText names }

declareFrameContext :: [(Builder, [Prop])] -> SMT2
declareFrameContext names = SMT2 (["; frame context"] <> concatMap declare names) mempty cexvars mempty
  where
    declare (n,props) = [ "(declare-fun " <> n <> " () (_ BitVec 256))" ]
                        <> fmap (\p -> "(assert " <> propToSMT p <> ")") props
    cexvars = (mempty :: CexVars){ txContext = fmap (toLazyText . fst) names }

declareAbstractStores :: [Builder] -> SMT2
declareAbstractStores names = SMT2 (["; abstract base stores"] <> fmap declare names) mempty mempty mempty
  where
    declare n = "(declare-fun " <> n <> " () Storage)"

declareBlockContext :: [(Builder, [Prop])] -> SMT2
declareBlockContext names = SMT2 (["; block context"] <> concatMap declare names) mempty cexvars mempty
  where
    declare (n, props) = [ "(declare-fun " <> n <> " () (_ BitVec 256))" ]
                         <> fmap (\p -> "(assert " <> propToSMT p <> ")") props
    cexvars = (mempty :: CexVars){ blockContext = fmap (toLazyText . fst) names }

prelude :: SMT2
prelude =  SMT2 src mempty mempty mempty
  where
  src = fmap (fromLazyText . T.drop 2) . T.lines $ [i|
  ; logic
  (set-info :smt-lib-version 2.6)
  ;(set-logic QF_AUFBV)
  (set-logic ALL)
  (set-info :source |
  Generator: hevm
  Application: hevm symbolic execution system
  |)
  (set-info :category "industrial")

  ; types
  (define-sort Byte () (_ BitVec 8))
  (define-sort Word () (_ BitVec 256))
  (define-sort Addr () (_ BitVec 160))
  (define-sort Buf () (Array Word Byte))

  ; slot -> value
  (define-sort Storage () (Array Word Word))

  ; hash functions
  (declare-fun keccak (Buf) Word)
  (declare-fun sha256 (Buf) Word)
  (define-fun max ((a (_ BitVec 256)) (b (_ BitVec 256))) (_ BitVec 256) (ite (bvult a b) b a))

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

  (define-fun readWord ((idx Word) (buf Buf)) Word
    (concat
      (select buf idx)
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000001))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000002))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000003))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000004))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000005))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000006))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000007))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000008))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000009))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000a))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000b))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000c))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000d))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000e))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000000f))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000010))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000011))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000012))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000013))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000014))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000015))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000016))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000017))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000018))
      (concat (select buf (bvadd idx #x0000000000000000000000000000000000000000000000000000000000000019))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001a))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001b))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001c))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001d))
      (concat (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001e))
      (select buf (bvadd idx #x000000000000000000000000000000000000000000000000000000000000001f))
      ))))))))))))))))))))))))))))))
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
  (declare-fun codesize (Addr) Word)

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
  |]

exprToSMT :: Expr a -> Builder
exprToSMT = \case
  Lit w -> fromLazyText $ "(_ bv" <> (T.pack $ show (into w :: Integer)) <> " 256)"
  Var s -> fromText s
  GVar (BufVar n) -> fromString $ "buf" <> (show n)
  GVar (StoreVar n) -> fromString $ "store" <> (show n)
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
               _ -> internalError "cannot encode symbolic exponentiation into SMT"
  Min a b ->
    let aenc = exprToSMT a
        benc = exprToSMT b in
    "(ite (bvule " <> aenc `sp` benc <> ") " <> aenc `sp` benc <> ")"
  Max a b ->
    let aenc = exprToSMT a
        benc = exprToSMT b in
    "(max " <> aenc `sp` benc <> ")"
  LT a b ->
    let cond = op2 "bvult" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  SLT a b ->
    let cond = op2 "bvslt" a b in
    "(ite " <> cond `sp` one `sp` zero <> ")"
  SGT a b ->
    let cond = op2 "bvsgt" a b in
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

  TxValue -> fromString "txvalue"
  Balance a -> fromString "balance_" <> formatEAddr a

  Origin ->  "origin"
  BlockHash a ->
    let enc = exprToSMT a in
    "(blockhash " <> enc <> ")"
  CodeSize a ->
    let enc = exprToSMT a in
    "(codesize " <> enc <> ")"
  Coinbase -> "coinbase"
  Timestamp -> "timestamp"
  BlockNumber -> "blocknumber"
  PrevRandao -> "prevrandao"
  GasLimit -> "gaslimit"
  ChainId -> "chainid"
  BaseFee -> "basefee"

  a@(SymAddr _) -> formatEAddr a
  WAddr(a@(SymAddr _)) -> "(concat (_ bv0 96)" `sp` exprToSMT a `sp` ")"

  LitByte b -> fromLazyText $ "(_ bv" <> T.pack (show (into b :: Integer)) <> " 8)"
  IndexWord idx w -> case idx of
    Lit n -> if n >= 0 && n < 32
             then
               let enc = exprToSMT w in
               fromLazyText ("(indexWord" <> T.pack (show (into n :: Integer))) `sp` enc <> ")"
             else exprToSMT (LitByte 0)
    _ -> op2 "indexWord" idx w
  ReadByte idx src -> op2 "select" src idx

  ConcreteBuf "" -> "((as const Buf) #b00000000)"
  ConcreteBuf bs -> writeBytes bs mempty
  AbstractBuf s -> fromText s
  ReadWord idx prev -> op2 "readWord" idx prev
  BufLength (AbstractBuf b) -> fromText b <> "_length"
  BufLength (GVar (BufVar n)) -> fromLazyText $ "buf" <> (T.pack . show $ n) <> "_length"
  BufLength b -> exprToSMT (bufLength b)
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

  -- we need to do a bit of processing here.
  ConcreteStore s -> encodeConcreteStore s
  AbstractStore a idx -> storeName a idx
  SStore idx val prev ->
    let encIdx = exprToSMT idx
        encVal = exprToSMT val
        encPrev = exprToSMT prev in
    "(store" `sp` encPrev `sp` encIdx `sp` encVal <> ")"
  SLoad idx store -> op2 "select" store idx

  a -> internalError $ "TODO: implement: " <> show a
  where
    op1 op a =
      let enc =  exprToSMT a in
      "(" <> op `sp` enc <> ")"
    op2 op a b =
      let aenc = exprToSMT a
          benc = exprToSMT b in
      "(" <> op `sp` aenc `sp` benc <> ")"
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
copySlice srcOffset dstOffset size0@(Lit _) src dst =
  "(let ((src " <> src <> ")) " <> internal size0 <> ")"
  where
    internal (Lit 0) = dst
    internal size =
      let size' = (Expr.sub size (Lit 1))
          encDstOff = exprToSMT (Expr.add dstOffset size')
          encSrcOff = exprToSMT (Expr.add srcOffset size')
          child = internal size' in
      "(store " <> child `sp` encDstOff `sp` "(select src " <> encSrcOff <> "))"
copySlice _ _ _ _ _ = internalError "TODO: implement copySlice with a symbolically sized region"

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
          idxSMT = exprToSMT . Lit . unsafeInto $ idx
        in (idx + 1, "(store " <> inner `sp` idxSMT `sp` byteSMT <> ")")

encodeConcreteStore :: Map W256 W256 -> Builder
encodeConcreteStore s = foldl encodeWrite "((as const Storage) #x0000000000000000000000000000000000000000000000000000000000000000)" (Map.toList s)
  where
    encodeWrite prev (key, val) = let
        encKey = exprToSMT (Lit key)
        encVal = exprToSMT (Lit val)
      in "(store " <> prev `sp` encKey `sp` encVal <> ")"

storeName :: Expr EAddr -> Maybe W256 -> Builder
storeName a Nothing = fromString ("baseStore_") <> formatEAddr a
storeName a (Just idx) = fromString ("baseStore_") <> formatEAddr a <> "_" <> (fromString $ show idx)

formatEAddr :: Expr EAddr -> Builder
formatEAddr = \case
  LitAddr a -> fromString ("litaddr_" <> show a)
  SymAddr a -> fromText ("symaddr_" <> a)
  GVar _ -> internalError "Unexpected GVar"


-- ** Cex parsing ** --------------------------------------------------------------------------------

parseAddr :: SpecConstant -> Addr
parseAddr = parseSC

parseW256 :: SpecConstant -> W256
parseW256 = parseSC

parseInteger :: SpecConstant -> Integer
parseInteger = parseSC

parseW8 :: SpecConstant -> Word8
parseW8 = parseSC

parseSC :: (Num a, Eq a) => SpecConstant -> a
parseSC (SCHexadecimal a) = fst . head . Numeric.readHex . T.unpack . T.fromStrict $ a
parseSC (SCBinary a) = fst . head . Numeric.readBin . T.unpack . T.fromStrict $ a
parseSC sc = internalError $ "cannot parse: " <> show sc

parseErr :: (Show a) => a -> b
parseErr res = internalError $ "cannot parse solver response: " <> show res

parseVar :: TS.Text -> Expr EWord
parseVar = Var

parseEAddr :: TS.Text -> Expr EAddr
parseEAddr name
  | Just a <- TS.stripPrefix "litaddr_" name = LitAddr (read (TS.unpack a))
  | Just a <- TS.stripPrefix "symaddr_" name = SymAddr a
  | otherwise = internalError $ "cannot parse: " <> show name

parseBlockCtx :: TS.Text -> Expr EWord
parseBlockCtx "origin" = Origin
parseBlockCtx "coinbase" = Coinbase
parseBlockCtx "timestamp" = Timestamp
parseBlockCtx "blocknumber" = BlockNumber
parseBlockCtx "prevrandao" = PrevRandao
parseBlockCtx "gaslimit" = GasLimit
parseBlockCtx "chainid" = ChainId
parseBlockCtx "basefee" = BaseFee
parseBlockCtx t = internalError $ "cannot parse " <> (TS.unpack t) <> " into an Expr"

parseTxCtx :: TS.Text -> Expr EWord
parseTxCtx name
  | name == "txvalue" = TxValue
  | Just a <- TS.stripPrefix "balance_" name = Balance (parseEAddr a)
  | otherwise = internalError $ "cannot parse " <> (TS.unpack name) <> " into an Expr"

getAddrs :: (TS.Text -> Expr EAddr) -> (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr EAddr) Addr)
getAddrs parseName getVal names = Map.mapKeys parseName <$> foldM (getOne parseAddr getVal) mempty names

getVars :: (TS.Text -> Expr EWord) -> (Text -> IO Text) -> [TS.Text] -> IO (Map (Expr EWord) W256)
getVars parseName getVal names = Map.mapKeys parseName <$> foldM (getOne parseW256 getVal) mempty names

getOne :: (SpecConstant -> a) -> (Text -> IO Text) -> Map TS.Text a -> TS.Text -> IO (Map TS.Text a)
getOne parseVal getVal acc name = do
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
             then parseVal sc
             else internalError "solver did not return model for requested value"
      r -> parseErr r
  pure $ Map.insert name val acc

-- | Queries the solver for models for each of the expressions representing the
-- max read index for a given buffer
queryMaxReads :: (Text -> IO Text) -> Map Text (Expr EWord)  -> IO (Map Text W256)
queryMaxReads getVal maxReads = mapM (queryValue getVal) maxReads

-- | Gets the initial model for each buffer, these will often be much too large for our purposes
getBufs :: (Text -> IO Text) -> [Text] -> IO (Map (Expr Buf) BufModel)
getBufs getVal bufs = foldM getBuf mempty bufs
  where
    getLength :: Text -> IO W256
    getLength name = do
      val <- getVal (name <> "_length ")
      pure $ case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (parsed :| [])) -> case parsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), (TermSpecConstant sc))
            -> if symbol == (T.toStrict $ name <> "_length")
               then parseW256 sc
               else internalError "solver did not return model for requested value"
          res -> parseErr res
        res -> parseErr res

    getBuf :: Map (Expr Buf) BufModel -> Text -> IO (Map (Expr Buf) BufModel)
    getBuf acc name = do
      len <- getLength name
      val <- getVal name

      buf <- case parseCommentFreeFileMsg getValueRes (T.toStrict val) of
        Right (ResSpecific (valParsed :| [])) -> case valParsed of
          (TermQualIdentifier (Unqualified (IdSymbol symbol)), term)
            -> if (T.fromStrict symbol) == name
               then pure $ parseBuf len term
               else internalError "solver did not return model for requested value"
          res -> internalError $ "cannot parse solver response: " <> show res
        res -> internalError $ "cannot parse solver response: " <> show res
      pure $ Map.insert (AbstractBuf $ T.toStrict name) buf acc

    parseBuf :: W256 -> Term -> BufModel
    parseBuf len = Comp . go mempty
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
                 SCHexadecimal "00" -> Base 0 0
                 v -> Base (parseW8 v) len

          -- writing a byte over some array
          (TermApplication
            (Unqualified (IdSymbol "store"))
            (base :| [TermSpecConstant idx, TermSpecConstant val])
            ) -> let
              pbase = go env base
              pidx = parseW256 idx
              pval = parseW8 val
            in Write pval pidx pbase

          -- binding a new name
          (TermLet ((VarBinding name bound) :| []) term) -> let
              pbound = go env bound
            in go (Map.insert name pbound env) term

          -- looking up a bound name
          (TermQualIdentifier (Unqualified (IdSymbol name))) -> case Map.lookup name env of
            Just t -> t
            Nothing -> internalError $ "could not find "
                            <> (TS.unpack name)
                            <> " in environment mapping"
          p -> parseErr p

-- | Takes a Map containing all reads from a store with an abstract base, as
-- well as the concrete part of the storage prestate and returns a fully
-- concretized storage
getStore
  :: (Text -> IO Text)
  -> Map (Expr EAddr, Maybe W256) (Set (Expr EWord))
  -> IO (Map (Expr EAddr) (Map W256 W256))
getStore getVal abstractReads =
  fmap Map.fromList $ forM (Map.toList abstractReads) $ \((addr, idx), slots) -> do
    let name = toLazyText (storeName addr idx)
    raw <- getVal name
    let parsed = case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
                   Right (ResSpecific (valParsed :| [])) -> valParsed
                   r -> parseErr r
        -- first interpret SMT term as a function
        fun = case parsed of
                (TermQualIdentifier (Unqualified (IdSymbol symbol)), term) ->
                  if symbol == (T.toStrict name)
                  then interpret1DArray Map.empty term
                  else internalError "solver did not return model for requested value"
                r -> parseErr r

    -- then create a map by adding only the locations that are read by the program
    store <- foldM (\m slot -> do
      slot' <- queryValue getVal slot
      pure $ Map.insert slot' (fun slot') m) Map.empty slots
    pure (addr, store)

-- | Ask the solver to give us the concrete value of an arbitrary abstract word
queryValue :: (Text -> IO Text) -> Expr EWord -> IO W256
queryValue _ (Lit w) = pure w
queryValue getVal w = do
  let expr = toLazyText $ exprToSMT w
  raw <- getVal expr
  case parseCommentFreeFileMsg getValueRes (T.toStrict raw) of
    Right (ResSpecific (valParsed :| [])) ->
      case valParsed of
        (_, TermSpecConstant sc) -> pure $ parseW256 sc
        _ -> internalError $ "cannot parse model for: " <> show w
    r -> parseErr r

-- | Interpret an N-dimensional array as a value of type a.
-- Parameterized by an interpretation function for array values.
interpretNDArray :: (Map Symbol Term -> Term -> a) -> (Map Symbol Term) -> Term -> (W256 -> a)
interpretNDArray interp env = \case
  -- variable reference
  TermQualIdentifier (Unqualified (IdSymbol s)) ->
    case Map.lookup s env of
      Just t -> interpretNDArray interp env t
      Nothing -> internalError "unknown identifier, cannot parse array"
  -- (let (x t') t)
  TermLet (VarBinding x t' :| []) t -> interpretNDArray interp (Map.insert x t' env) t
  TermLet (VarBinding x t' :| lets) t -> interpretNDArray interp (Map.insert x t' env) (TermLet (NonEmpty.fromList lets) t)
  -- (as const (Array (_ BitVec 256) (_ BitVec 256))) SpecConstant
  TermApplication asconst (val :| []) | isArrConst asconst ->
    \_ -> interp env val
  -- (store arr ind val)
  TermApplication store (arr :| [TermSpecConstant ind, val]) | isStore store ->
    \x -> if x == parseW256 ind then interp env val else interpretNDArray interp env arr x
  t -> internalError $ "cannot parse array value. Unexpected term: " <> (show t)

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
        Nothing -> internalError "unknown identifier, cannot parse array"
    interpretW256 _ t = internalError $ "cannot parse array value. Unexpected term: " <> (show t)
