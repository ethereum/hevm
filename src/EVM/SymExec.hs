{-# LANGUAGE DeriveAnyClass #-}

module EVM.SymExec where

import Control.Concurrent.Async (concurrently, mapConcurrently)
import Control.Concurrent.Spawn (parMapIO, pool)
import Control.Concurrent.STM (TVar, readTVarIO, newTVarIO)
import Control.Monad (when, forM_, forM)
import Control.Monad.IO.Unlift
import Control.Monad.Operational qualified as Operational
import Control.Monad.ST (RealWorld, stToIO, ST)
import Control.Monad.State.Strict (runStateT)
import Data.Bifunctor (second, first)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.Containers.ListUtils (nubOrd)
import Data.DoubleWord (Word256)
import Data.List (foldl', sortBy, sort)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, mapMaybe, listToMaybe)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Map.Merge.Strict qualified as Map
import Data.Set (Set, isSubsetOf, size)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Tree.Zipper qualified as Zipper
import Data.Tuple (swap)
import Data.Vector qualified as V
import Data.Vector.Unboxed qualified as VUnboxed
import EVM (makeVm, abstractContract, initialContract, getCodeLocation, isValidJumpDest)
import EVM.Exec
import EVM.Fetch qualified as Fetch
import EVM.ABI
import EVM.Effects
import EVM.Expr qualified as Expr
import EVM.FeeSchedule (feeSchedule)
import EVM.Format (formatExpr, formatPartial, formatPartialShort, showVal, indent, formatBinary, formatProp)
import EVM.SMT (SMTCex(..), SMT2(..), assertProps)
import EVM.SMT qualified as SMT
import EVM.Solvers
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.Traversals
import EVM.Types
import EVM.Expr (maybeConcStoreSimp)
import GHC.Conc (getNumProcessors)
import GHC.Generics (Generic)
import Optics.Core
import Options.Generic (ParseField, ParseFields, ParseRecord)
import Text.Printf (printf)
import Witch (into, unsafeInto)

data LoopHeuristic
  = Naive
  | StackBased
  deriving (Eq, Show, Read, ParseField, ParseFields, ParseRecord, Generic)

data ProofResult a b c d = Qed a | Cex b | Unknown c | Error d
  deriving (Show, Eq)
type VerifyResult = ProofResult () (Expr End, SMTCex) (Expr End) String
type EquivResult = ProofResult () (SMTCex) () String

isUnknown :: ProofResult a b c d -> Bool
isUnknown (EVM.SymExec.Unknown _) = True
isUnknown _ = False

isError :: ProofResult a b c d -> Bool
isError (EVM.SymExec.Error _) = True
isError _ = False

getError :: ProofResult a b c String -> Maybe String
getError (EVM.SymExec.Error e) = Just e
getError _ = Nothing

isCex :: ProofResult a b c d -> Bool
isCex (Cex _) = True
isCex _ = False

isQed :: ProofResult a b c d -> Bool
isQed (Qed _) = True
isQed _ = False

groupIssues :: [ProofResult a b c String] -> [(Integer, String)]
groupIssues results = map (\g -> (into (length g), NE.head g)) grouped
  where
    getErr :: ProofResult a b c String -> String
    getErr (EVM.SymExec.Error k) = k
    getErr (EVM.SymExec.Unknown _) = "SMT result timeout/unknown"
    getErr _ = internalError "shouldn't happen"
    sorted = sort $ map getErr results
    grouped = NE.group sorted

groupPartials :: [Expr End] -> [(Integer, String)]
groupPartials e = map (\g -> (into (length g), NE.head g)) grouped
  where
    getErr :: Expr End -> String
    getErr (Partial _ _ reason) = T.unpack $ formatPartialShort reason
    getErr _ = internalError "shouldn't happen"
    sorted = sort $ map getErr (filter isPartial e)
    grouped = NE.group sorted

data VeriOpts = VeriOpts
  { simp :: Bool
  , maxIter :: Maybe Integer
  , askSmtIters :: Integer
  , loopHeuristic :: LoopHeuristic
  , rpcInfo :: Fetch.RpcInfo
  }
  deriving (Eq, Show)

defaultVeriOpts :: VeriOpts
defaultVeriOpts = VeriOpts
  { simp = True
  , maxIter = Nothing
  , askSmtIters = 1
  , loopHeuristic = StackBased
  , rpcInfo = Nothing
  }

rpcVeriOpts :: (Fetch.BlockNumber, Text) -> VeriOpts
rpcVeriOpts info = defaultVeriOpts { rpcInfo = Just info }

extractCex :: VerifyResult -> Maybe (Expr End, SMTCex)
extractCex (Cex c) = Just c
extractCex _ = Nothing

bool :: Expr EWord -> Prop
bool e = POr (PEq (Lit 1) e) (PEq (Lit 0) e)

-- | Abstract calldata argument generation
symAbiArg :: Text -> AbiType -> CalldataFragment
symAbiArg name = \case
  AbiUIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then St [Expr.inRange n v] v
    else internalError "bad type"
  AbiIntType n ->
    if n `mod` 8 == 0 && n <= 256
    -- TODO: is this correct?
    then St [Expr.inRange n v] v
    else internalError "bad type"
  AbiBoolType -> St [bool v] v
  AbiAddressType -> St [] (WAddr (SymAddr name))
  AbiBytesType n ->
    if n > 0 && n <= 32
    then St [Expr.inRange (n * 8) v] v
    else internalError "bad type"
  AbiArrayType sz tps -> do
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg (name <> "-a-" <> i) tp) $ (V.replicate sz tps)
  AbiTupleType tps ->
    Comp . V.toList . V.imap (\(T.pack . show -> i) tp -> symAbiArg (name <> "-t-" <> i) tp) $ tps
  t -> internalError $ "TODO: symbolic abi encoding for " <> show t
  where
    v = Var name

data CalldataFragment
  = St [Prop] (Expr EWord)
  | Dy [Prop] (Expr EWord) (Expr Buf)
  | Comp [CalldataFragment]
  deriving (Show, Eq)

-- | Generates calldata matching given type signature, optionally specialized
-- with concrete arguments.
-- Any argument given as "<symbolic>" or omitted at the tail of the list are
-- kept symbolic.
symCalldata :: App m => Text -> [AbiType] -> [String] -> Expr Buf -> m (Expr Buf, [Prop])
symCalldata sig typesignature concreteArgs base = do
  conf <- readConfig
  let
    args = concreteArgs <> replicate (length typesignature - length concreteArgs) "<symbolic>"
    mkArg :: AbiType -> String -> Int -> CalldataFragment
    mkArg typ "<symbolic>" n = symAbiArg (T.pack $ "arg" <> show n) typ
    mkArg typ arg _ =
      case makeAbiValue typ arg of
        AbiUInt _ w -> St [] . Lit . into $ w
        AbiInt _ w -> St [] . Lit . unsafeInto $ w
        AbiAddress w -> St [] . Lit . into $ w
        AbiBool w -> St [] . Lit $ if w then 1 else 0
        _ -> internalError "TODO"
    calldatas = zipWith3 mkArg typesignature args [1..]
    (cdBuf, props) = combineFragments calldatas base
    withSelector = writeSelector cdBuf sig
    sizeConstraints
      = (Expr.bufLength withSelector .>= cdLen calldatas)
      .&& (Expr.bufLength withSelector .< (Lit (2 ^ conf.maxBufSize)))
  pure (withSelector, sizeConstraints : props)

cdLen :: [CalldataFragment] -> Expr EWord
cdLen = go (Lit 4)
  where
    go acc = \case
      [] -> acc
      (hd:tl) -> case hd of
                   St _ _ -> go (Expr.add acc (Lit 32)) tl
                   Comp xs | all isSt xs -> go acc (xs <> tl)
                   _ -> internalError "unsupported"

writeSelector :: Expr Buf -> Text -> Expr Buf
writeSelector buf sig =
  writeSel (Lit 0) $ writeSel (Lit 1) $ writeSel (Lit 2) $ writeSel (Lit 3) buf
  where
    sel = ConcreteBuf $ selector sig
    writeSel idx = Expr.writeByte idx (Expr.readByte idx sel)

combineFragments :: [CalldataFragment] -> Expr Buf -> (Expr Buf, [Prop])
combineFragments fragments base = go (Lit 4) fragments (base, [])
  where
    go :: Expr EWord -> [CalldataFragment] -> (Expr Buf, [Prop]) -> (Expr Buf, [Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) =
      case f of
        -- static fragments get written as a word in place
        St p w -> go (Expr.add idx (Lit 32)) rest (Expr.writeWord idx w buf, p <> ps)
        -- compound fragments that contain only static fragments get written in place
        Comp xs | all isSt xs -> go idx (xs <> rest) (buf,ps)
        -- dynamic fragments are not yet supported... :/
        s -> internalError $ "unsupported cd fragment: " <> show s

isSt :: CalldataFragment -> Bool
isSt (St {}) = True
isSt (Comp fs) = all isSt fs
isSt _ = False


abstractVM
  :: (Expr Buf, [Prop])
  -> ByteString
  -> Maybe (Precondition s)
  -> Bool
  -> ST s (VM Symbolic s)
abstractVM cd contractCode maybepre create = do
  let value = TxValue
  let code = if create then InitCode contractCode (fst cd) else RuntimeCode (ConcreteRuntimeCode contractCode)
  vm <- loadSymVM code value (if create then mempty else cd) create
  let precond = case maybepre of
                Nothing -> []
                Just p -> [p vm]
  pure $ vm & over #constraints (<> precond)

loadSymVM
  :: ContractCode
  -> Expr EWord
  -> (Expr Buf, [Prop])
  -> Bool
  -> ST s (VM Symbolic s)
loadSymVM x callvalue cd create =
  (makeVm $ VMOpts
    { contract = if create then initialContract x else abstractContract x (SymAddr "entrypoint")
    , otherContracts = []
    , calldata = cd
    , value = callvalue
    , baseState = AbstractBase
    , address = SymAddr "entrypoint"
    , caller = SymAddr "caller"
    , origin = SymAddr "origin"
    , coinbase = SymAddr "coinbase"
    , number = 0
    , timestamp = Lit 0
    , blockGaslimit = 0
    , gasprice = 0
    , prevRandao = 42069
    , gas = ()
    , gaslimit = 0xffffffffffffffff
    , baseFee = 0
    , priorityFee = 0
    , maxCodeSize = 0xffffffff
    , schedule = feeSchedule
    , chainId = 1
    , create = create
    , txAccessList = mempty
    , allowFFI = False
    , freshAddresses = 0
    , beaconRoot = 0
    })

-- freezes any mutable refs, making it safe to share between threads
freezeVM :: VM Symbolic RealWorld -> ST RealWorld (VM Symbolic RealWorld)
freezeVM vm = do
    state' <- do
      mem' <- freeze (vm.state.memory)
      pure $ vm.state { memory = mem' }
    frames' <- forM (vm.frames :: [Frame Symbolic RealWorld]) $ \frame -> do
      mem' <- freeze frame.state.memory
      pure $ (frame :: Frame Symbolic RealWorld) { state = frame.state { memory = mem' } }

    pure (vm :: VM Symbolic RealWorld)
      { state = state'
      , frames = frames'
      }
  where
    freeze = \case
      ConcreteMemory m -> SymbolicMemory . ConcreteBuf . BS.pack . VUnboxed.toList <$> VUnboxed.freeze m
      m@(SymbolicMemory _) -> pure m

-- | Interpreter which explores all paths at branching points. Returns an
-- 'Expr End' representing the possible executions.
interpret
  :: forall m . App m
  => Fetch.Fetcher Symbolic m RealWorld
  -> Maybe Integer -- max iterations
  -> Integer -- ask smt iterations
  -> LoopHeuristic
  -> VM Symbolic RealWorld
  -> Stepper Symbolic RealWorld (Expr End)
  -> m (Expr End)
interpret fetcher maxIter askSmtIters heuristic vm =
  eval . Operational.view
  where
  eval
    :: Operational.ProgramView (Stepper.Action Symbolic RealWorld) (Expr End)
    -> m (Expr End)

  eval (Operational.Return x) = pure x

  eval (action Operational.:>>= k) =
    case action of
      Stepper.Exec -> do
        conf <- readConfig
        (r, vm') <- liftIO $ stToIO $ runStateT (exec conf) vm
        interpret fetcher maxIter askSmtIters heuristic vm' (k r)
      Stepper.Fork (PleaseRunBoth cond continue) -> do
        frozen <- liftIO $ stToIO $ freezeVM vm
        evalLeft <- toIO $ do
          (ra, vma) <- liftIO $ stToIO $ runStateT (continue True) frozen { result = Nothing }
          interpret fetcher maxIter askSmtIters heuristic vma (k ra)
        evalRight <- toIO $ do
          (rb, vmb) <- liftIO $ stToIO $ runStateT (continue False) frozen { result = Nothing }
          interpret fetcher maxIter askSmtIters heuristic vmb (k rb)
        (a, b) <- liftIO $ concurrently evalLeft evalRight
        pure $ ITE cond a b
      Stepper.Wait q -> do
        let performQuery = do
              m <- fetcher q
              (r, vm') <- liftIO$ stToIO $ runStateT m vm
              interpret fetcher maxIter askSmtIters heuristic vm' (k r)

        case q of
          PleaseAskSMT cond preconds continue -> do
            let
              -- no concretiziation here, or we may lose information
              simpProps = Expr.simplifyProps ((cond ./= Lit 0):preconds)
            case Expr.concKeccakSimpExpr cond of
              -- is the condition concrete?
              Lit c ->
                -- have we reached max iterations, are we inside a loop?
                case (maxIterationsReached vm maxIter, isLoopHead heuristic vm) of
                  -- Yes. return a partial leaf
                  (Just _, Just True) ->
                    pure $ Partial [] (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) $ MaxIterationsReached vm.state.pc vm.state.contract
                  -- No. keep executing
                  _ -> do
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case (c > 0))) vm
                    interpret fetcher maxIter askSmtIters heuristic vm' (k r)

              -- the condition is symbolic
              _ ->
                -- are in we a loop, have we hit maxIters, have we hit askSmtIters?
                case (isLoopHead heuristic vm, askSmtItersReached vm askSmtIters, maxIterationsReached vm maxIter) of
                  -- we're in a loop and maxIters has been reached
                  (Just True, _, Just n) -> do
                    -- continue execution down the opposite branch than the one that
                    -- got us to this point and return a partial leaf for the other side
                    (r, vm') <- liftIO $ stToIO $ runStateT (continue (Case $ not n)) vm
                    a <- interpret fetcher maxIter askSmtIters heuristic vm' (k r)
                    pure $ ITE cond a (Partial [] (TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels) (MaxIterationsReached vm.state.pc vm.state.contract))
                  -- we're in a loop and askSmtIters has been reached
                  (Just True, True, _) ->
                    -- ask the smt solver about the loop condition
                    performQuery
                  _ -> do
                    (r, vm') <- case simpProps of
                      -- if we can statically determine unsatisfiability then we skip exploring the jump
                      [PBool False] -> liftIO $ stToIO $ runStateT (continue (Case False)) vm
                      -- otherwise we explore both branches
                      _ -> liftIO $ stToIO $ runStateT (continue EVM.Types.Unknown) vm
                    interpret fetcher maxIter askSmtIters heuristic vm' (k r)
          _ -> performQuery

      Stepper.EVM m -> do
        (r, vm') <- liftIO $ stToIO $ runStateT m vm
        interpret fetcher maxIter askSmtIters heuristic vm' (k r)

maxIterationsReached :: VM Symbolic s -> Maybe Integer -> Maybe Bool
maxIterationsReached _ Nothing = Nothing
maxIterationsReached vm (Just maxIter) =
  let codelocation = getCodeLocation vm
      (iters, _) = view (at codelocation % non (0, [])) vm.iterations
  in if unsafeInto maxIter <= iters
     then Map.lookup (codelocation, iters - 1) vm.cache.path
     else Nothing

askSmtItersReached :: VM Symbolic s -> Integer -> Bool
askSmtItersReached vm askSmtIters = let
    codelocation = getCodeLocation vm
    (iters, _) = view (at codelocation % non (0, [])) vm.iterations
  in askSmtIters <= into iters

{- | Loop head detection heuristic

 The main thing we wish to differentiate between, are actual loop heads, and branch points inside of internal functions that are called multiple times.

 One way to do this is to observe that for internal functions, the compiler must always store a stack item representing the location that it must jump back to. If we compare the stack at the time of the previous visit, and the time of the current visit, and notice that this location has changed, then we can guess that the location is a jump point within an internal function instead of a loop (where such locations should be constant between iterations).

 This heuristic is not perfect, and can certainly be tricked, but should generally be good enough for most compiler generated and non pathological user generated loops.
 -}
isLoopHead :: LoopHeuristic -> VM Symbolic s -> Maybe Bool
isLoopHead Naive _ = Just True
isLoopHead StackBased vm = let
    loc = getCodeLocation vm
    oldIters = Map.lookup loc vm.iterations
    isValid (Lit wrd) = wrd <= unsafeInto (maxBound :: Int) && isValidJumpDest vm (unsafeInto wrd)
    isValid _ = False
  in case oldIters of
       Just (_, oldStack) -> Just $ filter isValid oldStack == filter isValid vm.state.stack
       Nothing -> Nothing

type Precondition s = VM Symbolic s -> Prop
type Postcondition s = VM Symbolic s -> Expr End -> Prop

checkAssert
  :: App m
  => SolverGroup
  -> [Word256]
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> m (Expr End, [VerifyResult])
checkAssert solvers errs c signature' concreteArgs opts =
  verifyContract solvers c signature' concreteArgs opts Nothing (Just $ checkAssertions errs)

getExpr
  :: App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> m (Expr End)
getExpr solvers c signature' concreteArgs opts = do
      calldata <- mkCalldata signature' concreteArgs
      preState <- liftIO $ stToIO $ abstractVM calldata c Nothing False
      exprInter <- interpret (Fetch.oracle solvers opts.rpcInfo) opts.maxIter opts.askSmtIters opts.loopHeuristic preState runExpr
      if opts.simp then (pure $ Expr.simplify exprInter) else pure exprInter

{- | Checks if an assertion violation has been encountered

  hevm recognises the following as an assertion violation:

  1. the invalid opcode (0xfe) (solc < 0.8)
  2. a revert with a reason of the form `abi.encodeWithSelector("Panic(uint256)", code)`, where code is one of the following (solc >= 0.8):
    - 0x00: Used for generic compiler inserted panics.
    - 0x01: If you call assert with an argument that evaluates to false.
    - 0x11: If an arithmetic operation results in underflow or overflow outside of an unchecked { ... } block.
    - 0x12; If you divide or modulo by zero (e.g. 5 / 0 or 23 % 0).
    - 0x21: If you convert a value that is too big or negative into an enum type.
    - 0x22: If you access a storage byte array that is incorrectly encoded.
    - 0x31: If you call .pop() on an empty array.
    - 0x32: If you access an array, bytesN or an array slice at an out-of-bounds or negative index (i.e. x[i] where i >= x.length or i < 0).
    - 0x41: If you allocate too much memory or create an array that is too large.
    - 0x51: If you call a zero-initialized variable of internal function type.

  see: https://docs.soliditylang.org/en/v0.8.6/control-structures.html?highlight=Panic#panic-via-assert-and-error-via-require
-}
checkAssertions :: [Word256] -> Postcondition s
checkAssertions errs _ = \case
  Failure _ _ (Revert (ConcreteBuf msg)) -> PBool $ msg `notElem` (fmap panicMsg errs)
  Failure _ _ (Revert b) -> foldl' PAnd (PBool True) (fmap (PNeg . PEq b . ConcreteBuf . panicMsg) errs)
  _ -> PBool True

-- | By default hevm only checks for user-defined assertions
defaultPanicCodes :: [Word256]
defaultPanicCodes = [0x01]

allPanicCodes :: [Word256]
allPanicCodes = [0x00, 0x01, 0x11, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51]

-- | Produces the revert message for solc >=0.8 assertion violations
panicMsg :: Word256 -> ByteString
panicMsg err = selector "Panic(uint256)" <> encodeAbiValue (AbiUInt 256 err)

-- | Builds a buffer representing calldata from the provided method description
-- and concrete arguments
mkCalldata :: App m => Maybe Sig -> [String] -> m (Expr Buf, [Prop])
mkCalldata Nothing _ = do
  conf <- readConfig
  pure ( AbstractBuf "txdata"
       -- assert that the length of the calldata is never more than 2^64
       -- this is way larger than would ever be allowed by the gas limit
       -- and avoids spurious counterexamples during abi decoding
       -- TODO: can we encode calldata as an array with a smaller length?
       , [Expr.bufLength (AbstractBuf "txdata") .< (Lit (2 ^ conf.maxBufSize))]
       )
mkCalldata (Just (Sig name types)) args =
  symCalldata name types args (AbstractBuf "txdata")

verifyContract
  :: App m
  => SolverGroup
  -> ByteString
  -> Maybe Sig
  -> [String]
  -> VeriOpts
  -> Maybe (Precondition RealWorld)
  -> Maybe (Postcondition RealWorld)
  -> m (Expr End, [VerifyResult])
verifyContract solvers theCode signature' concreteArgs opts maybepre maybepost = do
  calldata <- mkCalldata signature' concreteArgs
  preState <- liftIO $ stToIO $ abstractVM calldata theCode maybepre False
  verify solvers opts preState maybepost

-- | Stepper that parses the result of Stepper.runFully into an Expr End
runExpr :: Stepper.Stepper Symbolic RealWorld (Expr End)
runExpr = do
  vm <- Stepper.runFully
  let traces = TraceContext (Zipper.toForest vm.traces) vm.env.contracts vm.labels
  pure $ case vm.result of
    Just (VMSuccess buf) -> Success vm.constraints traces buf (fmap toEContract vm.env.contracts)
    Just (VMFailure e)   -> Failure vm.constraints traces e
    Just (Unfinished p)  -> Partial vm.constraints traces p
    _ -> internalError "vm in intermediate state after call to runFully"

toEContract :: Contract -> Expr EContract
toEContract c = C c.code c.storage c.tStorage c.balance c.nonce

-- | Converts a given top level expr into a list of final states and the
-- associated path conditions for each state.
flattenExpr :: Expr End -> [Expr End]
flattenExpr = go []
  where
    go :: [Prop] -> Expr End -> [Expr End]
    go pcs = \case
      ITE c t f -> go (PNeg ((PEq (Lit 0) c)) : pcs) t <> go (PEq (Lit 0) c : pcs) f
      Success ps trace msg store -> [Success (nubOrd $ ps <> pcs) trace msg store]
      Failure ps trace e -> [Failure (nubOrd $ ps <> pcs) trace e]
      Partial ps trace p -> [Partial (nubOrd $ ps <> pcs) trace p]
      GVar _ -> internalError "cannot flatten an Expr containing a GVar"

-- | Strips unreachable branches from a given expr
-- Returns a list of executed SMT queries alongside the reduced expression for debugging purposes
-- Note that the reduced expression loses information relative to the original
-- one if jump conditions are removed. This restriction can be removed once
-- Expr supports attaching knowledge to AST nodes.
-- Although this algorithm currently parallelizes nicely, it does not exploit
-- the incremental nature of the task at hand. Introducing support for
-- incremental queries might let us go even faster here.
-- TODO: handle errors properly
reachable :: App m => SolverGroup -> Expr End -> m ([SMT2], Expr End)
reachable solvers e = do
  res <- go [] e
  pure $ second (fromMaybe (internalError "no reachable paths found")) res
  where
    {-
       Walk down the tree and collect pcs.
       Dispatch a reachability query at each leaf.
       If reachable return the expr wrapped in a Just. If not return Nothing.
       When walking back up the tree drop unreachable subbranches.
    -}
    go :: (App m, MonadUnliftIO m) => [Prop] -> Expr End -> m ([SMT2], Maybe (Expr End))
    go pcs = \case
      ITE c t f -> do
        (tres, fres) <- withRunInIO $ \env -> concurrently
          (env $ go (PEq (Lit 1) c : pcs) t)
          (env $ go (PEq (Lit 0) c : pcs) f)
        let subexpr = case (snd tres, snd fres) of
              (Just t', Just f') -> Just $ ITE c t' f'
              (Just t', Nothing) -> Just t'
              (Nothing, Just f') -> Just f'
              (Nothing, Nothing) -> Nothing
        pure (fst tres <> fst fres, subexpr)
      leaf -> do
        (res, smt2) <- checkSatWithProps solvers pcs
        case res of
          Sat _ -> pure ([getNonError smt2], Just leaf)
          Unsat -> pure ([getNonError smt2], Nothing)
          r -> internalError $ "Invalid solver result: " <> show r

-- | Extract constraints stored in Expr End nodes
extractProps :: Expr End -> [Prop]
extractProps = \case
  ITE _ _ _ -> []
  Success asserts _ _ _ -> asserts
  Failure asserts _ _ -> asserts
  Partial asserts _ _ -> asserts
  GVar _ -> internalError "cannot extract props from a GVar"

extractEndStates :: Expr End -> Map (Expr EAddr) (Expr EContract)
extractEndStates = \case
  ITE {} -> mempty
  Success _ _ _ contr -> contr
  Failure {} -> mempty
  Partial  {} -> mempty
  GVar _ -> internalError "cannot extract props from a GVar"

isPartial :: Expr a -> Bool
isPartial (Partial _ _ _) = True
isPartial _ = False

printPartialIssues :: [Expr End] -> String -> IO ()
printPartialIssues flattened call =
  when (any isPartial flattened) $ do
    T.putStrLn $ indent 3 "\x1b[33m[WARNING]\x1b[0m: hevm was only able to partially explore "
                <> T.pack call <> " due to the following issue(s):"
    T.putStr . T.unlines . fmap (indent 5 . ("- " <>)) . fmap formatPartial . getPartials $ flattened

getPartials :: [Expr End] -> [PartialExec]
getPartials = mapMaybe go
  where
    go :: Expr End -> Maybe PartialExec
    go = \case
      Partial _ _ p -> Just p
      _ -> Nothing

-- | Symbolically execute the VM and check all endstates against the
-- postcondition, if available.
verify
  :: App m
  => SolverGroup
  -> VeriOpts
  -> VM Symbolic RealWorld
  -> Maybe (Postcondition RealWorld)
  -> m (Expr End, [VerifyResult])
verify solvers opts preState maybepost = do
  conf <- readConfig
  let call = mconcat ["prefix 0x", getCallPrefix preState.state.calldata]
  when conf.debug $ liftIO $ putStrLn $ "   Exploring call " <> call

  exprInter <- interpret (Fetch.oracle solvers opts.rpcInfo) opts.maxIter opts.askSmtIters opts.loopHeuristic preState runExpr
  when conf.dumpExprs $ liftIO $ T.writeFile "unsimplified.expr" (formatExpr exprInter)
  liftIO $ do
    when conf.debug $ putStrLn "   Simplifying expression"
    let expr = if opts.simp then (Expr.simplify exprInter) else exprInter
    when conf.dumpExprs $ T.writeFile "simplified.expr" (formatExpr expr)
    let flattened = flattenExpr expr
    when conf.debug $ do
      printPartialIssues flattened ("the call " <> call)
      putStrLn $ "   Exploration finished, " <> show (Expr.numBranches expr) <> " branch(es) to check in call " <> call

    case maybepost of
      Nothing -> pure (expr, [Qed ()])
      Just post -> liftIO $ do
        let
          -- Filter out any leaves from `flattened` that can be statically shown to be safe
          tocheck = flip map flattened $ \leaf -> (toPropsFinal leaf preState.constraints post, leaf)
          withQueries = filter canBeSat tocheck <&> first (assertProps conf)
        when conf.debug $
          putStrLn $ "   Checking for reachability of " <> show (length withQueries)
                     <> " potential property violation(s) in call " <> call

        -- Dispatch the remaining branches to the solver to check for violations
        results <- flip mapConcurrently withQueries $ \(query, leaf) -> do
          res <- checkSat solvers query
          when conf.debug $ putStrLn $ "   SMT result: " <> show res
          pure (res, leaf)
        let cexs = filter (\(res, _) -> not . isUnsat $ res) results
        when conf.debug $ putStrLn $ "   Found " <> show (length cexs) <> " potential counterexample(s) in call " <> call
        pure $ if Prelude.null cexs then (expr, [Qed ()]) else (expr, fmap toVRes cexs)
  where
    getCallPrefix :: Expr Buf -> String
    getCallPrefix (WriteByte (Lit 0) (LitByte a) (WriteByte (Lit 1) (LitByte b) (WriteByte (Lit 2) (LitByte c) (WriteByte (Lit 3) (LitByte d) _)))) = mconcat $ map (printf "%02x") [a,b,c,d]
    getCallPrefix _ = "unknown"
    toProps leaf constr post = PNeg (post preState leaf) : constr <> extractProps leaf
    toPropsFinal leaf constr post = if opts.simp then Expr.simplifyProps $ toProps leaf constr post
                                                 else toProps leaf constr post
    canBeSat (a, _) = case a of
        [PBool False] -> False
        _ -> True
    toVRes :: (CheckSatResult, Expr End) -> VerifyResult
    toVRes (res, leaf) = case res of
      Sat model -> Cex (leaf, expandCex preState model)
      EVM.Solvers.Unknown _ -> EVM.SymExec.Unknown leaf
      EVM.Solvers.Error e -> EVM.SymExec.Error e
      Unsat -> Qed ()

expandCex :: VM Symbolic s -> SMTCex -> SMTCex
expandCex prestate c = c { store = Map.union c.store concretePreStore }
  where
    concretePreStore = Map.mapMaybe (maybeConcStoreSimp . (.storage))
                     . Map.filter (\v -> Expr.containsNode isConcreteStore v.storage)
                     $ (prestate.env.contracts)
    isConcreteStore = \case
      ConcreteStore _ -> True
      _ -> False

type UnsatCache = TVar [Set Prop]

-- | Compares two contract runtimes for trace equivalence by running two VMs
-- and comparing the end states.
--
-- We do this by asking the solver to find a common input for each pair of
-- endstates that satisfies the path conditions for both sides and produces a
-- differing output. If we can find such an input, then we have a clear
-- equivalence break, and since we run this check for every pair of end states,
-- the check is exhaustive.
equivalenceCheck
  :: forall m . App m
  => SolverGroup
  -> ByteString
  -> ByteString
  -> VeriOpts
  -> (Expr Buf, [Prop])
  -> Bool
  -> m ([EquivResult], [Expr End])
equivalenceCheck solvers bytecodeA bytecodeB opts calldata create = do
  conf <- readConfig
  case bytecodeA == bytecodeB of
    True -> liftIO $ do
      putStrLn "bytecodeA and bytecodeB are identical"
      pure ([Qed ()], mempty)
    False -> do
      when conf.debug $ liftIO $ do
        putStrLn "bytecodeA and bytecodeB are different, checking for equivalence"
      branchesAorig <- getBranches bytecodeA
      branchesBorig <- getBranches bytecodeB
      when conf.debug $ liftIO $ do
        liftIO $ putStrLn $ "branchesA props: " <> show (map extractProps branchesAorig)
        liftIO $ putStrLn $ "branchesB props: " <> show (map extractProps branchesBorig)
        liftIO $ putStrLn ""
        liftIO $ putStrLn $ "branchesA endstates: " <> show (map extractEndStates branchesAorig)

        liftIO $ putStrLn $ "branchesB endstates: " <> show (map extractEndStates branchesBorig)
      let branchesA = rewriteFresh "A-" branchesAorig
          branchesB = rewriteFresh "B-" branchesBorig
      (res, ends) <- equivalenceCheck' solvers branchesA branchesB create
      pure (res, branchesA <> branchesB <> ends)
  where
    -- decompiles the given bytecode into a list of branches
    getBranches :: ByteString -> m [Expr End]
    getBranches bs = do
      let bytecode = if BS.null bs then BS.pack [0] else bs
      prestate <- liftIO $ stToIO $ abstractVM calldata bytecode Nothing create
      expr <- interpret (Fetch.oracle solvers Nothing) opts.maxIter opts.askSmtIters opts.loopHeuristic prestate runExpr
      let simpl = if opts.simp then (Expr.simplify expr) else expr
      pure $ flattenExpr simpl

rewriteFresh :: Text -> [Expr a] -> [Expr a]
rewriteFresh prefix exprs = fmap (mapExpr mymap) exprs
  where
    mymap :: Expr a -> Expr a
    mymap = \case
      Gas p x -> Gas (prefix <> p) x
      Var name | ("-fresh-" `T.isInfixOf` name) -> Var $ prefix <> name
      AbstractBuf name | ("-fresh-" `T.isInfixOf` name) -> AbstractBuf $ prefix <> name
      x -> x

equivalenceCheck'
  :: forall m . App m
  => SolverGroup -> [Expr End] -> [Expr End] -> Bool -> m ([EquivResult], [Expr End])
equivalenceCheck' solvers branchesA branchesB create = do
      conf <- readConfig
      when conf.debug $ do
        liftIO $ printPartialIssues branchesA "codeA"
        liftIO $ printPartialIssues branchesB "codeB"

      let allPairs = [(a,b) | a <- branchesA, b <- branchesB]
      liftIO $ putStrLn $ "Found " <> show (length allPairs) <> " total pairs of endstates"

      when conf.dumpEndStates $ liftIO $
        putStrLn $ "endstates in bytecodeA: " <> show (length branchesA)
                   <> "\nendstates in bytecodeB: " <> show (length branchesB)

      disctictPairs <- forM allPairs $ uncurry distinct
      let differingEndStates = sortBySize $ mapMaybe (view _1) disctictPairs
          deployedCexes = concatMap (view _2) disctictPairs
          ends = concatMap (view _3) disctictPairs
      liftIO $ putStrLn $ "Asking the SMT solver for " <> (show $ length differingEndStates) <> " pairs"
      when conf.dumpEndStates $ forM_ (zip differingEndStates [(1::Integer)..]) (\(x, i) ->
        liftIO $ T.writeFile ("prop-checked-" <> show i <> ".prop") (T.pack $ show x))

      knownUnsat <- liftIO $ newTVarIO []
      procs <- liftIO getNumProcessors
      cexes <- checkAll differingEndStates knownUnsat procs
      let allCexes = cexes <> deployedCexes
      if all isQed allCexes then pure ([Qed ()], ends)
                            else pure (filter (Prelude.not . isQed) allCexes, ends)
  where
    -- we order the sets by size because this gives us more cache hits when
    -- running our queries later on (since we rely on a subset check)
    sortBySize :: [Set a] -> [Set a]
    sortBySize = sortBy (\a b -> if size a > size b then Prelude.LT else Prelude.GT)

    -- returns True if a is a subset of any of the sets in b
    subsetAny :: Set Prop -> [Set Prop] -> Bool
    subsetAny a b = foldr (\bp acc -> acc || isSubsetOf a bp) False b

    -- checks for satisfiability of all the props in the provided set. skips
    -- the solver if we can determine unsatisfiability from the cache already
    -- the last element of the returned tuple indicates whether the cache was
    -- used or not
    check :: App m => UnsatCache -> Set Prop -> m EquivResult
    check knownUnsat props = do
      ku <- liftIO $ readTVarIO knownUnsat
      res <- if subsetAny props ku then pure Unsat
             else do
               (res, _) <- checkSatWithProps solvers (Set.toList props)
               pure res
      case res of
        Sat x -> pure $ Cex x
        Unsat -> pure $ Qed ()
        EVM.Solvers.Unknown _ -> pure $ EVM.SymExec.Unknown ()
        EVM.Solvers.Error txt -> pure $ EVM.SymExec.Error txt

    -- Allows us to run it in parallel. Note that this (seems to) run it
    -- from left-to-right, and with a max of K threads. This is in contrast to
    -- mapConcurrently which would spawn as many threads as there are jobs, and
    -- run them in a random order. We ordered them correctly, though so that'd be bad
    checkAll :: (App m, MonadUnliftIO m) => [(Set Prop)] -> UnsatCache -> Int -> m [EquivResult]
    checkAll input cache numproc = withRunInIO $ \env -> do
       wrap <- pool numproc
       parMapIO (\e -> wrap (env $ check cache e)) input

    -- Takes two branches and returns a set of props that will need to be
    -- satisfied for the two branches to violate the equivalence check. i.e.
    -- for a given pair of branches, equivalence is violated if there exists an
    -- input that satisfies the branch conditions from both sides and produces
    -- a differing result in each branch
    distinct :: App m => Expr End -> Expr End -> m (Maybe (Set Prop), [EquivResult], [Expr End])
    distinct aEnd bEnd = do
      (props, res, ends) <- resultsDiffer aEnd bEnd
      case props of
        -- if the end states are the same, then they can never produce a
        -- different result under any circumstances
        PBool False -> pure (Nothing, mempty, mempty)
        -- if we can statically determine that the end states differ, then we
        -- ask the solver to find us inputs that satisfy both sets of branch
        -- conditions
        PBool True  -> pure (Just . Set.fromList $ extractProps aEnd <> extractProps bEnd, res, ends)
        -- if we cannot statically determine whether or not the end states
        -- differ, then we ask the solver if the end states can differ if both
        -- sets of path conditions are satisfiable
        _ -> do
          pure (Just . Set.fromList $ props : extractProps aEnd <> extractProps bEnd, res, ends)

    resultsDiffer :: App m => Expr End -> Expr End -> m (Prop, [EquivResult], [Expr End])
    resultsDiffer aEnd bEnd = case (aEnd, bEnd) of
      (Success aProps _ aOut aState, Success bProps _ bOut bState) ->
        case (aOut == bOut, aState == bState) of
          (True, True) -> pure (PBool False, mempty, mempty)
          (True, False) -> pure (statesDiffer aState bState, mempty, mempty)
          (False, _) -> do
            (outDiff, res, ends) <-
              if create then checkCreatedDiff aOut bOut aProps bProps
              else pure (aOut ./= bOut, mempty, mempty)
            pure (statesDiffer aState bState .|| outDiff, res, ends)
      (Failure _ _ (Revert a), Failure _ _ (Revert b)) ->
        pure $ if a == b then (PBool False, mempty, mempty) else (a ./= b, mempty, mempty)
      (Failure _ _ a, Failure _ _ b) ->
        let lhs =  if a == b then PBool False else PBool True
        in pure (lhs, mempty, mempty)
      -- partial end states can't be compared to actual end states, so we always ignore them
      (Partial {}, _) -> pure (PBool False, mempty, mempty)
      (_, Partial {}) -> pure (PBool False, mempty, mempty)
      (ITE _ _ _, _) -> internalError "Expressions must be flattened"
      (_, ITE _ _ _) -> internalError "Expressions must be flattened"
      (a, b) -> pure (PBool (a /= b), mempty, mempty)

    -- If the original check was for create (i.e. undeployed code), then we must also check that the deployed
    -- code is equivalent. The constraints from the undeployed code (aProps,bProps) influence this check.
    checkCreatedDiff aOut bOut aProps bProps = do
      let simpA = Expr.simplify aOut
          simpB = Expr.simplify bOut
      case (simpA, simpB) of
        (ConcreteBuf codeA, ConcreteBuf codeB) -> do
          -- TODO: use aProps/bProps to constrain the deployed code
          --       since symbolic code (with constructors taking arguments) is not supported,
          --       this is currently not necessary
          conf <- readConfig
          when conf.debug $ liftIO $ do
            liftIO $ putStrLn $ "create deployed code A: " <> bsToHex codeA
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp aProps)
            liftIO $ putStrLn $ "create deployed code B: " <> bsToHex codeB
              <> " with constraints: " <> (T.unpack . T.unlines $ map formatProp bProps)
          calldata <- mkCalldata Nothing []
          (res, ends) <- equivalenceCheck solvers codeA codeB defaultVeriOpts calldata False
          pure (PBool False, res, ends)
        _ -> internalError $ "Symbolic code returned from constructor." <> " A: " <> show simpA <> " B: " <> show simpB

    statesDiffer :: Map (Expr EAddr) (Expr EContract) -> Map (Expr EAddr) (Expr EContract) -> Prop
    statesDiffer aState bState =
      case aState == bState of
        True -> PBool False
        False ->  if Set.fromList (Map.keys aState) /= Set.fromList (Map.keys bState)
          -- TODO: consider possibility of aliased symbolic addresses
          then PBool True
          else let
            merged = (Map.merge Map.dropMissing Map.dropMissing (Map.zipWithMatched (\_ x y -> (x,y))) aState bState)
          in Map.foldl' (\a (ac, bc) -> a .|| contractsDiffer ac bc) (PBool False) merged

    contractsDiffer :: Expr EContract -> Expr EContract -> Prop
    contractsDiffer ac bc = let
        balsDiffer = case (ac.balance, bc.balance) of
          (Lit ab, Lit bb) -> PBool $ ab /= bb
          (ab, bb) -> if ab == bb then PBool False else ab ./= bb
        -- TODO: is this sound? do we need a more sophisticated nonce representation?
        noncesDiffer = PBool (ac.nonce /= bc.nonce)
        storesDiffer = case (ac.storage, bc.storage) of
          (ConcreteStore as, ConcreteStore bs) | not (as == Map.empty || bs == Map.empty) -> PBool $ as /= bs
          (as, bs) -> if as == bs then PBool False else as ./= bs
      in balsDiffer .|| storesDiffer .|| noncesDiffer


both' :: (a -> b) -> (a, a) -> (b, b)
both' f (x, y) = (f x, f y)

produceModels :: App m => SolverGroup -> Expr End -> m [(Expr End, CheckSatResult)]
produceModels solvers expr = do
  let flattened = flattenExpr expr
      withQueries conf = fmap (\e -> ((assertProps conf) . extractProps $ e, e)) flattened
  conf <- readConfig
  results <- liftIO $ (flip mapConcurrently) (withQueries conf) $ \(query, leaf) -> do
    res <- checkSat solvers query
    pure (res, leaf)
  pure $ fmap swap $ filter (\(res, _) -> not . isUnsat $ res) results

showModel :: Expr Buf -> (Expr End, CheckSatResult) -> IO ()
showModel cd (expr, res) = do
  case res of
    EVM.Solvers.Unsat -> pure () -- ignore unreachable branches
    EVM.Solvers.Error e -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Error during SMT solving, cannot check branch " <> e
    EVM.Solvers.Unknown reason -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn $ "Unable to produce a model for the following end state due to '" <> reason <> "' :"
      T.putStrLn $ indent 2 $ formatExpr expr
      putStrLn ""
    Sat cex -> do
      putStrLn ""
      putStrLn "--- Branch ---"
      putStrLn "Inputs:"
      T.putStrLn $ indent 2 $ formatCex cd Nothing cex
      putStrLn "End State:"
      T.putStrLn $ indent 2 $ formatExpr expr


formatCex :: Expr Buf -> Maybe Sig -> SMTCex -> Text
formatCex cd sig m@(SMTCex _ addrs _ store blockContext txContext) = T.unlines $
  [ "Calldata:"
  , indent 2 cd'
  ]
  <> storeCex
  <> txCtx
  <> blockCtx
  <> addrsCex
  where
    -- we attempt to produce a model for calldata by substituting all variables
    -- and buffers provided by the model into the original calldata expression.
    -- If we have a concrete result then we display it, otherwise we display
    -- `Any`. This is a little bit of a hack (and maybe unsound?), but we need
    -- it for branches that do not refer to calldata at all (e.g. the top level
    -- callvalue check inserted by solidity in contracts that don't have any
    -- payable functions).
    cd' = case sig of
      Nothing -> prettyBuf . Expr.concKeccakSimpExpr . defaultSymbolicValues $ subModel m cd
      Just (Sig n ts) -> prettyCalldata m cd n ts

    storeCex :: [Text]
    storeCex
      | Map.null store = []
      | otherwise =
          [ "Storage:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ("Addr " <> (T.pack . show $ key)
                <> ": " <> (T.pack $ show (Map.toList val))) : acc
            ) mempty store
          ]

    txCtx :: [Text]
    txCtx
      | Map.null txContext = []
      | otherwise =
        [ "Transaction Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (showTxCtx key <> ": " <> (T.pack $ show val)) : acc
          ) mempty (filterSubCtx txContext)
        ]

    addrsCex :: [Text]
    addrsCex
      | Map.null addrs = []
      | otherwise =
          [ "Addrs:"
          , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
              ((T.pack . show $ key) <> ": " <> (T.pack $ show val)) : acc
            ) mempty addrs
          ]

    -- strips the frame arg from frame context vars to make them easier to read
    showTxCtx :: Expr EWord -> Text
    showTxCtx (TxValue) = "TxValue"
    showTxCtx x = T.pack $ show x

    -- strips all frame context that doesn't come from the top frame
    filterSubCtx :: Map (Expr EWord) W256 -> Map (Expr EWord) W256
    filterSubCtx = Map.filterWithKey go
      where
        go :: Expr EWord -> W256 -> Bool
        go (TxValue) _ = True
        go (Balance {}) _ = internalError "TODO: BALANCE"
        go (Gas {}) _ = internalError "TODO: Gas"
        go _ _ = False

    blockCtx :: [Text]
    blockCtx
      | Map.null blockContext = []
      | otherwise =
        [ "Block Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc ->
            (T.pack $ show key <> ": " <> show val) : acc
          ) mempty txContext
        ]

prettyBuf :: Expr Buf -> Text
prettyBuf (ConcreteBuf "") = "Empty"
prettyBuf (ConcreteBuf bs) = formatBinary bs
prettyBuf b = internalError $ "Unexpected symbolic buffer:\n" <> T.unpack (formatExpr b)

prettyCalldata :: SMTCex -> Expr Buf -> Text -> [AbiType] -> Text
prettyCalldata cex buf sig types = headErr errSig (T.splitOn "(" sig) <> "(" <> body <> ")"
  where
    argdata = Expr.drop 4 . Expr.simplify . defaultSymbolicValues $ subModel cex buf
    body = case decodeBuf types argdata of
      CAbi v -> T.intercalate "," (fmap showVal v)
      NoVals -> case argdata of
          ConcreteBuf c -> T.pack (bsToHex c)
          _ -> err
      SAbi _ -> err
    headErr e l = fromMaybe e $ listToMaybe l
    err = internalError $ "unable to produce a concrete model for calldata: " <> show buf
    errSig = internalError $ "unable to split sig: " <> show sig

-- | If the expression contains any symbolic values, default them to some
-- concrete value The intuition here is that if we still have symbolic values
-- in our calldata expression after substituting in our cex, then they can have
-- any value and we can safely pick a random value. This is a bit unsatisfying,
-- we should really be doing smth like: https://github.com/ethereum/hevm/issues/334
-- but it's probably good enough for now
defaultSymbolicValues :: Expr a -> Expr a
defaultSymbolicValues e = subBufs (foldTerm symbufs mempty e)
                        . subVars (foldTerm symwords mempty e)
                        . subAddrs (foldTerm symaddrs mempty e) $ e
  where
    symaddrs :: Expr a -> Map (Expr EAddr) Addr
    symaddrs = \case
      a@(SymAddr _) -> Map.singleton a (Addr 0x1312)
      _ -> mempty
    symbufs :: Expr a -> Map (Expr Buf) ByteString
    symbufs = \case
      a@(AbstractBuf _) -> Map.singleton a ""
      _ -> mempty
    symwords :: Expr a -> Map (Expr EWord) W256
    symwords = \case
      a@(Var _) -> Map.singleton a 0
      a@Origin -> Map.singleton a 0
      a@Coinbase -> Map.singleton a 0
      a@Timestamp -> Map.singleton a 0
      a@BlockNumber -> Map.singleton a 0
      a@PrevRandao -> Map.singleton a 0
      a@GasLimit -> Map.singleton a 0
      a@ChainId -> Map.singleton a 0
      a@BaseFee -> Map.singleton a 0
      _ -> mempty

-- | Takes an expression and a Cex and replaces all abstract values in the buf with
-- concrete ones from the Cex.
subModel :: SMTCex -> Expr a -> Expr a
subModel c
  = subBufs (fmap forceFlattened c.buffers)
  . subStores c.store
  . subVars c.vars
  . subVars c.blockContext
  . subVars c.txContext
  . subAddrs c.addrs
  where
    forceFlattened (SMT.Flat bs) = bs
    forceFlattened b@(SMT.Comp _) = forceFlattened $
      fromMaybe (internalError $ "cannot flatten buffer: " <> show b)
                (SMT.collapse b)

subVars :: Map (Expr EWord) W256 -> Expr a -> Expr a
subVars model b = Map.foldlWithKey subVar b model
  where
    subVar :: Expr a -> Expr EWord -> W256 -> Expr a
    subVar a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(Var _) -> if v == var
                      then Lit val
                      else v
          e -> e

subAddrs :: Map (Expr EAddr) Addr -> Expr a -> Expr a
subAddrs model b = Map.foldlWithKey subAddr b model
  where
    subAddr :: Expr a -> Expr EAddr -> Addr -> Expr a
    subAddr a var val = mapExpr go a
      where
        go :: Expr a -> Expr a
        go = \case
          v@(SymAddr _) -> if v == var
                      then LitAddr val
                      else v
          e -> e

subBufs :: Map (Expr Buf) ByteString -> Expr a -> Expr a
subBufs model b = Map.foldlWithKey subBuf b model
  where
    subBuf :: Expr a -> Expr Buf -> ByteString -> Expr a
    subBuf x var val = mapExpr go x
      where
        go :: Expr a -> Expr a
        go = \case
          a@(AbstractBuf _) -> if a == var
                      then ConcreteBuf val
                      else a
          e -> e

subStores :: Map (Expr EAddr) (Map W256 W256) -> Expr a -> Expr a
subStores model b = Map.foldlWithKey subStore b model
  where
    subStore :: Expr a -> Expr EAddr -> Map W256 W256 -> Expr a
    subStore x var val = mapExpr go x
      where
        go :: Expr a -> Expr a
        go = \case
          v@(AbstractStore a _)
            -> if a == var
               then ConcreteStore val
               else v
          e -> e

getCex :: ProofResult a b c d -> Maybe b
getCex (Cex c) = Just c
getCex _ = Nothing

getUnknown :: ProofResult a b c d-> Maybe c
getUnknown (EVM.SymExec.Unknown c) = Just c
getUnknown _ = Nothing
