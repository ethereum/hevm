{-# Language DataKinds #-}

module EVM.SymExec where

import Prelude hiding (Word)

import Control.Lens hiding (pre)
import EVM hiding (Query, Revert, push)
import qualified EVM
import EVM.Exec
import qualified EVM.Fetch as Fetch
import EVM.ABI
import EVM.SMT
import EVM.Traversals
import qualified EVM.Expr as Expr
import EVM.Stepper (Stepper)
import qualified EVM.Stepper as Stepper
import qualified Control.Monad.Operational as Operational
import Control.Monad.State.Strict hiding (state)
import EVM.Types
import EVM.Concrete (createAddress)
import qualified EVM.FeeSchedule as FeeSchedule
import Data.DoubleWord (Word256)
import Control.Concurrent.Async
import Data.Maybe
import Data.List (foldl')
import Data.Tuple (swap)

import Data.ByteString (ByteString)
import qualified Control.Monad.State.Class as State
import Data.Bifunctor (first, second)
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Text.Lazy as TL
import qualified Data.Text.Lazy.IO as TL
import EVM.Format (formatExpr, indent, formatBinary)

data ProofResult a b c = Qed a | Cex b | Timeout c
  deriving (Show)
type VerifyResult = ProofResult () (Expr End, SMTCex) (Expr End)
type EquivalenceResult = ProofResult ([VM], [VM]) VM ()

isQed :: ProofResult a b c -> Bool
isQed (Qed _) = True
isQed _ = False

data VeriOpts = VeriOpts
  { simp :: Bool
  , debug :: Bool
  , maxIter :: Maybe Integer
  , askSmtIters :: Maybe Integer
  }
  deriving (Eq, Show)

defaultVeriOpts :: VeriOpts
defaultVeriOpts = VeriOpts { simp = True, debug = False, maxIter = Nothing, askSmtIters = Nothing }

debugVeriOpts :: VeriOpts
debugVeriOpts = VeriOpts { simp = True, debug = True, maxIter = Nothing, askSmtIters = Nothing }

extractCex :: VerifyResult -> Maybe (Expr End, SMTCex)
extractCex (Cex c) = Just c
extractCex _ = Nothing

inRange :: Int -> Expr EWord -> Prop
inRange sz e = PAnd (PGEq e (Lit 0)) (PLEq e (Lit $ 2 ^ sz - 1))

bool :: Expr EWord -> Prop
bool e = POr (PEq e (Lit 1)) (PEq e (Lit 0))

-- | Abstract calldata argument generation
symAbiArg :: Text -> AbiType -> CalldataFragment
symAbiArg name = \case
  AbiUIntType n ->
    if n `mod` 8 == 0 && n <= 256
    then let v = Var name in St [inRange n v] v
    else error "bad type"
  AbiIntType n ->
    if n `mod` 8 == 0 && n <= 256
    -- TODO: is this correct?
    then let v = Var name in St [inRange n v] v
    else error "bad type"
  AbiBoolType -> let v = Var name in St [bool v] v
  AbiAddressType -> let v = Var name in St [inRange 160 v] v
  AbiBytesType n
    -> if n > 0 && n <= 32
       then let v = Var name in St [inRange (n * 8) v] v
       else error "bad type"
  AbiArrayType sz tp -> Comp $ fmap (\n -> symAbiArg (name <> n) tp) [T.pack (show n) | n <- [0..sz-1]]
  t -> error $ "TODO: symbolic abi encoding for " <> show t

data CalldataFragment
  = St [Prop] (Expr EWord)
  | Dy [Prop] (Expr EWord) (Expr Buf)
  | Comp [CalldataFragment]
  deriving (Show, Eq)

-- | Generates calldata matching given type signature, optionally specialized
-- with concrete arguments.
-- Any argument given as "<symbolic>" or omitted at the tail of the list are
-- kept symbolic.
symCalldata :: Text -> [AbiType] -> [String] -> Expr Buf -> (Expr Buf, [Prop])
symCalldata sig typesignature concreteArgs base =
  let args = concreteArgs <> replicate (length typesignature - length concreteArgs)  "<symbolic>"
      mkArg :: AbiType -> String -> Int -> CalldataFragment
      mkArg typ "<symbolic>" n = symAbiArg (T.pack $ "arg" <> show n) typ
      mkArg typ arg _ = let v = makeAbiValue typ arg
                        in case v of
                             AbiUInt _ w -> St [] . Lit . num $ w
                             AbiInt _ w -> St [] . Lit . num $ w
                             AbiAddress w -> St [] . Lit . num $ w
                             AbiBool w -> St [] . Lit $ if w then 1 else 0
                             _ -> error "TODO"
      calldatas = zipWith3 mkArg typesignature args [1..]
      (cdBuf, props) = combineFragments calldatas base
      withSelector = writeSelector cdBuf sig
      sizeConstraints
        = (Expr.bufLength withSelector .>= cdLen calldatas)
        .&& (Expr.bufLength withSelector .< (Lit (2 ^ (64 :: Integer))))
  in (withSelector, sizeConstraints : props)

cdLen :: [CalldataFragment] -> Expr EWord
cdLen = go (Lit 4)
  where
    go acc = \case
      [] -> acc
      (hd:tl) -> case hd of
                   St _ _ -> go (Expr.add acc (Lit 32)) tl
                   _ -> error "unsupported"

writeSelector :: Expr Buf -> Text -> Expr Buf
writeSelector buf sig = writeSel (Lit 0) $ writeSel (Lit 1) $ writeSel (Lit 2) $ writeSel (Lit 3) buf
  where
    sel = ConcreteBuf $ selector sig
    writeSel idx = Expr.writeByte idx (Expr.readByte idx sel)

combineFragments :: [CalldataFragment] -> Expr Buf -> (Expr Buf, [Prop])
combineFragments fragments base = go (Lit 4) fragments (base, [])
  where
    go :: Expr EWord -> [CalldataFragment] -> (Expr Buf, [Prop]) -> (Expr Buf, [Prop])
    go _ [] acc = acc
    go idx (f:rest) (buf, ps) = case f of
                             St p w -> go (Expr.add idx (Lit 32)) rest (Expr.writeWord idx w buf, p <> ps)
                             s -> error $ "unsupported cd fragment: " <> show s


abstractVM :: Maybe (Text, [AbiType]) -> [String] -> ByteString -> Maybe Precondition -> StorageModel -> VM
abstractVM typesignature concreteArgs contractCode maybepre storagemodel = finalVm
  where
    (calldata', calldataProps) = case typesignature of
                 Nothing -> (AbstractBuf "txdata", [])
                 Just (name, typs) -> symCalldata name typs concreteArgs (AbstractBuf "txdata")
    store = case storagemodel of
              SymbolicS -> AbstractStore
              InitialS -> EmptyStore
              ConcreteS -> ConcreteStore mempty
    caller' = Caller 0
    value' = CallValue 0
    code' = RuntimeCode $ fromJust $ Expr.toList (ConcreteBuf contractCode)
    vm' = loadSymVM code' store caller' value' calldata' calldataProps
    precond = case maybepre of
                Nothing -> []
                Just p -> [p vm']
    finalVm = vm' & over constraints (<> precond)

loadSymVM :: ContractCode -> Expr Storage -> Expr EWord -> Expr EWord -> Expr Buf -> [Prop] -> VM
loadSymVM x initStore addr callvalue' calldata' calldataProps =
  (makeVm $ VMOpts
    { vmoptContract = initialContract x
    , vmoptCalldata = (calldata', calldataProps)
    , vmoptValue = callvalue'
    , vmoptStorageBase = Symbolic
    , vmoptAddress = createAddress ethrunAddress 1
    , vmoptCaller = addr
    , vmoptOrigin = ethrunAddress --todo: generalize
    , vmoptCoinbase = 0
    , vmoptNumber = 0
    , vmoptTimestamp = (Lit 0)
    , vmoptBlockGaslimit = 0
    , vmoptGasprice = 0
    , vmoptDifficulty = 0
    , vmoptGas = 0xffffffffffffffff
    , vmoptGaslimit = 0xffffffffffffffff
    , vmoptBaseFee = 0
    , vmoptPriorityFee = 0
    , vmoptMaxCodeSize = 0xffffffff
    , vmoptSchedule = FeeSchedule.berlin
    , vmoptChainId = 1
    , vmoptCreate = False
    , vmoptTxAccessList = mempty
    , vmoptAllowFFI = False
    }) & set (env . contracts . at (createAddress ethrunAddress 1))
             (Just (initialContract x))
       & set (env . EVM.storage) initStore

-- | Interpreter which explores all paths at branching points.
-- returns an Expr representing the possible executions
interpret
  :: Fetch.Fetcher
  -> Maybe Integer -- max iterations
  -> Maybe Integer -- ask smt iterations
  -> Stepper (Expr End)
  -> StateT VM IO (Expr End)
interpret fetcher maxIter askSmtIters =
  eval . Operational.view

  where
    eval
      :: Operational.ProgramView Stepper.Action (Expr End)
      -> StateT VM IO (Expr End)

    eval (Operational.Return x) = pure x

    eval (action Operational.:>>= k) =
      case action of
        Stepper.Exec ->
          exec >>= interpret fetcher maxIter askSmtIters . k
        Stepper.Run ->
          run >>= interpret fetcher maxIter askSmtIters . k
        Stepper.IOAct q ->
          mapStateT liftIO q >>= interpret fetcher maxIter askSmtIters . k
        Stepper.Ask (EVM.PleaseChoosePath cond continue) -> do
          assign result Nothing
          vm <- get
          case maxIterationsReached vm maxIter of
            -- TODO: parallelise
            Nothing -> do
              a <- interpret fetcher maxIter askSmtIters (Stepper.evm (continue True) >>= k)
              put vm
              b <- interpret fetcher maxIter askSmtIters (Stepper.evm (continue False) >>= k)
              return $ ITE cond a b
            Just n ->
              interpret fetcher maxIter askSmtIters (Stepper.evm (continue (not n)) >>= k)
        Stepper.Wait q -> do
          let performQuery = do
                m <- liftIO (fetcher q)
                interpret fetcher maxIter askSmtIters (Stepper.evm m >>= k)

          case q of
            PleaseAskSMT _ _ continue -> do
              codelocation <- getCodeLocation <$> get
              iteration <- num . fromMaybe 0 <$> use (iterations . at codelocation)

              -- if this is the first time we are branching at this point,
              -- explore both branches without consulting SMT.
              -- Exploring too many branches is a lot cheaper than
              -- consulting our SMT solver.
              if iteration < (fromMaybe 5 askSmtIters)
              then interpret fetcher maxIter askSmtIters (Stepper.evm (continue EVM.Unknown) >>= k)
              else performQuery

            _ -> performQuery

        Stepper.EVM m ->
          State.state (runState m) >>= interpret fetcher maxIter askSmtIters . k

maxIterationsReached :: VM -> Maybe Integer -> Maybe Bool
maxIterationsReached _ Nothing = Nothing
maxIterationsReached vm (Just maxIter) =
  let codelocation = getCodeLocation vm
      iters = view (iterations . at codelocation . non 0) vm
  in if num maxIter <= iters
     then view (cache . path . at (codelocation, iters - 1)) vm
     else Nothing


type Precondition = VM -> Prop
type Postcondition = VM -> Expr End -> Prop


checkAssert :: SolverGroup -> [Word256] -> ByteString -> Maybe (Text, [AbiType]) -> [String] -> VeriOpts -> IO (Expr End, [VerifyResult])
checkAssert solvers errs c signature' concreteArgs opts = verifyContract solvers c signature' concreteArgs opts SymbolicS Nothing (Just $ checkAssertions errs)

{- |Checks if an assertion violation has been encountered

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
checkAssertions :: [Word256] -> Postcondition
checkAssertions errs _ = \case
  Revert _ (ConcreteBuf msg) -> PBool $ msg `notElem` (fmap panicMsg errs)
  Revert _ b -> foldl' PAnd (PBool True) (fmap (PNeg . PEq b . ConcreteBuf . panicMsg) errs)
  _ -> PBool True

-- |By default hevm checks for all assertions except those which result from arithmetic overflow
defaultPanicCodes :: [Word256]
defaultPanicCodes = [ 0x00, 0x01, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51 ]

allPanicCodes :: [Word256]
allPanicCodes = [ 0x00, 0x01, 0x11, 0x12, 0x21, 0x22, 0x31, 0x32, 0x41, 0x51 ]

-- |Produces the revert message for solc >=0.8 assertion violations
panicMsg :: Word256 -> ByteString
panicMsg err = (selector "Panic(uint256)") <> (encodeAbiValue $ AbiUInt 256 err)

verifyContract :: SolverGroup -> ByteString -> Maybe (Text, [AbiType]) -> [String] -> VeriOpts -> StorageModel -> Maybe Precondition -> Maybe Postcondition -> IO (Expr End, [VerifyResult])
verifyContract solvers theCode signature' concreteArgs opts storagemodel maybepre maybepost = do
  let preState = abstractVM signature' concreteArgs theCode maybepre storagemodel
  verify solvers opts preState Nothing maybepost

pruneDeadPaths :: [VM] -> [VM]
pruneDeadPaths =
  filter $ \vm -> case view result vm of
    Just (VMFailure DeadPath) -> False
    _ -> True

-- | Stepper that parses the result of Stepper.runFully into an Expr End
runExpr :: Stepper.Stepper (Expr End)
runExpr = do
  vm <- Stepper.runFully
  let asserts = view keccakEqs vm
  pure $ case view result vm of
    Nothing -> error "Internal Error: vm in intermediate state after call to runFully"
    Just (VMSuccess buf) -> Return asserts buf (view (env . EVM.storage) vm)
    Just (VMFailure e) -> case e of
      UnrecognizedOpcode _ -> Invalid asserts
      SelfDestruction -> SelfDestruct asserts
      EVM.IllegalOverflow -> EVM.Types.IllegalOverflow asserts
      EVM.Revert buf -> EVM.Types.Revert asserts buf
      e' -> EVM.Types.TmpErr asserts $ show e'


-- | Converts a given top level expr into a list of final states and the associated path conditions for each state
flattenExpr :: Expr End -> [([Prop], Expr End)]
flattenExpr = go []
  where
    go :: [Prop] -> Expr End -> [([Prop], Expr End)]
    go pcs = \case
      ITE c t f -> go (PNeg ((PEq c (Lit 0))) : pcs) t <> go (PEq c (Lit 0) : pcs) f
      e@(Invalid _)  -> [(pcs, e)]
      e@(SelfDestruct _) -> [(pcs, e)]
      e@(Revert _ _) -> [(pcs, e)]
      e@(Return _ _ _) -> [(pcs, e)]
      e@(EVM.Types.IllegalOverflow _) -> [(pcs, e)]
      TmpErr _ s -> error s
      GVar _ -> error "cannot flatten an Expr containing a GVar"

-- | Strips unreachable branches from a given expr
-- Returns a list of executed SMT queries alongside the reduced expression for debugging purposes
-- Note that the reduced expression loses information relative to the original
-- one if jump conditions are removed. This restriction can be removed once
-- Expr supports attaching knowledge to AST nodes.
-- Although this algorithm currently parallelizes nicely, it does not exploit
-- the incremental nature of the task at hand. Introducing support for
-- incremental queries might let us go even faster here.
-- TODO: handle errors properly
reachable :: SolverGroup -> Expr End -> IO ([SMT2], Expr End)
reachable solvers e = do
    res <- go [] e
    pure $ second (fromMaybe (error "Internal Error: no reachable paths found")) res
  where
    {-
       Walk down the tree and collect pcs.
       Dispatch a reachability query at each leaf.
       If reachable return the expr wrapped in a Just. If not return Nothing.
       When walking back up the tree drop unreachable subbranches.
    -}
    go :: [Prop] -> Expr End -> IO ([SMT2], Maybe (Expr End))
    go pcs = \case
      ITE c t f -> do
        (tres, fres) <- concurrently
          (go (PEq (Lit 1) c : pcs) t)
          (go (PEq (Lit 0) c : pcs) f)
        let subexpr = case (snd tres, snd fres) of
              (Just t', Just f') -> Just $ ITE c t' f'
              (Just t', Nothing) -> Just t'
              (Nothing, Just f') -> Just f'
              (Nothing, Nothing) -> Nothing
        pure (fst tres <> fst fres, subexpr)
      leaf -> do
        let query = assertProps pcs
        res <- checkSat solvers query
        case res of
          Sat _ -> pure ([query], Just leaf)
          Unsat -> pure ([query], Nothing)
          r -> error $ "Invalid solver result: " <> show r

-- | Evaluate the provided proposition down to its most concrete result
evalProp :: Prop -> Prop
evalProp = \case
  o@(PBool _) -> o
  o@(PNeg p)  -> case p of
              (PBool b) -> PBool (not b)
              _ -> o
  o@(PEq l r) -> if l == r
                 then PBool True
                 else o
  o@(PLT (Lit l) (Lit r)) -> if l < r
                             then PBool True
                             else o
  o@(PGT (Lit l) (Lit r)) -> if l > r
                             then PBool True
                             else o
  o@(PGEq (Lit l) (Lit r)) -> if l >= r
                              then PBool True
                              else o
  o@(PLEq (Lit l) (Lit r)) -> if l <= r
                              then PBool True
                              else o
  o@(PAnd l r) -> case (evalProp l, evalProp r) of
                    (PBool True, PBool True) -> PBool True
                    (PBool _, PBool _) -> PBool False
                    _ -> o
  o@(POr l r) -> case (evalProp l, evalProp r) of
                   (PBool False, PBool False) -> PBool False
                   (PBool _, PBool _) -> PBool True
                   _ -> o
  o -> o


-- | Extract contraints stored in  Expr End nodes
extractProps :: Expr End -> [Prop]
extractProps = \case
  ITE _ _ _ -> []
  Invalid asserts -> asserts
  SelfDestruct asserts -> asserts
  Revert asserts _ -> asserts
  Return asserts _ _ -> asserts
  EVM.Types.IllegalOverflow asserts -> asserts
  TmpErr asserts _ -> asserts
  GVar _ -> error "cannot extract props from a GVar"


-- | Symbolically execute the VM and check all endstates against the postcondition, if available.
verify :: SolverGroup -> VeriOpts -> VM -> Maybe (Fetch.BlockNumber, Text) -> Maybe Postcondition -> IO (Expr End, [VerifyResult])
verify solvers opts preState rpcinfo maybepost = do
  putStrLn "Exploring contract"

  exprInter <- evalStateT (interpret (Fetch.oracle solvers rpcinfo) Nothing Nothing runExpr) preState
  when (debug opts) $ T.writeFile "unsimplified.expr" (formatExpr exprInter)

  putStrLn "Simplifying expression"
  expr <- if (simp opts) then (pure $ Expr.simplify exprInter) else pure exprInter
  when (debug opts) $ T.writeFile "simplified.expr" (formatExpr expr)

  putStrLn $ "Explored contract (" <> show (Expr.numBranches expr) <> " branches)"

  case maybepost of
    Nothing -> pure (expr, [Qed ()])
    Just post -> do
      let
        -- Filter out any leaves that can be statically shown to be safe
        canViolate = flip filter (flattenExpr expr) $
          \(_, leaf) -> case evalProp (post preState leaf) of
            PBool True -> False
            _ -> True
        assumes = view constraints preState
        withQueries = fmap (\(pcs, leaf) -> (assertProps (PNeg (post preState leaf) : assumes <> extractProps leaf <> pcs), leaf)) canViolate
      putStrLn $ "Checking for reachability of " <> show (length withQueries) <> " potential property violation(s)"

      when (debug opts) $ forM_ (zip [(1 :: Int)..] withQueries) $ \(idx, (q, leaf)) -> do
        TL.writeFile
          ("query-" <> show idx <> ".smt2")
          ("; " <> (TL.pack $ show leaf) <> "\n\n" <> formatSMT2 q <> "\n\n(check-sat)")

      -- Dispatch the remaining branches to the solver to check for violations
      results <- flip mapConcurrently withQueries $ \(query, leaf) -> do
        res <- checkSat solvers query
        pure (res, leaf)
      let cexs = filter (\(res, _) -> not . isUnsat $ res) results
      pure $ if null cexs then (expr, [Qed ()]) else (expr, fmap toVRes cexs)
  where
    toVRes :: (CheckSatResult, Expr End) -> VerifyResult
    toVRes (res, leaf) = case res of
      Sat model -> Cex (leaf, model)
      EVM.SMT.Unknown -> Timeout leaf
      Unsat -> Qed ()
      Error e -> error $ "Internal Error: solver responded with error: " <> show e

-- | Compares two contract runtimes for trace equivalence by running two VMs and comparing the end states.
equivalenceCheck :: ByteString -> ByteString -> Maybe Integer -> Maybe Integer -> Maybe (Text, [AbiType]) -> EquivalenceResult
equivalenceCheck bytecodeA bytecodeB maxiter askSmtIters signature' = undefined
  --let
    --bytecodeA' = if BS.null bytecodeA then BS.pack [0] else bytecodeA
    --bytecodeB' = if BS.null bytecodeB then BS.pack [0] else bytecodeB
  --preStateA <- abstractVM signature' [] bytecodeA' SymbolicS

  --let preself = preStateA ^. state . contract
      --precaller = preStateA ^. state . caller
      --callvalue' = preStateA ^. state . callvalue
      --prestorage = preStateA ^?! env . contracts . ix preself . storage
      --(calldata', cdlen) = view (state . calldata) preStateA
      --pathconds = view constraints preStateA
      --preStateB = loadSymVM (RuntimeCode (ConcreteBuffer bytecodeB')) prestorage SymbolicS precaller callvalue' (calldata', cdlen) & set constraints pathconds

  --smtState <- queryState
  --push 1
  --aVMs <- doInterpret (Fetch.oracle (Just smtState) Nothing False) maxiter askSmtIters preStateA
  --pop 1
  --push 1
  --bVMs <- doInterpret (Fetch.oracle (Just smtState) Nothing False) maxiter askSmtIters preStateB
  --pop 1
  ---- Check each pair of endstates for equality:
  --let differingEndStates = uncurry distinct <$> [(a,b) | a <- pruneDeadPaths (leaves aVMs), b <- pruneDeadPaths (leaves bVMs)]
      --distinct a b =
        --let (aPath, bPath) = both' (view constraints) (a, b)
            --(aSelf, bSelf) = both' (view (state . contract)) (a, b)
            --(aEnv, bEnv) = both' (view (env . contracts)) (a, b)
            --(aResult, bResult) = both' (view result) (a, b)
            ----(Symbolic _ aStorage, Symbolic _ bStorage) = (view storage (aEnv ^?! ix aSelf), view storage (bEnv ^?! ix bSelf))
            --differingResults = case (aResult, bResult) of

              --(Just (VMSuccess aOut), Just (VMSuccess bOut)) ->
                --aOut ./= bOut .|| aStorage ./= bStorage .|| fromBool (aSelf /= bSelf)

              --(Just (VMFailure UnexpectedSymbolicArg), _) ->
                --error $ "Unexpected symbolic argument at opcode: " <> maybe "??" show (vmOp a) <> ". Not supported (yet!)"

              --(_, Just (VMFailure UnexpectedSymbolicArg)) ->
                --error $ "Unexpected symbolic argument at opcode: " <> maybe "??" show (vmOp a) <> ". Not supported (yet!)"

              --(Just (VMFailure _), Just (VMFailure _)) -> sFalse

              --(Just _, Just _) -> sTrue

              --errormsg -> error $ show errormsg

        --in sAnd (fst <$> aPath) .&& sAnd (fst <$> bPath) .&& differingResults
  ---- If there exists a pair of endstates where this is not the case,
  ---- the following constraint is satisfiable
  --constrain $ sOr differingEndStates

  --checkSat >>= \case
     --Unk -> return $ Timeout ()
     --Sat -> return $ Cex preStateA
     --Unsat -> return $ Qed (leaves aVMs, leaves bVMs)
     --DSat _ -> error "unexpected DSAT"

both' :: (a -> b) -> (a, a) -> (b, b)
both' f (x, y) = (f x, f y)

produceModels :: SolverGroup -> Expr End -> IO [(Expr End, CheckSatResult)]
produceModels solvers expr = do
  let flattened = flattenExpr expr
      withQueries = fmap (first assertProps) flattened
  results <- flip mapConcurrently withQueries $ \(query, leaf) -> do
    res <- checkSat solvers query
    pure (res, leaf)
  pure $ fmap swap $ filter (\(res, _) -> not . isUnsat $ res) results

showModel :: Expr Buf -> (Expr End, CheckSatResult) -> IO ()
showModel cd (expr, res) = do
  case res of
    Unsat -> pure () -- ignore unreachable branches
    Error e -> error $ "Internal error: smt solver returned an error: " <> show e
    EVM.SMT.Unknown -> do
      putStrLn "--- Branch ---"
      putStrLn ""
      putStrLn "Unable to produce a model for the following end state:"
      putStrLn ""
      T.putStrLn $ indent 2 $ formatExpr expr
      putStrLn ""
    Sat cex -> do
      putStrLn "--- Branch ---"
      putStrLn ""
      putStrLn "Inputs:"
      putStrLn ""
      T.putStrLn $ indent 2 $ formatCex cd cex
      putStrLn ""
      putStrLn "End State:"
      putStrLn ""
      T.putStrLn $ indent 2 $ formatExpr expr
      putStrLn ""


formatCex :: Expr Buf -> SMTCex -> Text
formatCex cd m@(SMTCex _ _ blockContext txContext) = T.unlines $
  [ "Calldata:"
  , indent 2 cd'
  , ""
  ]
  <> txCtx
  <> blockCtx
  where
    cd' = prettyBuf $ Expr.simplify $ subModel m cd

    txCtx :: [Text]
    txCtx
      | Map.null txContext = []
      | otherwise =
        [ "Transaction Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc -> (showTxCtx key <> ": " <> (T.pack $ show val)) : acc) mempty (filterSubCtx txContext)
        , ""
        ]

    -- strips the frame arg from frame context vars to make them easier to read
    showTxCtx :: Expr EWord -> Text
    showTxCtx (CallValue _) = "CallValue"
    showTxCtx (Caller _) = "Caller"
    showTxCtx (Address _) = "Address"
    showTxCtx x = T.pack $ show x

    -- strips all frame context that doesn't come from the top frame
    filterSubCtx :: Map (Expr EWord) W256 -> Map (Expr EWord) W256
    filterSubCtx = Map.filterWithKey go
      where
        go :: Expr EWord -> W256 -> Bool
        go (CallValue x) _ = x == 0
        go (Caller x) _ = x == 0
        go (Address x) _ = x == 0
        go (Balance {}) _ = error "TODO: BALANCE"
        go (SelfBalance {}) _ = error "TODO: SELFBALANCE"
        go (Gas {}) _ = error "TODO: Gas"
        go _ _ = False

    blockCtx :: [Text]
    blockCtx
      | Map.null blockContext = []
      | otherwise =
        [ "Block Context:"
        , indent 2 $ T.unlines $ Map.foldrWithKey (\key val acc -> (T.pack $ show key <> ": " <> show val) : acc) mempty txContext
        , ""
        ]

    prettyBuf :: Expr Buf -> Text
    prettyBuf (ConcreteBuf "") = "Empty"
    prettyBuf (ConcreteBuf bs) = formatBinary bs
    prettyBuf _ = "Any"

-- | Takes a buffer and a Cex and replaces all abstract values in the buf with concrete ones from the Cex
subModel :: SMTCex -> Expr a -> Expr a
subModel c expr = subBufs (buffers c) . subVars (vars c) $ expr
  where
    subVars model b = Map.foldlWithKey subVar b model
    subVar :: Expr a -> Expr EWord -> W256 -> Expr a
    subVar b var val = mapExpr go b
      where
        go :: Expr a -> Expr a
        go = \case
          v@(Var _) -> if v == var
                      then Lit val
                      else v
          e -> e
    subBufs model b = Map.foldlWithKey subBuf b model
    subBuf :: Expr a -> Expr Buf -> ByteString -> Expr a
    subBuf b var val = mapExpr go b
      where
        go :: Expr a -> Expr a
        go = \case
          a@(AbstractBuf _) -> if a == var
                      then ConcreteBuf val
                      else a
          e -> e
