{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TemplateHaskell #-}

module EVM.TTY where

import Brick
import Brick.Widgets.Border
import Brick.Widgets.Center
import Brick.Widgets.List
import Control.Lens hiding (List)
import Control.Monad.Operational qualified as Operational
import Control.Monad.State.Strict hiding (state)
import Data.Aeson.Lens
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.List (find, sort)
import Data.Map (Map, filter, insert, lookupLT, singleton)
import Data.Map qualified as Map
import Data.Maybe (fromJust, fromMaybe, isJust, isNothing)
import Data.Text (Text, pack)
import Data.Text qualified as T
import Data.Text qualified as Text
import Data.Text.Encoding (decodeUtf8)
import Data.Vector qualified as Vec
import Data.Vector.Storable qualified as SVec
import Data.Version (showVersion)
import EVM
import EVM.ABI (AbiType (..), abiTypeSolidity, decodeAbiValue, emptyAbi)
import EVM.Dapp (DappInfo (..), Test (..), dappInfo, extractSig, srcMap, unitTestMethods)
import EVM.Debug
import EVM.Expr (simplify)
import EVM.Fetch (Fetcher)
import EVM.Fetch qualified as Fetch
import EVM.Format
  ( contractNamePart,
    contractPathPart,
    formatExpr,
    prettyIfConcreteWord,
    showTraceTree,
    showWordExact,
    showWordExplanation,
  )
import EVM.Hexdump (prettyHex)
import EVM.Op
import EVM.Solidity hiding (storageLayout)
import EVM.Solvers (SolverGroup)
import EVM.Stepper (Stepper)
import EVM.Stepper qualified as Stepper
import EVM.StorageLayout
import EVM.SymExec (maxIterationsReached, symCalldata)
import EVM.TTYCenteredList qualified as Centered
import EVM.Types hiding (padRight)
import EVM.UnitTest
import Graphics.Vty qualified as V
import Paths_hevm qualified as Paths
import System.Console.Haskeline qualified as Readline
import Text.Wrap
import Prelude hiding (Word, lookup)

data Name
  = AbiPane
  | StackPane
  | BytecodePane
  | TracePane
  | SolidityPane
  | TestPickerPane
  | BrowserPane
  | Pager
  deriving (Eq, Show, Ord)

type UiWidget = Widget Name

data UiVmState = UiVmState
  { _uiVm :: VM,
    _uiStep :: Int,
    _uiSnapshots :: Map Int (VM, Stepper ()),
    _uiStepper :: Stepper (),
    _uiShowMemory :: Bool,
    _uiTestOpts :: UnitTestOptions
  }

data UiTestPickerState = UiTestPickerState
  { _testPickerList :: List Name (Text, Text),
    _testPickerDapp :: DappInfo,
    _testOpts :: UnitTestOptions
  }

data UiBrowserState = UiBrowserState
  { _browserContractList :: List Name (Addr, Contract),
    _browserVm :: UiVmState
  }

data UiState
  = ViewVm UiVmState
  | ViewContracts UiBrowserState
  | ViewPicker UiTestPickerState
  | ViewHelp UiVmState

makeLenses ''UiVmState
makeLenses ''UiTestPickerState
makeLenses ''UiBrowserState
makePrisms ''UiState

-- caching VM states lets us backstep efficiently
snapshotInterval :: Int
snapshotInterval = 50

type Pred a = a -> Bool

data StepMode
  = -- | Run a specific number of steps
    Step !Int
  | -- | Finish when a VM predicate holds
    StepUntil (Pred VM)

-- | Each step command in the terminal should finish immediately
-- with one of these outcomes.
data Continuation a
  = -- | Program finished
    Stopped a
  | -- | Took one step; more steps to go
    Continue (Stepper a)

-- | This turns a @Stepper@ into a state action usable
-- from within the TTY loop, yielding a @StepOutcome@ depending on the @StepMode@.
interpret ::
  ( ?fetcher :: Fetcher,
    ?maxIter :: Maybe Integer
  ) =>
  StepMode ->
  Stepper a ->
  StateT UiVmState IO (Continuation a)
interpret mode =
  -- Like the similar interpreters in @EVM.UnitTest@ and @EVM.VMTest@,
  -- this one is implemented as an "operational monad interpreter".

  eval . Operational.view
  where
    eval ::
      Operational.ProgramView Stepper.Action a ->
      StateT UiVmState IO (Continuation a)

    eval (Operational.Return x) =
      pure (Stopped x)
    eval (action Operational.:>>= k) =
      case action of
        Stepper.Run -> do
          -- Have we reached the final result of this action?
          use (uiVm . result) >>= \case
            Just _ -> do
              -- Yes, proceed with the next action.
              vm <- use uiVm
              interpret mode (k vm)
            Nothing -> do
              -- No, keep performing the current action
              keepExecuting mode (Stepper.run >>= k)

        -- Stepper wants to keep executing?
        Stepper.Exec -> do
          -- Have we reached the final result of this action?
          use (uiVm . result) >>= \case
            Just r ->
              -- Yes, proceed with the next action.
              interpret mode (k r)
            Nothing -> do
              -- No, keep performing the current action
              keepExecuting mode (Stepper.exec >>= k)

        -- Stepper is waiting for user input from a query
        Stepper.Ask (PleaseChoosePath _ cont) -> do
          -- ensure we aren't stepping past max iterations
          vm <- use uiVm
          case maxIterationsReached vm ?maxIter of
            Nothing -> pure $ Continue (k ())
            Just n -> interpret mode (Stepper.evm (cont (not n)) >>= k)

        -- Stepper wants to make a query and wait for the results?
        Stepper.Wait q -> do
          do
            m <- liftIO (?fetcher q)
            interpret mode (Stepper.evm m >>= k)

        -- Stepper wants to make a query and wait for the results?
        Stepper.IOAct q -> do
          Brick.zoom uiVm (StateT (runStateT q)) >>= interpret mode . k

        -- Stepper wants to modify the VM.
        Stepper.EVM m -> do
          vm <- use uiVm
          let (r, vm1) = runState m vm
          assign uiVm vm1
          interpret mode (Stepper.exec >> (k r))

keepExecuting ::
  ( ?fetcher :: Fetcher,
    ?maxIter :: Maybe Integer
  ) =>
  StepMode ->
  Stepper a ->
  StateT UiVmState IO (Continuation a)
keepExecuting mode restart = case mode of
  Step 0 -> do
    -- We come here when we've continued while stepping,
    -- either from a query or from a return;
    -- we should pause here and wait for the user.
    pure (Continue restart)
  Step i -> do
    -- Run one instruction and recurse
    stepOneOpcode restart
    interpret (Step (i - 1)) restart
  StepUntil p -> do
    vm <- use uiVm
    if p vm
      then interpret (Step 0) restart
      else do
        -- Run one instruction and recurse
        stepOneOpcode restart
        interpret (StepUntil p) restart

isUnitTestContract :: Text -> DappInfo -> Bool
isUnitTestContract name dapp =
  elem name (map fst dapp.unitTests)

mkVty :: IO V.Vty
mkVty = do
  vty <- V.mkVty V.defaultConfig
  V.setMode (V.outputIface vty) V.BracketedPaste True
  return vty

runFromVM :: SolverGroup -> Fetch.RpcInfo -> Maybe Integer -> DappInfo -> VM -> IO VM
runFromVM solvers rpcInfo maxIter' dappinfo vm = do
  let opts =
        UnitTestOptions
          { solvers = solvers,
            rpcInfo = rpcInfo,
            verbose = Nothing,
            maxIter = maxIter',
            askSmtIters = Nothing,
            smtTimeout = Nothing,
            smtDebug = False,
            solver = Nothing,
            maxDepth = Nothing,
            match = "",
            fuzzRuns = 1,
            replay = error "irrelevant",
            vmModifier = id,
            testParams = error "irrelevant",
            dapp = dappinfo,
            ffiAllowed = False,
            covMatch = Nothing
          }
      ui0 = initUiVmState vm opts (void Stepper.execFully)

  v <- mkVty
  ui2 <- customMain v mkVty Nothing (app opts) (ViewVm ui0)
  case ui2 of
    ViewVm ui -> return ui._uiVm
    _ -> error "internal error: customMain returned prematurely"

initUiVmState :: VM -> UnitTestOptions -> Stepper () -> UiVmState
initUiVmState vm0 opts script =
  UiVmState
    { _uiVm = vm0,
      _uiStepper = script,
      _uiStep = 0,
      _uiSnapshots = singleton 0 (vm0, script),
      _uiShowMemory = False,
      _uiTestOpts = opts
    }

-- filters out fuzztests, unless they have
-- explicitly been given an argument by `replay`
debuggableTests :: UnitTestOptions -> (Text, [(Test, [AbiType])]) -> [(Text, Text)]
debuggableTests UnitTestOptions {..} (contractname, tests) = case replay of
  Nothing -> [(contractname, extractSig $ fst x) | x <- tests, not $ isFuzzTest x]
  Just (sig, _) -> [(contractname, extractSig $ fst x) | x <- tests, not (isFuzzTest x) || extractSig (fst x) == sig]

isFuzzTest :: (Test, [AbiType]) -> Bool
isFuzzTest (SymbolicTest _, _) = False
isFuzzTest (ConcreteTest _, []) = False
isFuzzTest (ConcreteTest _, _) = True
isFuzzTest (InvariantTest _, _) = True

main :: UnitTestOptions -> FilePath -> FilePath -> IO ()
main opts root jsonFilePath =
  readSolc jsonFilePath
    >>= \case
      Nothing ->
        error "Failed to read Solidity JSON"
      Just (contractMap, sourceCache) -> do
        let dapp = dappInfo root contractMap sourceCache
            ui =
              ViewPicker $
                UiTestPickerState
                  { _testPickerList =
                      list
                        TestPickerPane
                        ( Vec.fromList
                            ( concatMap
                                (debuggableTests opts)
                                dapp.unitTests
                            )
                        )
                        1,
                    _testPickerDapp = dapp,
                    _testOpts = opts
                  }
        v <- mkVty
        _ <- customMain v mkVty Nothing (app opts) (ui :: UiState)
        return ()

takeStep ::
  ( ?fetcher :: Fetcher,
    ?maxIter :: Maybe Integer
  ) =>
  UiVmState ->
  StepMode ->
  EventM n UiState ()
takeStep ui mode =
  liftIO nxt >>= \case
    (Stopped (), _) ->
      pure ()
    (Continue steps, ui') ->
      put (ViewVm (ui' & set uiStepper steps))
  where
    m = interpret mode ui._uiStepper
    nxt = runStateT m ui

backstepUntil ::
  ( ?fetcher :: Fetcher,
    ?maxIter :: Maybe Integer
  ) =>
  (UiVmState -> Pred VM) ->
  EventM n UiState ()
backstepUntil p =
  get >>= \case
    ViewVm s ->
      case s._uiStep of
        0 -> pure ()
        n -> do
          s1 <- liftIO $ backstep s
          let -- find a previous vm that satisfies the predicate
              snapshots' = Data.Map.filter (p s1 . fst) s1._uiSnapshots
          case lookupLT n snapshots' of
            -- If no such vm exists, go to the beginning
            Nothing ->
              let (step', (vm', stepper')) = fromJust $ lookupLT (n - 1) s._uiSnapshots
                  s2 =
                    s1
                      & set uiVm vm'
                      & set (uiVm . cache) s1._uiVm._cache
                      & set uiStep step'
                      & set uiStepper stepper'
               in takeStep s2 (Step 0)
            -- step until the predicate doesn't hold
            Just (step', (vm', stepper')) ->
              let s2 =
                    s1
                      & set uiVm vm'
                      & set (uiVm . cache) s1._uiVm._cache
                      & set uiStep step'
                      & set uiStepper stepper'
               in takeStep s2 (StepUntil (not . p s1))
    _ -> pure ()

backstep ::
  ( ?fetcher :: Fetcher,
    ?maxIter :: Maybe Integer
  ) =>
  UiVmState ->
  IO UiVmState
backstep s =
  case s._uiStep of
    -- We're already at the first step; ignore command.
    0 -> pure s
    -- To step backwards, we revert to the previous snapshot
    -- and execute n - 1 `mod` snapshotInterval steps from there.

    -- We keep the current cache so we don't have to redo
    -- any blocking queries, and also the memory view.
    n ->
      let (step, (vm, stepper)) = fromJust $ lookupLT n s._uiSnapshots
          s1 =
            s
              & set uiVm vm
              & set (uiVm . cache) s._uiVm._cache
              & set uiStep step
              & set uiStepper stepper
          stepsToTake = n - step - 1
       in runStateT (interpret (Step stepsToTake) stepper) s1 >>= \case
            (Continue steps, ui') -> pure $ ui' & set uiStepper steps
            _ -> error "unexpected end"

appEvent ::
  (?fetcher :: Fetcher, ?maxIter :: Maybe Integer) =>
  BrickEvent Name e ->
  EventM Name UiState ()
-- Contracts: Down - list down
appEvent (VtyEvent e@(V.EvKey V.KDown [])) =
  get >>= \case
    ViewContracts _s -> do
      Brick.zoom
        (_ViewContracts . browserContractList)
        (handleListEvent e)
      pure ()
    _ -> pure ()
-- Contracts: Up - list up
-- Page: Up - scroll
appEvent (VtyEvent e@(V.EvKey V.KUp [])) =
  get >>= \case
    ViewContracts _s -> do
      Brick.zoom
        (_ViewContracts . browserContractList)
        (handleListEvent e)
    _ -> pure ()
-- Vm Overview: Esc - return to test picker or exit
-- Any: Esc - return to Vm Overview or Exit
appEvent (VtyEvent (V.EvKey V.KEsc [])) =
  get >>= \case
    ViewVm s -> do
      let opts = s ^. uiTestOpts
          dapp = opts.dapp
          tests = concatMap (debuggableTests opts) dapp.unitTests
      case tests of
        [] -> halt
        ts ->
          put $
            ViewPicker $
              UiTestPickerState
                { _testPickerList = list TestPickerPane (Vec.fromList ts) 1,
                  _testPickerDapp = dapp,
                  _testOpts = opts
                }
    ViewHelp s -> put (ViewVm s)
    ViewContracts s -> put (ViewVm $ s ^. browserVm)
    _ -> halt
-- Vm Overview: Enter - open contracts view
-- UnitTest Picker: Enter - select from list
appEvent (VtyEvent (V.EvKey V.KEnter [])) =
  get >>= \case
    ViewVm s ->
      put . ViewContracts $
        UiBrowserState
          { _browserContractList =
              list
                BrowserPane
                (Vec.fromList (Map.toList s._uiVm._env._contracts))
                2,
            _browserVm = s
          }
    ViewPicker s ->
      case listSelectedElement s._testPickerList of
        Nothing -> error "nothing selected"
        Just (_, x) -> do
          let initVm = initialUiVmStateForTest s._testOpts x
          put (ViewVm initVm)
    _ -> pure ()
-- Vm Overview: m - toggle memory pane
appEvent (VtyEvent (V.EvKey (V.KChar 'm') [])) =
  get >>= \case
    ViewVm s -> put (ViewVm $ over uiShowMemory not s)
    _ -> pure ()
-- Vm Overview: h - open help view
appEvent (VtyEvent (V.EvKey (V.KChar 'h') [])) =
  get >>= \case
    ViewVm s -> put (ViewHelp s)
    _ -> pure ()
-- Vm Overview: spacebar - read input
appEvent (VtyEvent (V.EvKey (V.KChar ' ') [])) =
  let loop = do
        Readline.getInputLine "% " >>= \case
          Just hey -> Readline.outputStrLn hey
          Nothing -> pure ()
        Readline.getInputLine "% " >>= \case
          Just hey' -> Readline.outputStrLn hey'
          Nothing -> pure ()
   in do
        s <- get
        suspendAndResume $ do
          Readline.runInputT Readline.defaultSettings loop
          pure s

-- todo refactor to zipper step forward
-- Vm Overview: n - step
appEvent (VtyEvent (V.EvKey (V.KChar 'n') [])) =
  get >>= \case
    ViewVm s ->
      when (isNothing (s ^. uiVm . result)) $
        takeStep s (Step 1)
    _ -> pure ()
-- Vm Overview: N - step
appEvent (VtyEvent (V.EvKey (V.KChar 'N') [])) =
  get >>= \case
    ViewVm s ->
      when (isNothing (s ^. uiVm . result)) $
        takeStep s (StepUntil (isNextSourcePosition s))
    _ -> pure ()
-- Vm Overview: C-n - step
appEvent (VtyEvent (V.EvKey (V.KChar 'n') [V.MCtrl])) =
  get >>= \case
    ViewVm s ->
      when (isNothing (s ^. uiVm . result)) $
        takeStep s (StepUntil (isNextSourcePositionWithoutEntering s))
    _ -> pure ()
-- Vm Overview: e - step
appEvent (VtyEvent (V.EvKey (V.KChar 'e') [])) =
  get >>= \case
    ViewVm s ->
      when (isNothing (s ^. uiVm . result)) $
        takeStep s (StepUntil (isExecutionHalted s))
    _ -> pure ()
-- Vm Overview: a - step
appEvent (VtyEvent (V.EvKey (V.KChar 'a') [])) =
  get >>= \case
    ViewVm s ->
      -- We keep the current cache so we don't have to redo
      -- any blocking queries.
      let (vm, stepper) = fromJust (Map.lookup 0 s._uiSnapshots)
          s' =
            s
              & set uiVm vm
              & set (uiVm . cache) s._uiVm._cache
              & set uiStep 0
              & set uiStepper stepper
       in takeStep s' (Step 0)
    _ -> pure ()
-- Vm Overview: p - backstep
appEvent (VtyEvent (V.EvKey (V.KChar 'p') [])) =
  get >>= \case
    ViewVm s ->
      case s._uiStep of
        0 ->
          -- We're already at the first step; ignore command.
          pure ()
        n -> do
          -- To step backwards, we revert to the previous snapshot
          -- and execute n - 1 `mod` snapshotInterval steps from there.

          -- We keep the current cache so we don't have to redo
          -- any blocking queries, and also the memory view.
          let (step, (vm, stepper)) = fromJust $ lookupLT n s._uiSnapshots
              s1 =
                s
                  & set uiVm vm -- set the vm to the one from the snapshot
                  & set (uiVm . cache) s._uiVm._cache
                  -- persist the cache
                  & set uiStep step
                  & set uiStepper stepper
              stepsToTake = n - step - 1

          takeStep s1 (Step stepsToTake)
    _ -> pure ()
-- Vm Overview: P - backstep to previous source
appEvent (VtyEvent (V.EvKey (V.KChar 'P') [])) =
  backstepUntil isNextSourcePosition
-- Vm Overview: c-p - backstep to previous source avoiding CALL and CREATE
appEvent (VtyEvent (V.EvKey (V.KChar 'p') [V.MCtrl])) =
  backstepUntil isNextSourcePositionWithoutEntering
-- Vm Overview: 0 - choose no jump
appEvent (VtyEvent (V.EvKey (V.KChar '0') [])) =
  get >>= \case
    ViewVm s ->
      case view (uiVm . result) s of
        Just (VMFailure (Choose (PleaseChoosePath _ contin))) ->
          takeStep
            (s & set uiStepper (Stepper.evm (contin True) >> s._uiStepper))
            (Step 1)
        _ -> pure ()
    _ -> pure ()
-- Vm Overview: 1 - choose jump
appEvent (VtyEvent (V.EvKey (V.KChar '1') [])) =
  get >>= \case
    ViewVm s ->
      case s._uiVm._result of
        Just (VMFailure (Choose (PleaseChoosePath _ contin))) ->
          takeStep
            (s & set uiStepper (Stepper.evm (contin False) >> s._uiStepper))
            (Step 1)
        _ -> pure ()
    _ -> pure ()
-- Page: C-f - Page down
appEvent (VtyEvent (V.EvKey (V.KChar 'f') [V.MCtrl])) =
  vScrollPage (viewportScroll TracePane) Down
-- Page: C-b - Page up
appEvent (VtyEvent (V.EvKey (V.KChar 'b') [V.MCtrl])) =
  vScrollPage (viewportScroll TracePane) Up
-- UnitTest Picker: (main) - render list
appEvent (VtyEvent e) = do
  Brick.zoom
    (_ViewPicker . testPickerList)
    (handleListEvent e)

-- Default
appEvent _ = pure ()

app :: UnitTestOptions -> App UiState () Name
app UnitTestOptions {..} =
  let ?fetcher = Fetch.oracle solvers rpcInfo
      ?maxIter = maxIter
   in App
        { appDraw = drawUi,
          appChooseCursor = neverShowCursor,
          appHandleEvent = appEvent,
          appStartEvent = pure (),
          appAttrMap = const (attrMap V.defAttr myTheme)
        }

initialUiVmStateForTest ::
  UnitTestOptions ->
  (Text, Text) ->
  UiVmState
initialUiVmStateForTest opts@UnitTestOptions {..} (theContractName, theTestName) = initUiVmState vm0 opts script
  where
    cd = case test of
      SymbolicTest _ -> symCalldata theTestName types [] (AbstractBuf "txdata")
      _ -> (error "unreachable", error "unreachable")
    (test, types) = fromJust $ find (\(test', _) -> extractSig test' == theTestName) $ unitTestMethods testContract
    testContract = fromJust $ Map.lookup theContractName dapp.solcByName
    vm0 =
      initialUnitTestVm opts testContract
    script = do
      Stepper.evm . pushTrace . EntryTrace $
        "test " <> theTestName <> " (" <> theContractName <> ")"
      initializeUnitTest opts testContract
      case test of
        ConcreteTest _ -> do
          let args = case replay of
                Nothing -> emptyAbi
                Just (sig, callData) ->
                  if theTestName == sig
                    then decodeAbiValue (AbiTupleType (Vec.fromList types)) callData
                    else emptyAbi
          void (runUnitTest opts theTestName args)
        SymbolicTest _ -> do
          void (execSymTest opts theTestName cd)
        InvariantTest _ -> do
          targets <- getTargetContracts opts
          let randomRun = initialExplorationStepper opts theTestName [] targets (fromMaybe 20 maxDepth)
          void $ case replay of
            Nothing -> randomRun
            Just (sig, cd') ->
              if theTestName == sig
                then initialExplorationStepper opts theTestName (decodeCalls cd') targets (length (decodeCalls cd'))
                else randomRun

myTheme :: [(AttrName, V.Attr)]
myTheme =
  [ (selectedAttr, V.defAttr `V.withStyle` V.standout),
    (dimAttr, V.defAttr `V.withStyle` V.dim),
    (borderAttr, V.defAttr `V.withStyle` V.dim),
    (wordAttr, fg V.yellow),
    (boldAttr, V.defAttr `V.withStyle` V.bold),
    (activeAttr, V.defAttr `V.withStyle` V.standout)
  ]

drawUi :: UiState -> [UiWidget]
drawUi (ViewVm s) = drawVm s
drawUi (ViewPicker s) = drawTestPicker s
drawUi (ViewContracts s) = drawVmBrowser s
drawUi (ViewHelp _) = drawHelpView

drawHelpView :: [UiWidget]
drawHelpView =
  [ center
      . borderWithLabel version
      . padLeftRight 4
      . padTopBottom 2
      . str
      $ "Esc    Exit the debugger\n\n"
        <> "a      Step to start\n"
        <> "e      Step to end\n"
        <> "n      Step fwds by one instruction\n"
        <> "N      Step fwds to the next source position\n"
        <> "C-n    Step fwds to the next source position skipping CALL & CREATE\n"
        <> "p      Step back by one instruction\n\n"
        <> "P      Step back to the previous source position\n\n"
        <> "C-p    Step back to the previous source position skipping CALL & CREATE\n\n"
        <> "m      Toggle memory pane\n"
        <> "0      Choose the branch which does not jump \n"
        <> "1      Choose the branch which does jump \n"
        <> "Down   Step to next entry in the callstack / Scroll memory pane\n"
        <> "Up     Step to previous entry in the callstack / Scroll memory pane\n"
        <> "C-f    Page memory pane fwds\n"
        <> "C-b    Page memory pane back\n\n"
        <> "Enter  Contracts browser"
  ]
  where
    version =
      txt "Hevm "
        <+> str (showVersion Paths.version)
        <+> txt " - Key bindings"

drawTestPicker :: UiTestPickerState -> [UiWidget]
drawTestPicker ui =
  [ center
      . borderWithLabel (txt "Unit tests")
      . hLimit 80
      $ renderList
        ( \selected (x, y) ->
            withHighlight selected $
              txt " Debug " <+> txt (contractNamePart x) <+> txt "::" <+> txt y
        )
        True
        ui._testPickerList
  ]

drawVmBrowser :: UiBrowserState -> [UiWidget]
drawVmBrowser ui =
  [ hBox
      [ borderWithLabel (txt "Contracts")
          . hLimit 60
          $ renderList
            ( \selected (k, c') ->
                withHighlight selected . txt . mconcat $
                  [ fromMaybe "<unknown contract>" $
                      Map.lookup (maybeHash c') dapp.solcByHash <&> (.contractName) . snd,
                    "\n",
                    "  ",
                    pack (show k)
                  ]
            )
            True
            ui._browserContractList,
        case snd <$> Map.lookup (maybeHash c) dapp.solcByHash of
          Nothing ->
            hBox
              [ borderWithLabel (txt "Contract information") . padBottom Max . padRight Max $
                  vBox
                    [ txt ("Codehash: " <> pack (show c._codehash)),
                      txt ("Nonce: " <> showWordExact c._nonce),
                      txt ("Balance: " <> showWordExact c._balance)
                    ]
              ]
          -- , txt ("Storage: "  <> storageDisplay (view storage c)) -- TODO: fix this

          Just sol ->
            hBox
              [ borderWithLabel (txt "Contract information") . padBottom Max . padRight (Pad 2) $
                  vBox
                    [ txt "Name: " <+> txt (contractNamePart sol.contractName),
                      txt "File: " <+> txt (contractPathPart sol.contractName),
                      txt " ",
                      txt "Constructor inputs:",
                      vBox . flip map sol.constructorInputs $
                        \(name, abiType) -> txt ("  " <> name <> ": " <> abiTypeSolidity abiType),
                      txt "Public methods:",
                      vBox . flip map (sort (Map.elems sol.abiMap)) $
                        \method -> txt ("  " <> method.methodSignature)
                    ],
                -- , txt ("Storage:" <> storageDisplay (view storage c)) -- TODO: fix this

                borderWithLabel (txt "Storage slots") . padBottom Max . padRight Max $
                  vBox
                    (map txt (storageLayout dapp sol))
              ]
      ]
  ]
  where
    dapp = ui._browserVm._uiTestOpts.dapp
    (_, (_, c)) = fromJust $ listSelectedElement ui._browserContractList
    --        currentContract  = view (dappSolcByHash . ix ) dapp
    maybeHash ch = fromJust (error "Internal error: cannot find concrete codehash for partially symbolic code") (maybeLitWord ch._codehash)

drawVm :: UiVmState -> [UiWidget]
drawVm ui =
  -- EVM debugging needs a lot of space because of the 256-bit words
  -- in both the bytecode and the stack .
  --
  -- If on a very tall display, prefer a vertical layout.
  --
  -- Actually the horizontal layout would be preferrable if the display
  -- is both very tall and very wide, but this is okay for now.
  [ ifTallEnough
      (20 * 4)
      ( vBox
          [ vLimit 20 $ drawBytecodePane ui,
            vLimit 20 $ drawStackPane ui,
            drawSolidityPane ui,
            vLimit 20 $ drawTracePane ui,
            vLimit 2 drawHelpBar
          ]
      )
      ( vBox
          [ hBox
              [ vLimit 20 $ drawBytecodePane ui,
                vLimit 20 $ drawStackPane ui
              ],
            hBox
              [ drawSolidityPane ui,
                drawTracePane ui
              ],
            vLimit 2 drawHelpBar
          ]
      )
  ]

drawHelpBar :: UiWidget
drawHelpBar = hBorder <=> hCenter help
  where
    help =
      hBox (map (\(k, v) -> txt k <+> dim (txt (" (" <> v <> ")  "))) helps)

    helps =
      [ ("n", "step"),
        ("p", "step back"),
        ("a", "step to start"),
        ("e", "step to end"),
        ("m", "toggle memory"),
        ("Esc", "exit"),
        ("h", "more help")
      ]

stepOneOpcode :: Stepper a -> StateT UiVmState IO ()
stepOneOpcode restart = do
  n <- use uiStep
  when (n > 0 && n `mod` snapshotInterval == 0) $ do
    vm <- use uiVm
    modifying uiSnapshots (insert n (vm, void restart))
  modifying uiVm (execState exec1)
  modifying uiStep (+ 1)

isNewTraceAdded ::
  UiVmState -> Pred VM
isNewTraceAdded ui vm =
  let currentTraceTree = length <$> traceForest ui._uiVm
      newTraceTree = length <$> traceForest vm
   in currentTraceTree /= newTraceTree

isNextSourcePosition ::
  UiVmState -> Pred VM
isNextSourcePosition ui vm =
  let dapp = ui._uiTestOpts.dapp
      initialPosition = currentSrcMap dapp ui._uiVm
   in currentSrcMap dapp vm /= initialPosition

isNextSourcePositionWithoutEntering ::
  UiVmState -> Pred VM
isNextSourcePositionWithoutEntering ui vm =
  let dapp = ui._uiTestOpts.dapp
      vm0 = ui._uiVm
      initialPosition = currentSrcMap dapp vm0
      initialHeight = length vm0._frames
   in case currentSrcMap dapp vm of
        Nothing ->
          False
        Just here ->
          let moved = Just here /= initialPosition
              deeper = length vm._frames > initialHeight
              boring =
                case srcMapCode dapp.sources here of
                  Just bs ->
                    BS.isPrefixOf "contract " bs
                  Nothing ->
                    True
           in moved && not deeper && not boring

isExecutionHalted :: UiVmState -> Pred VM
isExecutionHalted _ vm = isJust vm._result

currentSrcMap :: DappInfo -> VM -> Maybe SrcMap
currentSrcMap dapp vm = do
  this <- currentContract vm
  i <- this._opIxMap SVec.!? vm._state._pc
  srcMap dapp this i

drawStackPane :: UiVmState -> UiWidget
drawStackPane ui =
  let gasText = showWordExact (num ui._uiVm._state._gas)
      labelText = txt ("Gas available: " <> gasText <> "; stack:")
      stackList = list StackPane (Vec.fromList $ zip [(1 :: Int) ..] (simplify <$> ui._uiVm._state._stack)) 2
   in hBorderWithLabel labelText
        <=> renderList
          ( \_ (i, w) ->
              vBox
                [ withHighlight True (str ("#" ++ show i ++ " "))
                    <+> ourWrap (Text.unpack $ prettyIfConcreteWord w),
                  dim
                    ( txt
                        ( "   " <> case unlit w of
                            Nothing -> ""
                            Just u -> showWordExplanation u ui._uiTestOpts.dapp
                        )
                    )
                ]
          )
          False
          stackList

message :: VM -> String
message vm =
  case vm._result of
    Just (VMSuccess (ConcreteBuf msg)) ->
      "VMSuccess: " <> (show $ ByteStringS msg)
    Just (VMSuccess (msg)) ->
      "VMSuccess: <symbolicbuffer> " <> (show msg)
    Just (VMFailure (EVM.Revert msg)) ->
      "VMFailure: " <> (show msg)
    Just (VMFailure err) ->
      "VMFailure: " <> show err
    Nothing ->
      "Executing EVM code in " <> show vm._state._contract

drawBytecodePane :: UiVmState -> UiWidget
drawBytecodePane ui =
  let vm = ui._uiVm
      move = maybe id listMoveTo $ vmOpIx vm
   in hBorderWithLabel (str $ message vm)
        <=> Centered.renderList
          ( \active x ->
              if not active
                then withDefAttr dimAttr (opWidget x)
                else withDefAttr boldAttr (opWidget x)
          )
          False
          ( move $
              list
                BytecodePane
                (maybe mempty (._codeOps) (currentContract vm))
                1
          )

dim :: Widget n -> Widget n
dim = withDefAttr dimAttr

withHighlight :: Bool -> Widget n -> Widget n
withHighlight False = withDefAttr dimAttr
withHighlight True = withDefAttr boldAttr

prettyIfConcrete :: Expr Buf -> String
prettyIfConcrete (ConcreteBuf x) = prettyHex 40 x
prettyIfConcrete x = T.unpack $ formatExpr $ simplify x

drawTracePane :: UiVmState -> UiWidget
drawTracePane s =
  let vm = s._uiVm
      dapp = s._uiTestOpts.dapp
      traceList =
        list
          TracePane
          ( Vec.fromList
              . Text.lines
              . showTraceTree dapp
              $ vm
          )
          1
   in case s._uiShowMemory of
        True ->
          viewport TracePane Vertical $
            hBorderWithLabel (txt "Calldata")
              <=> ourWrap (prettyIfConcrete vm._state._calldata)
              <=> hBorderWithLabel (txt "Returndata")
              <=> ourWrap (prettyIfConcrete vm._state._returndata)
              <=> hBorderWithLabel (txt "Output")
              <=> ourWrap (maybe "" show vm._result)
              <=> hBorderWithLabel (txt "Cache")
              <=> ourWrap (show vm._cache._path)
              <=> hBorderWithLabel (txt "Path Conditions")
              <=> (ourWrap $ show $ vm._constraints)
              <=> hBorderWithLabel (txt "Memory")
              <=> (ourWrap (prettyIfConcrete vm._state._memory))
        False ->
          hBorderWithLabel (txt "Trace")
            <=> renderList
              (\_ x -> txt x)
              False
              (listMoveTo (length traceList) traceList)

ourWrap :: String -> Widget n
ourWrap = strWrapWith settings
  where
    settings =
      WrapSettings
        { preserveIndentation = True,
          breakLongWords = True,
          fillStrategy = NoFill,
          fillScope = FillAfterFirst
        }

solidityList :: VM -> DappInfo -> List Name (Int, ByteString)
solidityList vm dapp =
  list
    SolidityPane
    ( case currentSrcMap dapp vm of
        Nothing -> mempty
        Just x ->
          view
            ( ix x.srcMapFile
                . to (Vec.imap (,))
            )
            dapp.sources.lines
    )
    1

drawSolidityPane :: UiVmState -> UiWidget
drawSolidityPane ui =
  let dapp = ui._uiTestOpts.dapp
      dappSrcs = dapp.sources
      vm = ui._uiVm
   in case currentSrcMap dapp vm of
        Nothing -> padBottom Max (hBorderWithLabel (txt "<no source map>"))
        Just sm ->
          let rows = dappSrcs.lines !! sm.srcMapFile
              subrange = lineSubrange rows (sm.srcMapOffset, sm.srcMapLength)
              fileName :: Maybe Text
              fileName = preview (ix sm.srcMapFile . _1) dapp.sources.files
              lineNo :: Maybe Int
              lineNo = ((\a -> Just (a - 1)) . snd) =<< srcMapCodePos dapp.sources sm
           in vBox
                [ hBorderWithLabel $
                    txt (fromMaybe "<unknown>" fileName)
                      <+> str (":" ++ (maybe "?" show lineNo))
                      -- Show the AST node type if present
                      <+> txt
                        ( " ("
                            <> fromMaybe
                              "?"
                              ( dapp.astSrcMap sm
                                  >>= preview (key "name" . _String)
                              )
                            <> ")"
                        ),
                  Centered.renderList
                    ( \_ (i, line) ->
                        let s = case decodeUtf8 line of "" -> " "; y -> y
                         in case subrange i of
                              Nothing -> withHighlight False (txt s)
                              Just (a, b) ->
                                let (x, y, z) =
                                      ( Text.take a s,
                                        Text.take b (Text.drop a s),
                                        Text.drop (a + b) s
                                      )
                                 in hBox
                                      [ withHighlight False (txt x),
                                        withHighlight True (txt y),
                                        withHighlight False (txt z)
                                      ]
                    )
                    False
                    ( (maybe id listMoveTo lineNo)
                        (solidityList vm dapp)
                    )
                ]

ifTallEnough :: Int -> Widget n -> Widget n -> Widget n
ifTallEnough need w1 w2 =
  Widget Greedy Greedy $ do
    c <- getContext
    if view availHeightL c > need
      then render w1
      else render w2

opWidget :: (Integral a, Show a) => (a, Op) -> Widget n
opWidget = txt . pack . opString

selectedAttr :: AttrName
selectedAttr = attrName "selected"

dimAttr :: AttrName
dimAttr = attrName "dim"

wordAttr :: AttrName
wordAttr = attrName "word"

boldAttr :: AttrName
boldAttr = attrName "bold"

activeAttr :: AttrName
activeAttr = attrName "active"
