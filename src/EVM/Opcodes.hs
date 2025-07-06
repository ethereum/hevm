{-# LANGUAGE TemplateHaskell, ImplicitParams #-}

module EVM.Opcodes where

import Optics.Core
import Optics.State
import Optics.State.Operators
import Optics.Zoom
import Optics.Operators.Unsafe


import Control.Monad.ST (ST)
import Control.Monad.State.Strict (StateT, get, put, gets)
import Witch.From (From)
import Witch (into, tryInto)
import Data.Word (Word8)
import Data.Vector qualified as V
import Data.ByteString qualified as BS

import EVM
import EVM.Types
import EVM.FeeSchedule (FeeSchedule (..))
import EVM.Expr qualified as Expr
import EVM.Effects (defaultConfig, maxDepth)

--{-# INLINE modifyState #-}
--modifyState :: (FrameState t s -> FrameState t s) -> VM t s -> VM t s
--modifyState f vm = vm { state = f (vm.state) }

runOpcodeAdd :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeAdd = do
  vm <- get
  let FeeSchedule {..} = vm.block.schedule
  let stk = vm.state.stack
  case stk of
    x:y:xs -> burn g_verylow $ do
      next
      vm' <- get
      let add (Lit a) (Lit b) = Lit (a + b)
          add a b = Expr.add a b
      put $ modifyState (vm'.state { stack = add x y : xs }) vm'
    _ -> underrun
  where modifyState :: FrameState t s -> VM t s -> VM t s
        modifyState st vm = vm { state = st }

runOpcodeAddSrc :: String
runOpcodeAddSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  let stk = vm.state.stack\n\
\  case stk of\n\
\    x:y:xs -> burn g_verylow $ do\n\
\      next\n\
\      vm' <- get\n\
\      let add (Lit a) (Lit b) = Lit (a + b)\n\
\          add a b = Expr.add a b\n\
\      put $ modifyState (vm'.state { stack = add x y : xs }) vm'\n\
\    _ -> underrun\n\
\  where modifyState :: FrameState t s -> VM t s -> VM t s\n\
\        modifyState st vm = vm { state = st }"

runOpcodeAddType :: String
runOpcodeAddType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeMul :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeMul = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_low Expr.mul

runOpcodeMulSrc :: String
runOpcodeMulSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  let stk = vm.state.stack\n\
\  case stk of\n\
\    x:y:xs -> burn g_low $ do\n\
\      next\n\
\      vm' <- get\n\
\      let f (Lit a) (Lit b) = Lit (a * b)\n\
\          f a b = Expr.mul a b\n\
\      put $ modifyState (vm'.state { stack = f x y : xs }) vm'\n\
\    _ -> underrun\n\
\  where modifyState :: FrameState t s -> VM t s -> VM t s\n\
\        modifyState st vm = vm { state = st }"

runOpcodeMulType :: String
runOpcodeMulType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeSub :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeSub = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_verylow Expr.sub

runOpcodeSubSrc :: String
runOpcodeSubSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  let stk = vm.state.stack\n\
\  case stk of\n\
\    x:y:xs -> burn g_low $ do\n\
\      next\n\
\      vm' <- get\n\
\      let f (Lit a) (Lit b) = Lit (a - b)\n\
\          f a b = Expr.sub a b\n\
\      put $ modifyState (vm'.state { stack = f x y : xs }) vm'\n\
\    _ -> underrun\n\
\  where modifyState :: FrameState t s -> VM t s -> VM t s\n\
\        modifyState st vm = vm { state = st }"

runOpcodeSubType :: String
runOpcodeSubType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeDiv :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeDiv = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_low Expr.div

runOpcodeDivSrc :: String
runOpcodeDivSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp2 g_low Expr.div"

runOpcodeDivType :: String
runOpcodeDivType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeMod :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeMod = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_low Expr.mod

runOpcodeModSrc :: String
runOpcodeModSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp2 g_low Expr.mod"

runOpcodeModType :: String
runOpcodeModType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

{-# INLINE runOpcodeDup #-}
runOpcodeDup :: (From source Int, VMOps t, ?op::Word8) =>
                source -> StateT (VM t s) (ST s) ()
runOpcodeDup i = do
  vm <- get
  let
    stk  = vm.state.stack
    FeeSchedule {..} = vm.block.schedule
  let remainingStack = drop (into i - 1) stk
  case remainingStack of
    [] -> underrun
    (x:_) -> limitStack 1 $
      burn g_verylow $ do
        next
        pushSym x

runOpcodeDupSrc :: String
runOpcodeDupSrc = "do\n\
\ vm <- get\n\
\ let stk = vm.state.stack\n\
\ let FeeSchedule {..} = vm.block.schedule\n\
\ let remainingStack = drop (into i - 1) stk\n\
\ case remainingStack of\n\
\   [] -> underrun\n\
\   (x:_) -> limitStack 1 $\n\
\     burn g_verylow $ do\n\
\       next\n\
\       pushSym x"

runOpcodeDupType :: String
runOpcodeDupType = "(From source Int, VMOps t, ?op::Word8) => source -> StateT (VM t s) (ST s) ()"

runOpcodeSwap :: (?op::Word8, VMOps t, From source Int) => source -> StateT (VM t s) (ST s) ()
runOpcodeSwap i = do
  vm <- get
  let stk = vm.state.stack
  let FeeSchedule {..} = vm.block.schedule
  case (stk ^? ix_i, stk ^? ix_0) of
    (Just ei, Just e0) ->
      burn g_verylow $ do
        next
        zoom (#state % #stack) $ do
          ix_i .= e0
          ix_0 .= ei
    _ -> underrun
  where
    (ix_i, ix_0) = (ix (into i), ix 0)
  --where modifyState :: FrameState t s -> VM t s -> VM t s
  --      modifyState st vm = vm { state = st }

runOpcodeSwapSrc :: String
runOpcodeSwapSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case (stk ^? ix_i, stk ^? ix_0) of\n\
\    (Just ei, Just e0) ->\n\
\      burn g_verylow $ do\n\
\        next\n\
\        zoom (#state % #stack) $ do\n\
\          ix_i .= e0\n\
\          ix_0 .= ei\n\
\    _ -> underrun\n\
\  where\n\
\    (ix_i, ix_0) = (ix (into i), ix 0)\n"


runOpcodeSwapType :: String
runOpcodeSwapType = "(?op::Word8, VMOps t, From source Int) => source -> StateT (VM t s) (ST s) ()"

runOpcodePush0 :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodePush0 = do
  vm <- get
  let FeeSchedule {..} = vm.block.schedule
  limitStack 1 $
    burn g_base $ do
      next
      pushSym (Lit 0)

runOpcodePush0Type :: String
runOpcodePush0Type = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodePush0Src :: String
runOpcodePush0Src = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  limitStack 1 $\n\
\    burn g_base $ do\n\
\      next\n\
\      pushSym (Lit 0)"

runOpcodePush :: (From source Int, VMOps t, ?op::Word8) => source -> StateT (VM t s) (ST s) ()
runOpcodePush i = do
  vm <- get
  let FeeSchedule {..} = vm.block.schedule
  let n = into i
      !xs = case vm.state.code of
        UnknownCode _ -> internalError "Cannot execute unknown code"
        InitCode conc _ -> Lit $ word $ padRight n $ BS.take n (BS.drop (1 + vm.state.pc) conc)
        RuntimeCode (ConcreteRuntimeCode bs) -> Lit $ word $ BS.take n $ BS.drop (1 + vm.state.pc) bs
        RuntimeCode (SymbolicRuntimeCode ops) ->
          let bytes = V.take n $ V.drop (1 + vm.state.pc) ops
          in Expr.readWord (Lit 0) $ Expr.fromList $ padLeft' 32 bytes
  limitStack 1 $
    burn g_verylow $ do
      next
      pushSym xs

runOpcodePushSrc :: String
runOpcodePushSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  let n = into i\n\
\      !xs = case vm.state.code of\n\
\        UnknownCode _ -> internalError \"Cannot execute unknown code\"\n\
\        InitCode conc _ -> Lit $ word $ padRight n $ BS.take n (BS.drop (1 + vm.state.pc) conc)\n\
\        RuntimeCode (ConcreteRuntimeCode bs) -> Lit $ word $ BS.take n $ BS.drop (1 + vm.state.pc) bs\n\
\        RuntimeCode (SymbolicRuntimeCode ops) ->\n\
\          let bytes = V.take n $ V.drop (1 + vm.state.pc) ops\n\
\          in Expr.readWord (Lit 0) $ Expr.fromList $ padLeft' 32 bytes\n\
\  limitStack 1 $\n\
\    burn g_verylow $ do\n\
\      next\n\
\      pushSym xs"

runOpcodePushType :: String
runOpcodePushType = "(From source Int, VMOps t, ?op::Word8) => source -> StateT (VM t s) (ST s) ()"

runOpcodePop :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodePop = do
  vm <- get
  let stk = vm.state.stack
      FeeSchedule {..} = vm.block.schedule
  case stk of
    _:xs -> burn g_base (next >> assign (#state % #stack) xs)
    _    -> underrun

runOpcodePopSrc :: String
runOpcodePopSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case stk of\n\
\    _:xs -> burn g_base (next >> assign (#state % #stack) xs)\n\
\    _    -> underrun"

runOpcodePopType :: String
runOpcodePopType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

{-# INLINE runOpcodeRevert #-}
runOpcodeRevert :: (VMOps t) =>
                StateT (VM t s) (ST s) ()
runOpcodeRevert = do
  vm <- get
  let stk = vm.state.stack
  case stk of
    xOffset:xSize:_ ->
      accessMemoryRange xOffset xSize $ do
        output <- readMemory xOffset xSize
        finishFrame (FrameReverted output)
    _ -> underrun

runOpcodeRevertSrc :: String
runOpcodeRevertSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  case stk of\n\
\    xOffset:xSize:_ ->\n\
\      accessMemoryRange xOffset xSize $ do\n\
\        output <- readMemory xOffset xSize\n\
\        finishFrame (FrameReverted output)\n\
\    _ -> underrun"

runOpcodeRevertType :: String
runOpcodeRevertType = "(VMOps t) => StateT (VM t s) (ST s) ()"

runOpStop :: (VMOps t) => EVM t s ()
runOpStop = finishFrame (FrameReturned mempty)

runOpcodeStopSrc :: String
runOpcodeStopSrc = "finishFrame (FrameReturned mempty)"

runOpcodeStopType :: String
runOpcodeStopType = "VMOps t => EVM t s ()"

runOpcodeJumpi :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeJumpi = do
  vm <- get
  let conf = defaultConfig -- TODO
  let stk = vm.state.stack
      FeeSchedule {..} = vm.block.schedule
  case stk of
    x:y:xs -> let ?conf = defaultConfig in forceConcreteLimitSz x 2 "JUMPI: symbolic jumpdest" $ \x' ->
      burn g_high $
        let jump :: (VMOps t) => Bool -> EVM t s ()
            jump False = assign (#state % #stack) xs >> next
            jump _    = case tryInto x' of
              Left _ -> vmError BadJumpDestination
              Right i -> checkJump i xs
        in branch conf.maxDepth y jump
    _ -> underrun

runOpcodeJumpiSrc :: String
runOpcodeJumpiSrc = "do\n\
\  vm <- get\n\
\  let conf = defaultConfig -- TODO\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case stk of\n\
\    x:y:xs -> let ?conf = defaultConfig in forceConcreteLimitSz x 2 \"JUMPI: symbolic jumpdest\" $ \\x' ->\n\
\      burn g_high $\n\
\        let jump :: (VMOps t) => Bool -> EVM t s ()\n\
\            jump False = assign (#state % #stack) xs >> next\n\
\            jump _    = case tryInto x' of\n\
\              Left _ -> vmError BadJumpDestination\n\
\              Right i -> checkJump i xs\n\
\        in branch conf.maxDepth y jump\n\
\    _ -> underrun"

runOpcodeJumpiType :: String
runOpcodeJumpiType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeJump :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodeJump = do
  vm <- get
  let stk = vm.state.stack
      FeeSchedule {..} = vm.block.schedule
  case stk of
    x:xs ->
      burn g_mid $ let ?conf = defaultConfig in forceConcreteLimitSz x 2 "JUMP: symbolic jumpdest" $ \x' ->
        case tryInto x' of
          Left _ -> vmError BadJumpDestination
          Right i -> checkJump i xs
    _ -> underrun

runOpcodeJumpSrc :: String
runOpcodeJumpSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case stk of\n\
\    x:xs ->\n\
\      burn g_mid $ let ?conf = defaultConfig in forceConcreteLimitSz x 2 \"JUMP: symbolic jumpdest\" $ \\x' ->\n\
\        case tryInto x' of\n\
\          Left _ -> vmError BadJumpDestination\n\
\          Right i -> checkJump i xs\n\
\    _ -> underrun"

runOpcodeJumpType :: String
runOpcodeJumpType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeJumpdest :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodeJumpdest = do
  vm <- get
  let FeeSchedule {..} = vm.block.schedule
  burn g_jumpdest next

runOpcodeJumpdestSrc :: String
runOpcodeJumpdestSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  burn g_jumpdest next"

runOpcodeJumpdestType :: String
runOpcodeJumpdestType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeMStore :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodeMStore = do
  vm <- get
  let stk = vm.state.stack
      FeeSchedule {..} = vm.block.schedule
  case stk of
    x:y:xs ->
      burn g_verylow $
        accessMemoryWord x $ do
          next
          gets (.state.memory) >>= \case
            ConcreteMemory mem -> do
              case y of
                Lit w ->
                  copyBytesToMemory (ConcreteBuf (word256Bytes w)) (Lit 32) (Lit 0) x
                _ -> do
                  -- copy out and move to symbolic memory
                  buf <- freezeMemory mem
                  assign (#state % #memory) (SymbolicMemory $ Expr.writeWord x y buf)
            SymbolicMemory mem ->
              assign (#state % #memory) (SymbolicMemory $ Expr.writeWord x y mem)
          assign (#state % #stack) xs
    _ -> underrun

runOpcodeMStoreSrc :: String
runOpcodeMStoreSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case stk of\n\
\    x:y:xs ->\n\
\      burn g_verylow $\n\
\        accessMemoryWord x $ do\n\
\          next\n\
\          gets (.state.memory) >>= \\case\n\
\            ConcreteMemory mem -> do\n\
\              case y of\n\
\                Lit w ->\n\
\                  copyBytesToMemory (ConcreteBuf (word256Bytes w)) (Lit 32) (Lit 0) x\n\
\                _ -> do\n\
\                  -- copy out and move to symbolic memory\n\
\                  buf <- freezeMemory mem\n\
\                  assign (#state % #memory) (SymbolicMemory $ Expr.writeWord x y buf)\n\
\            SymbolicMemory mem ->\n\
\              assign (#state % #memory) (SymbolicMemory $ Expr.writeWord x y mem)\n\
\          assign (#state % #stack) xs\n\
\    _ -> underrun"

runOpcodeMStoreType :: String
runOpcodeMStoreType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeMLoad :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodeMLoad = do
  vm <- get
  let stk = vm.state.stack
      FeeSchedule {..} = vm.block.schedule
  case stk of
    x:xs ->
      burn g_verylow $
        accessMemoryWord x $ do
          next
          buf <- readMemory x (Lit 32)
          let w = Expr.readWordFromBytes (Lit 0) buf
          assign (#state % #stack) (w : xs)
    _ -> underrun

runOpcodeMLoadSrc :: String
runOpcodeMLoadSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case stk of\n\
\    x:xs ->\n\
\      burn g_verylow $\n\
\        accessMemoryWord x $ do\n\
\          next\n\
\          buf <- readMemory x (Lit 32)\n\
\          let w = Expr.readWordFromBytes (Lit 0) buf\n\
\          assign (#state % #stack) (w : xs)\n\
\    _ -> underrun"

runOpcodeMLoadType :: String
runOpcodeMLoadType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeSlt :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()
runOpcodeSlt = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_verylow Expr.slt

runOpcodeSltSrc :: String
runOpcodeSltSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp2 g_verylow Expr.slt"

runOpcodeSltType :: String
runOpcodeSltType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeIsZero :: (VMOps t, ?op::Word8) =>
                StateT (VM t s) (ST s) ()

runOpcodeIsZero = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp1 g_verylow Expr.iszero

runOpcodeIsZeroSrc :: String
runOpcodeIsZeroSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp1 g_verylow Expr.iszero"

runOpcodeIsZeroType :: String
runOpcodeIsZeroType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeEq :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeEq = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_verylow Expr.eq

runOpcodeEqSrc :: String
runOpcodeEqSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp2 g_verylow Expr.eq"

runOpcodeEqType :: String
runOpcodeEqType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

runOpcodeStackOp2Src :: String
runOpcodeStackOp2Src =
  "use (#state % #stack) >>= \\case\n\
\  x:y:xs ->\n\
\    burn cost $ do\n\
\      next\n\
\      #state % #stack .= f x y : xs\n\
\  _ ->\n\
\    underrun"

runOpcodeStackOp2Type :: String
runOpcodeStackOp2Type = "(?op :: Word8, VMOps t) => Word64 -> (Expr EWord -> Expr EWord -> Expr EWord) -> EVM t s ()"

nextFast :: (?op :: Word8) => EVM t s ()
nextFast = do
  vm <- get
  put $ modifyState (vm.state { pc = vm.state.pc + fromIntegral (opSize ?op) }) vm
  where modifyState :: FrameState t s -> VM t s -> VM t s
        modifyState st vm = vm { state = st }

runOpcodeNextSrc :: String
runOpcodeNextSrc = "do\n\
\  vm <- get\n\
\  put $ modifyState (vm.state { pc = vm.state.pc + fromIntegral (opSize ?op) }) vm\n\
\  where modifyState :: FrameState t s -> VM t s -> VM t s\n\
\        modifyState st vm = vm { state = st }"

runOpcodeNextType :: String
runOpcodeNextType = "(?op :: Word8) => EVM t s ()"

opcodesImpl :: [(String, String, String, String, Bool)]
opcodesImpl =
  [
    ("Add",  "", runOpcodeAddType, runOpcodeAddSrc, True)
  , ("Mul",  "", runOpcodeMulType, runOpcodeMulSrc, True)
  , ("Sub",  "", runOpcodeSubType, runOpcodeSubSrc, True)
  , ("Div",  "", runOpcodeDivType, runOpcodeDivSrc, True)
  , ("Mod",  "", runOpcodeModType, runOpcodeModSrc, True)
  , ("Push0", "", runOpcodePush0Type, runOpcodePush0Src, True)
  , ("Push", " i", runOpcodePushType, runOpcodePushSrc, True)
  , ("Pop",  "", runOpcodePopType, runOpcodePopSrc, True)
  , ("Stop", "", runOpcodeStopType, runOpcodeStopSrc, True)
  , ("Revert", "", runOpcodeRevertType, runOpcodeRevertSrc, True)
  , ("Dup", " i", runOpcodeDupType, runOpcodeDupSrc, True)
  , ("Swap", " i", runOpcodeSwapType, runOpcodeSwapSrc, True)
  , ("MStore", "", runOpcodeMStoreType, runOpcodeMStoreSrc, True)
  , ("MLoad", "", runOpcodeMLoadType, runOpcodeMLoadSrc, True)
  , ("IsZero", "", runOpcodeIsZeroType, runOpcodeIsZeroSrc, True)
  , ("Eq", "", runOpcodeEqType, runOpcodeEqSrc, True)
  , ("Jumpi", "", runOpcodeJumpiType, runOpcodeJumpiSrc, True)
  , ("Jump", "", runOpcodeJumpType, runOpcodeJumpSrc, True)
  , ("Jumpdest", "", runOpcodeJumpdestType, runOpcodeJumpdestSrc, True)
  , ("Slt", "", runOpcodeSltType, runOpcodeSltSrc, True)
  , ("stackOp2", " cost f", runOpcodeStackOp2Type, runOpcodeStackOp2Src, False)
  , ("next", "", runOpcodeNextType, runOpcodeNextSrc, False)
  ]
