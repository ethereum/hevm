{-# LANGUAGE TemplateHaskell, ImplicitParams #-}

module EVM.Opcodes where

import Optics.Core
import Optics.State
import Optics.State.Operators
import Optics.Zoom
import Optics.Operators.Unsafe


import Control.Monad.ST (ST)
import Control.Monad.State.Strict (StateT, get)
import Witch.From (From)
import Witch (into)
import Data.Word (Word8)

import EVM
import EVM.Types
import EVM.FeeSchedule (FeeSchedule (..))
import EVM.Expr qualified as Expr

runOpcodeAdd :: (VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()
runOpcodeAdd = do
  vm <- get
  let
    FeeSchedule {..} = vm.block.schedule
  stackOp2 g_verylow Expr.add

runOpcodeAddSrc :: String
runOpcodeAddSrc = "do\n\
\  vm <- get\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  stackOp2 g_verylow Expr.add"

runOpcodeAddType :: String
runOpcodeAddType = "(VMOps t, ?op::Word8) => StateT (VM t s) (ST s) ()"

{-# INLINE runOpcodeDup #-}
runOpcodeDup :: (From source Int, VMOps t, ?op::Word8) =>
                source -> StateT (VM t s) (ST s) ()
runOpcodeDup i = do
  vm <- get
  let
    stk  = vm.state.stack
    FeeSchedule {..} = vm.block.schedule
  case preview (ix (into i - 1)) stk of
    Nothing -> underrun
    Just y ->
      limitStack 1 $
        burn g_verylow $ do
          next
          pushSym y

runOpcodeDupSrc :: String
runOpcodeDupSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  case preview (ix (into i - 1)) stk of\n\
\    Nothing -> underrun\n\
\    Just y ->\n\
\      limitStack 1 $\n\
\        burn g_verylow $ do\n\
\          next\n\
\          pushSym y"

runOpcodeDupType :: String
runOpcodeDupType = "(From source Int, VMOps t, ?op::Word8) => source -> StateT (VM t s) (ST s) ()"

runOpcodeSwap :: (?op::Word8, VMOps t, From source Int) => source -> StateT (VM t s) (ST s) ()
runOpcodeSwap i = do
  vm <- get
  let
    stk  = vm.state.stack
    FeeSchedule {..} = vm.block.schedule
  if length stk < (into i) + 1
    then underrun
    else
      burn g_verylow $ do
        next
        zoom (#state % #stack) $ do
          assign (ix 0) (stk ^?! ix (into i))
          assign (ix (into i)) (stk ^?! ix 0)

runOpcodeSwapSrc :: String
runOpcodeSwapSrc = "do\n\
\  vm <- get\n\
\  let stk = vm.state.stack\n\
\  let FeeSchedule {..} = vm.block.schedule\n\
\  if length stk < (into i) + 1\n\
\    then underrun\n\
\    else\n\
\      burn g_verylow $ do\n\
\        next\n\
\        zoom (#state % #stack) $ do\n\
\          assign (ix 0) (stk ^?! ix (into i))\n\
\          assign (ix (into i)) (stk ^?! ix 0)"

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

opcodesImpl :: [(String, String, String, String)]
opcodesImpl =
  [
    ("Add",  "", runOpcodeAddType, runOpcodeAddSrc)
  , ("Push0", "", runOpcodePush0Type, runOpcodePush0Src)
  , ("Stop", "", runOpcodeStopType, runOpcodeStopSrc)
  , ("Revert", "", runOpcodeRevertType, runOpcodeRevertSrc)
  , ("Dup", " i", runOpcodeDupType, runOpcodeDupSrc)
  , ("Swap", " i", runOpcodeSwapType, runOpcodeSwapSrc)
  ]
