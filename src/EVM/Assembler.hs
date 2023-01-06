{-# LANGUAGE DataKinds #-}

module EVM.Assembler where

import EVM.Op
import EVM.Types
import qualified EVM.Expr as Expr

import qualified Data.Vector as V
import Data.Vector (Vector)

assemble :: [Op] -> Vector (Expr Byte)
assemble os = V.concatMap go (V.fromList os)
  where
    go :: Op -> Vector (Expr Byte)
    go = \case
      OpStop -> V.singleton (LitByte 0x00)
      OpAdd -> V.singleton (LitByte 0x01)
      OpMul -> V.singleton (LitByte 0x02)
      OpSub -> V.singleton (LitByte 0x03)
      OpDiv -> V.singleton (LitByte 0x04)
      OpSdiv -> V.singleton (LitByte 0x05)
      OpMod -> V.singleton (LitByte 0x06)
      OpSmod -> V.singleton (LitByte 0x07)
      OpAddmod -> V.singleton (LitByte 0x08)
      OpMulmod -> V.singleton (LitByte 0x09)
      OpExp -> V.singleton (LitByte 0x0A)
      OpSignextend -> V.singleton (LitByte 0x0B)
      OpLt -> V.singleton (LitByte 0x10)
      OpGt -> V.singleton (LitByte 0x11)
      OpSlt -> V.singleton (LitByte 0x12)
      OpSgt -> V.singleton (LitByte 0x13)
      OpEq -> V.singleton (LitByte 0x14)
      OpIszero -> V.singleton (LitByte 0x15)
      OpAnd -> V.singleton (LitByte 0x16)
      OpOr -> V.singleton (LitByte 0x17)
      OpXor -> V.singleton (LitByte 0x18)
      OpNot -> V.singleton (LitByte 0x19)
      OpByte -> V.singleton (LitByte 0x1A)
      OpShl -> V.singleton (LitByte 0x1B)
      OpShr -> V.singleton (LitByte 0x1C)
      OpSar -> V.singleton (LitByte 0x1D)
      OpSha3 -> V.singleton (LitByte 0x20)
      OpAddress -> V.singleton (LitByte 0x30)
      OpBalance -> V.singleton (LitByte 0x31)
      OpOrigin -> V.singleton (LitByte 0x32)
      OpCaller -> V.singleton (LitByte 0x33)
      OpCallvalue -> V.singleton (LitByte 0x34)
      OpCalldataload -> V.singleton (LitByte 0x35)
      OpCalldatasize -> V.singleton (LitByte 0x36)
      OpCalldatacopy -> V.singleton (LitByte 0x37)
      OpCodesize -> V.singleton (LitByte 0x38)
      OpCodecopy -> V.singleton (LitByte 0x39)
      OpGasprice -> V.singleton (LitByte 0x3A)
      OpExtcodesize -> V.singleton (LitByte 0x3B)
      OpExtcodecopy -> V.singleton (LitByte 0x3C)
      OpReturndatasize -> V.singleton (LitByte 0x3D)
      OpReturndatacopy -> V.singleton (LitByte 0x3E)
      OpExtcodehash -> V.singleton (LitByte 0x3F)
      OpBlockhash -> V.singleton (LitByte 0x40)
      OpCoinbase -> V.singleton (LitByte 0x41)
      OpTimestamp -> V.singleton (LitByte 0x42)
      OpNumber -> V.singleton (LitByte 0x43)
      OpPrevRandao -> V.singleton (LitByte 0x44)
      OpGaslimit -> V.singleton (LitByte 0x45)
      OpChainid -> V.singleton (LitByte 0x46)
      OpSelfbalance -> V.singleton (LitByte 0x47)
      OpBaseFee -> V.singleton (LitByte 0x48)
      OpPop -> V.singleton (LitByte 0x50)
      OpMload -> V.singleton (LitByte 0x51)
      OpMstore -> V.singleton (LitByte 0x52)
      OpMstore8 -> V.singleton (LitByte 0x53)
      OpSload -> V.singleton (LitByte 0x54)
      OpSstore -> V.singleton (LitByte 0x55)
      OpJump -> V.singleton (LitByte 0x56)
      OpJumpi -> V.singleton (LitByte 0x57)
      OpPc -> V.singleton (LitByte 0x58)
      OpMsize -> V.singleton (LitByte 0x59)
      OpGas -> V.singleton (LitByte 0x5A)
      OpJumpdest -> V.singleton (LitByte 0x5B)
      OpCreate -> V.singleton (LitByte 0xF0)
      OpCall -> V.singleton (LitByte 0xF1)
      OpStaticcall -> V.singleton (LitByte 0xFA)
      OpCallcode -> V.singleton (LitByte 0xF2)
      OpReturn -> V.singleton (LitByte 0xF3)
      OpDelegatecall -> V.singleton (LitByte 0xF4)
      OpCreate2 -> V.singleton (LitByte 0xF5)
      OpRevert -> V.singleton (LitByte 0xFD)
      OpSelfdestruct -> V.singleton (LitByte 0xFF)
      OpDup n ->
        if 1 <= n && n <= 16
        then V.singleton (LitByte (0x80 + (n - 1)))
        else error $ "Internal Error: invalid argument to OpDup: " <> show n
      OpSwap n ->
        if 1 <= n && n <= 16
        then V.singleton (LitByte (0x90 + (n - 1)))
        else error $ "Internal Error: invalid argument to OpSwap: " <> show n
      OpLog n ->
        if 0 <= n && n <= 4
        then V.singleton (LitByte (0xA0 + n))
        else error $ "Internal Error: invalid argument to OpLog: " <> show n
      -- we just always assemble OpPush into PUSH32
      OpPush wrd -> V.cons (LitByte 0x7f) (V.fromList [Expr.indexWord (Lit i) wrd | i <- [0..31]])
      OpUnknown o -> V.singleton (LitByte o)
