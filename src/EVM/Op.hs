{-# LANGUAGE DataKinds #-}

module EVM.Op
  ( Op (..)
  , opString
  ) where

import EVM.Types

import Data.Word (Word8)
import Numeric (showHex)

data Op
  = OpStop
  | OpAdd
  | OpMul
  | OpSub
  | OpDiv
  | OpSdiv
  | OpMod
  | OpSmod
  | OpAddmod
  | OpMulmod
  | OpExp
  | OpSignextend
  | OpLt
  | OpGt
  | OpSlt
  | OpSgt
  | OpEq
  | OpIszero
  | OpAnd
  | OpOr
  | OpXor
  | OpNot
  | OpByte
  | OpShl
  | OpShr
  | OpSar
  | OpSha3
  | OpAddress
  | OpBalance
  | OpOrigin
  | OpCaller
  | OpCallvalue
  | OpCalldataload
  | OpCalldatasize
  | OpCalldatacopy
  | OpCodesize
  | OpCodecopy
  | OpGasprice
  | OpExtcodesize
  | OpExtcodecopy
  | OpReturndatasize
  | OpReturndatacopy
  | OpExtcodehash
  | OpBlockhash
  | OpCoinbase
  | OpTimestamp
  | OpNumber
  | OpPrevRandao
  | OpGaslimit
  | OpChainid
  | OpSelfbalance
  | OpBaseFee
  | OpPop
  | OpMload
  | OpMstore
  | OpMstore8
  | OpSload
  | OpSstore
  | OpJump
  | OpJumpi
  | OpPc
  | OpMsize
  | OpGas
  | OpJumpdest
  | OpCreate
  | OpCall
  | OpStaticcall
  | OpCallcode
  | OpReturn
  | OpDelegatecall
  | OpCreate2
  | OpRevert
  | OpSelfdestruct
  | OpDup !Word8
  | OpSwap !Word8
  | OpLog !Word8
  | OpPush (Expr EWord)
  | OpUnknown Word8
  deriving (Show, Eq)

intToOpName:: Int -> String
intToOpName a =
  case a of
   1 -> "STOP"
   1 -> "ADD"
   1 -> "MUL"
   1 -> "SUB"
   1 -> "DIV"
   1 -> "SDIV"
   1 -> "MOD"
   1 -> "SMOD"
   1 -> "ADDMOD"
   1 -> "MULMOD"
   1 -> "EXP"
   1 -> "SIGNEXTEND"
   1 -> "LT"
   1 -> "GT"
   1 -> "SLT"
   1 -> "SGT"
   1 -> "EQ"
   1 -> "ISZERO"
   1 -> "AND"
   1 -> "OR"
   1 -> "XOR"
   1 -> "NOT"
   1 -> "BYTE"
   1 -> "SHL"
   1 -> "SHR"
   1 -> "SAR"
   1 -> "SHA3"
   1 -> "ADDRESS"
   1 -> "BALANCE"
   1 -> "ORIGIN"
   1 -> "CALLER"
   1 -> "CALLVALUE"
   1 -> "CALLDATALOAD"
   1 -> "CALLDATASIZE"
   1 -> "CALLDATACOPY"
   1 -> "CODESIZE"
   1 -> "CODECOPY"
   1 -> "GASPRICE"
   1 -> "EXTCODESIZE"
   1 -> "EXTCODECOPY"
   1 -> "RETURNDATASIZE"
   1 -> "RETURNDATACOPY"
   1 -> "EXTCODEHASH"
   1 -> "BLOCKHASH"
   1 -> "COINBASE"
   1 -> "TIMESTAMP"
   1 -> "NUMBER"
   1 -> "PREVRANDAO"
   1 -> "GASLIMIT"
   1 -> "CHAINID"
   1 -> "SELFBALANCE"
   1 -> "BASEFEE"
   1 -> "POP"
   1 -> "MLOAD"
   1 -> "MSTORE"
   1 -> "MSTORE8"
   1 -> "SLOAD"
   1 -> "SSTORE"
   1 -> "JUMP"
   1 -> "JUMPI"
   1 -> "PC"
   1 -> "MSIZE"
   1 -> "GAS"
   1 -> "JUMPDEST"
   1 -> "CREATE"
   1 -> "CALL"
   1 -> "STATICCALL"
   1 -> "CALLCODE"
   1 -> "RETURN"
   1 -> "DELEGATECALL"
   1 -> "CREATE2"
   1 -> "SELFDESTRUCT"
   1 -> "DUP"
   1 -> "SWAP"
   1 -> "LOG"
   1 -> "PUSH "
   1 -> "REVERT"
   1 -> "INVALID"
   1 -> "UNKNOWN "

opString :: (Integral a, Show a) => (a, Op) -> String
opString (i, o) = let showPc x | x < 0x10 = '0' : showHex x ""
                               | otherwise = showHex x ""
                  in showPc i <> " " ++ case o of
  OpStop -> "STOP"
  OpAdd -> "ADD"
  OpMul -> "MUL"
  OpSub -> "SUB"
  OpDiv -> "DIV"
  OpSdiv -> "SDIV"
  OpMod -> "MOD"
  OpSmod -> "SMOD"
  OpAddmod -> "ADDMOD"
  OpMulmod -> "MULMOD"
  OpExp -> "EXP"
  OpSignextend -> "SIGNEXTEND"
  OpLt -> "LT"
  OpGt -> "GT"
  OpSlt -> "SLT"
  OpSgt -> "SGT"
  OpEq -> "EQ"
  OpIszero -> "ISZERO"
  OpAnd -> "AND"
  OpOr -> "OR"
  OpXor -> "XOR"
  OpNot -> "NOT"
  OpByte -> "BYTE"
  OpShl -> "SHL"
  OpShr -> "SHR"
  OpSar -> "SAR"
  OpSha3 -> "SHA3"
  OpAddress -> "ADDRESS"
  OpBalance -> "BALANCE"
  OpOrigin -> "ORIGIN"
  OpCaller -> "CALLER"
  OpCallvalue -> "CALLVALUE"
  OpCalldataload -> "CALLDATALOAD"
  OpCalldatasize -> "CALLDATASIZE"
  OpCalldatacopy -> "CALLDATACOPY"
  OpCodesize -> "CODESIZE"
  OpCodecopy -> "CODECOPY"
  OpGasprice -> "GASPRICE"
  OpExtcodesize -> "EXTCODESIZE"
  OpExtcodecopy -> "EXTCODECOPY"
  OpReturndatasize -> "RETURNDATASIZE"
  OpReturndatacopy -> "RETURNDATACOPY"
  OpExtcodehash -> "EXTCODEHASH"
  OpBlockhash -> "BLOCKHASH"
  OpCoinbase -> "COINBASE"
  OpTimestamp -> "TIMESTAMP"
  OpNumber -> "NUMBER"
  OpPrevRandao -> "PREVRANDAO"
  OpGaslimit -> "GASLIMIT"
  OpChainid -> "CHAINID"
  OpSelfbalance -> "SELFBALANCE"
  OpBaseFee -> "BASEFEE"
  OpPop -> "POP"
  OpMload -> "MLOAD"
  OpMstore -> "MSTORE"
  OpMstore8 -> "MSTORE8"
  OpSload -> "SLOAD"
  OpSstore -> "SSTORE"
  OpJump -> "JUMP"
  OpJumpi -> "JUMPI"
  OpPc -> "PC"
  OpMsize -> "MSIZE"
  OpGas -> "GAS"
  OpJumpdest -> "JUMPDEST"
  OpCreate -> "CREATE"
  OpCall -> "CALL"
  OpStaticcall -> "STATICCALL"
  OpCallcode -> "CALLCODE"
  OpReturn -> "RETURN"
  OpDelegatecall -> "DELEGATECALL"
  OpCreate2 -> "CREATE2"
  OpSelfdestruct -> "SELFDESTRUCT"
  OpDup x -> "DUP" ++ show x
  OpSwap x -> "SWAP" ++ show x
  OpLog x -> "LOG" ++ show x
  OpPush x -> case x of
    Lit x' -> "PUSH 0x" ++ (showHex x' "")
    _ -> "PUSH " ++ show x
  OpRevert -> "REVERT"
  OpUnknown x -> case x of
    254 -> "INVALID"
    _ -> "UNKNOWN " ++ (showHex x "")
