{-# Language DataKinds #-}

module EVM.Debug where

import EVM          (Contract, nonce, balance, bytecode, codehash)
import EVM.Solidity (SrcMap, srcMapFile, srcMapOffset, srcMapLength, SourceCache(..))
import EVM.Types    (Addr)
import EVM.Expr     (bufLength)

import Control.Arrow   (second)
import Control.Lens
import Data.ByteString (ByteString)
import Data.Map        (Map)

import qualified Data.ByteString       as ByteString
import qualified Data.Map              as Map

import Text.PrettyPrint.ANSI.Leijen

data Mode = Debug | Run | JsonTrace deriving (Eq, Show)

object :: [(Doc, Doc)] -> Doc
object xs =
  group $ lbrace
    <> line
    <> indent 2 (sep (punctuate (char ';') [k <+> equals <+> v | (k, v) <- xs]))
    <> line
    <> rbrace

prettyContract :: Contract -> Doc
prettyContract c =
  object
    [ (text "codesize", text . show $ (bufLength (c ^. bytecode)))
    , (text "codehash", text (show (c ^. codehash)))
    , (text "balance", int (fromIntegral (c ^. balance)))
    , (text "nonce", int (fromIntegral (c ^. nonce)))
    ]

prettyContracts :: Map Addr Contract -> Doc
prettyContracts x =
  object
    (map (\(a, b) -> (text (show a), prettyContract b))
     (Map.toList x))

srcMapCodePos :: SourceCache -> SrcMap -> Maybe (FilePath, Int)
srcMapCodePos cache sm =
  fmap (second f) $ cache.files ^? ix sm.srcMapFile
  where
    f v = ByteString.count 0xa (ByteString.take (sm.srcMapOffset - 1) v) + 1

srcMapCode :: SourceCache -> SrcMap -> Maybe ByteString
srcMapCode cache sm =
  fmap f $ cache.files ^? ix sm.srcMapFile
  where
    f (_, v) = ByteString.take (min 80 sm.srcMapLength) (ByteString.drop sm.srcMapOffset v)
