module EVM.Debug where

import EVM (bytecode)
import EVM.Expr (bufLength)
import EVM.Solidity (SrcMap(..), SourceCache(..))
import EVM.Types (Contract(..), Addr)

import Control.Arrow (second)
import Data.ByteString (ByteString)
import Data.ByteString qualified as ByteString
import Data.Map (Map)
import Data.Map qualified as Map
import Optics.Core
import Text.PrettyPrint.ANSI.Leijen
import Witch (unsafeInto)

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
    , (text "codehash", text (show c.codehash))
    , (text "balance", int (unsafeInto c.balance))
    , (text "nonce", int (unsafeInto c.nonce))
    ]

prettyContracts :: Map Addr Contract -> Doc
prettyContracts x =
  object
    (map (\(a, b) -> (text (show a), prettyContract b))
     (Map.toList x))

srcMapCodePos :: SourceCache -> SrcMap -> Maybe (FilePath, Int)
srcMapCodePos cache sm =
  fmap (second f) $ cache.files ^? ix sm.file
  where
    f v = ByteString.count 0xa (ByteString.take sm.offset v) + 1

srcMapCode :: SourceCache -> SrcMap -> Maybe ByteString
srcMapCode cache sm =
  fmap f $ cache.files ^? ix sm.file
  where
    f (_, v) = ByteString.take (min 80 sm.length) (ByteString.drop sm.offset v)
