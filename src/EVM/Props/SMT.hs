{-# Language OverloadedStrings #-}
{-# Language TemplateHaskell #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language PatternSynonyms #-}

module EVM.Props.SMT where

import Data.ByteString (ByteString)
import Data.Char
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List (intersperse, foldl')
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Builder.Linear
import GHC.Generics
import FlatParse.Basic


-- Types -------------------------------------------------------------------------------------------


-- smt statements are s-expressions
data SMT
  = L [SMT]
  | A Text
  deriving (Eq, Show, Read, Generic, Hashable)

-- scripts are lists of smt statements
newtype Script = Script [SMT]


-- Serialization -----------------------------------------------------------------------------------


class Serializable a where
  serialize :: a -> Builder

instance Serializable SMT where
  serialize (A t) = fromText t
  serialize (L xs)
    = parens
    . foldl' (<>) mempty
    . intersperse (fromChar ' ')
    . fmap serialize
    $ xs

instance Serializable Script where
  serialize (Script cmds) = foldl' (<>) mempty
                          . intersperse "\n"
                          . fmap serialize
                          $ cmds

parens :: Builder -> Builder
parens b = "(" <> b <> ")"

pprint :: Script -> Text
pprint = runBuilder . serialize


-- Parsing -----------------------------------------------------------------------------------------

ws, open, close :: Parser () ()
ws      = skipMany $(switch [| case _ of " " -> pure (); "\n" -> pure () |])
open    = $(char '(') >> ws
close   = $(char ')') >> ws

-- | characters allowed in a name
nameChar :: Parser () Char
nameChar = satisfy (`elem` ("~!@$%^&*_-+=<>.?/" :: String))

ident :: Parser () SMT
ident = do
  c <- nameChar <|> (satisfy isLatinLetter)
  cs <- many (satisfy isAlphaNum <|> nameChar)
  ws
  pure (A . T.pack $ c : cs)

sexp :: Parser () SMT
sexp = branch open go ident
  where
    go = do
      s <- many sexp
      close
      pure (L s)

src :: Parser () SMT
src = do
  s <- sexp
  eof
  pure s

parseSMT :: ByteString -> Result () SMT
parseSMT = runParser src


-- CSE ---------------------------------------------------------------------------------------------


-- takes an smt statement and pulls common subexpressions out into let bound variables
eliminate :: SMT -> SMT
eliminate = undefined
  where
    -- produce a map with counts of each subexpression
    count :: HashMap SMT Int -> SMT -> HashMap SMT Int
    count acc e@(A _) = HM.alter (maybe (Just 0) (Just . (+ 1))) e acc

