{-# Language OverloadedStrings #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language PatternSynonyms #-}

module EVM.Props.SMT where

import Debug.Trace

import Data.Hashable
import Data.List (intersperse, foldl')
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.Builder.Linear
import Data.Void
import GHC.Generics
import GHC.Natural
import Text.Megaparsec
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Witch


-- Types -------------------------------------------------------------------------------------------


-- smt statements are s-expressions
data SMT
  = L [SMT]
  | Id    Text
  | SInt  Integer
  | SBV   Natural Natural
  | SBool Bool
  deriving (Eq, Show, Read, Generic, Hashable)

-- scripts are lists of smt statements
newtype Script = Script [SMT]


-- Serialization -----------------------------------------------------------------------------------


class Serializable a where
  serialize :: a -> Builder

instance Serializable SMT where
  serialize (Id t) = fromText t
  serialize (SInt val) = fromText . T.pack . show $ val
  serialize (SBool True) = "true"
  serialize (SBool False) = "false"
  serialize (SBV sz val)
    = serialize (L
      [ Id "_"
      , Id ("bv" <> (T.pack $ show (into @Integer val)))
      , Id (T.pack $ show (into sz :: Integer))
      ])
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


type Parser = Parsec Void Text

-- | Space Consumer.
sc :: Parser ()
sc = L.space
  space1
  (L.skipLineComment ";")
  empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

brackets :: Parser a -> Parser a
brackets = between (symbol "(") (symbol ")")

-- | parse a lexeme into a boolean
bool :: Parser Bool
bool = lexeme $ False <$ string "false" <|> True <$ string "true"

-- | parse a lexeme into a signed integer
integer :: Parser Integer
integer = label "integer" $ L.signed sc (lexeme L.decimal)

-- | parse a bitvector literal: (_ bv<v> <sz>)
bitvec :: Parser (Natural, Natural)
bitvec = label "bitvector" $ brackets $ do
  _ <- symbol "_"
  _ <- char 'b'
  _ <- char 'v'
  v <- integer
  sz <- integer
  case (tryFrom v, tryFrom sz) of
    (Right v', Right sz') -> pure (sz', v')
    _ -> error "TODO"

-- | special chars allowed in smt names
nameChar :: Parser Char
nameChar = oneOf @[] "~!@$%^&*_-+=<>.?/"

-- | parse a lexeme into a
identifier :: Parser String
identifier = label "identifier" $ lexeme $ do
  c <- nameChar <|> letterChar
  cs <- many (alphaNumChar <|> nameChar)
  pure (c : cs)

list :: Parser SMT
list = label "S-expression" $ brackets (L <$> many smt)

smt :: Parser SMT
smt = choice
  [ uncurry SBV <$> try bitvec
  , list
  , SInt <$> integer
  , SBool <$> bool
  , Id . T.pack <$> identifier
  ]

parseSMT :: Text -> Either Text SMT
parseSMT input = case parse (between sc eof smt) "" input of
  Left err -> Left . T.pack $ errorBundlePretty err
  Right output -> Right output

testParser :: Text -> IO ()
testParser input = case parseSMT input of
  Left e -> T.putStrLn e
  Right s -> do
    print s
    T.putStrLn . runBuilder . serialize $ s


-- Patterns ----------------------------------------------------------------------------------------


pattern Add x y = L [Id "add", x, y]
pattern Sub x y = L [Id "sub", x, y]

pattern BvAdd x y = L [Id "bvadd", x, y]
pattern BvSub x y = L [Id "bvsub", x, y]

pattern And x y = L [Id "and", x, y]
pattern Eq x y = L [Id "=", x, y]
pattern Neq x y = L [Id "distinct", x, y]
