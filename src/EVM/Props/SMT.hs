{-# Language OverloadedStrings #-}
{-# Language ApplicativeDo #-}
{-# Language TemplateHaskell #-}
{-# Language DeriveAnyClass #-}
{-# Language DeriveGeneric #-}
{-# Language PatternSynonyms #-}

module EVM.Props.SMT where

import Control.Monad.Identity
import Control.Monad.State
import Data.ByteString (ByteString)
import Data.Char
import Data.Hashable
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HM
import Data.List (intersperse, foldl', sortOn)
import Data.Ord (Down(..))
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
  deriving (Eq, Show)


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
  serialize (Script cmds)
    = foldl' (<>) mempty
    . intersperse "\n"
    . fmap serialize
    $ cmds

parens :: Builder -> Builder
parens b = "(" <> b <> ")"

pprint :: Serializable s => s -> Text
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


-- Transformations ---------------------------------------------------------------------------------


-- | Merge all asserts into a single conjunction
mergeAsserts :: Script -> Script
mergeAsserts (Script cmds) = Script $ go [] [] cmds
  where
    go :: [SMT] -> [SMT] -> [SMT] -> [SMT]
    go rest asserts [] = (reverse rest) <> [L [A "assert", eliminate (L (A "and" : asserts))]]
    go rest asserts (c : cs) = case c of
      L [A "assert", e] -> go rest (e : asserts) cs
      e -> go (e : rest) asserts cs

-- | Pull every subexpression out into it's own let bound variable
eliminate :: SMT -> SMT
eliminate expr = res
  where
    (bound, (vars, _)) = runState (mapSMTM extract expr) (mempty, 0)
    res = declare bound (invert vars)

    -- assigns each subexpression a unique variable number.
    -- Since mapSMTM is bottom up, this will be in topological order.
    extract :: SMT -> State (HashMap SMT Int, Int) SMT
    extract e@(A _) = pure e
    extract e@(L _) = do
      (vs, c) <- get
      case HM.lookup e vs of
        Just _ -> pure e
        Nothing -> do
          put (HM.insert e c vs, c + 1)
          pure (mkname c)

    -- declares each subexpression in order as a let bound variable
    declare :: SMT -> [(Int, SMT)] -> SMT
    declare s (sortOn (Down . fst) -> vs) = foldl' (\acc (i,e) -> L [A "let", L [L [mkname i, e]], acc]) s vs

    mkname n = A $ "elim_" <> tshow n
    invert = map (\(x,y) -> (y,x)) . HM.toList


-- Utils -------------------------------------------------------------------------------------------


tshow :: Show a => a -> Text
tshow = T.pack . show

mapSMTM :: Monad m => (SMT -> m SMT) -> SMT -> m SMT
mapSMTM f e@(A _) = f e
mapSMTM f (L ls) = do
  ls' <- mapM f ls
  f (L ls')

mapSMT :: (SMT -> SMT) -> SMT -> SMT
mapSMT f e = runIdentity (mapSMTM (Identity . f) e)

test :: Script
test = Script
  [ L [A "set-logic", A "ALL"]
  , L [A "declare-const", A "x", A "Int"]
  , L [A "declare-const", A "y", A "Int"]
  , L [A "assert", L [A ">=", A "x", A "y"]]
  , L [A "assert", L [A ">=", A "x", A "110"]]
  ]
