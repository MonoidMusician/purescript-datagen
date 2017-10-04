module Externs.Parse.Names where

import Prelude

import Control.MonadZero (empty)
import Data.Argonaut (Json)
import Data.Argonaut as A
import Data.Array (drop, (!!))
import Data.Char (fromCharCode)
import Data.Char.Unicode (isUpper)
import Data.Maybe (Maybe)
import Data.NonEmpty ((:|))
import Data.String.CodePoints (codePointAt, codePointToInt)
import Data.Traversable (traverse)
import Types (Module(..), Proper(..), Qualified(..))

parseQualified :: forall a. (Json -> Maybe a) -> Json -> Maybe (Qualified a)
parseQualified f j = do
  a <- A.toArray j
  m <- parseModule =<< a !! 0
  n <- f =<< a !! 1
  pure (Qualified m n)

parseModule :: Json -> Maybe Module
parseModule j = do
  a <- A.toArray j
  head <- parseProper =<< a !! 0
  rest <- traverse parseProper $ drop 1 a
  pure $ Module (head :| rest)

ensureUpper :: String -> Maybe String
ensureUpper s = do
  c <- codePointAt 0 s
  if isUpper (fromCharCode (codePointToInt c))
    then pure s
    else empty

parseProper :: Json -> Maybe Proper
parseProper = A.toString >=> ensureUpper >>> map Proper
