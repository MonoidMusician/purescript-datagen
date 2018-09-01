module HoTT.Types.Name where

import Prelude

import Data.Array (snoc)
import Data.Either (Either(..), either)
import Data.String (joinWith)

data Name
  = Anonymous
  | MkString Name String
  | MkNumeral Name Int

derive instance eqName :: Eq Name
derive instance ordName :: Ord Name

parts :: Name -> Array (Either String Int)
parts Anonymous = []
parts (MkString n s) = snoc (parts n) (Left s)
parts (MkNumeral n i) = snoc (parts n) (Right i)

fromString :: String -> Name
fromString s = MkString Anonymous s

instance showName :: Show Name where
  show = parts >>> map (either identity show) >>> joinWith "."
