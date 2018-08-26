module HoTT.Types.Name where

import Prelude

import Data.Array (snoc)
import Data.Either (Either(..), either)
import Data.String (joinWith)

data Name
  = Anonymous
  | MkString Name String
  | MkNumeral Name Int

nameParts :: Name -> Array (Either String Int)
nameParts Anonymous = []
nameParts (MkString n s) = snoc (nameParts n) (Left s)
nameParts (MkNumeral n i) = snoc (nameParts n) (Right i)

instance showName :: Show Name where
  show = nameParts >>> map (either identity show) >>> joinWith "."
