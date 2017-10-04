module Externs.Parse.AKind where

import Prelude

import Control.Plus (empty)
import Data.Argonaut (Json, toArray, toString)
import Data.Argonaut as A
import Data.Array ((!!))
import Data.Const (Const(..))
import Data.Functor.Mu (roll)
import Data.Functor.Variant (inj)
import Data.Maybe (Maybe(..))
import Data.StrMap as StrMap
import Externs.Parse.Names (parseProper, parseQualified)
import Prim.Repr (kindArrow, rowKind)
import Types (AKindV, _name)

prop :: String -> Json -> Maybe Json
prop i = A.foldJsonObject Nothing (StrMap.lookup i)

parseAKind :: Json -> Maybe AKindV
parseAKind j = do
  tag <- toString =<< prop "tag" j
  contents <- prop "contents" j
  case tag of
    "NamedKind" ->
      parseQualified parseProper contents <#>
        Const >>> inj _name >>> roll
    "FunKind" -> do
      a <- toArray contents
      a0 <- a !! 0
      a1 <- a !! 1
      kindArrow <$> parseAKind a0 <*> parseAKind a1
    "Row" ->
      rowKind <$> parseAKind contents
    _ -> empty
