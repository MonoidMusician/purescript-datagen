module Externs.Parse where

import Prelude

import Data.Argonaut (Json)
import Data.Argonaut as A
import Data.Array (elem, filter, mapMaybe)
import Data.Maybe (Maybe(..))
import Data.StrMap as StrMap
import Data.Tuple (Tuple(..), fst)
import Externs.Parse.AKind (parseAKind)
import Externs.Parse.Names (parseProper)
import Types (Proper, AKindV)

prop :: String -> Json -> Maybe Json
prop i = A.foldJsonObject Nothing (StrMap.lookup i)

extractTypes :: Array Json -> Array (Tuple Proper AKindV)
extractTypes = mapMaybe $ prop "EDType" >=> \o ->
  Tuple
    <$> (parseProper =<< prop "edTypeName" o)
    <*> (parseAKind =<< prop "edTypeKind" o)

externsTypes :: Json -> Maybe (Array (Tuple Proper AKindV))
externsTypes = prop "efDeclarations" >=> A.toArray >>> map extractTypes

externsJustTypes :: Json -> Maybe (Array (Tuple Proper AKindV))
externsJustTypes = prop "efDeclarations" >=> A.toArray >>> map do
  types <- extractTypes
  classes <- mapMaybe $ prop "EDClass" >=> prop "edClassName" >=> parseProper
  let isClass t = t `elem` classes
  pure (filter (not isClass <<< fst) types)
