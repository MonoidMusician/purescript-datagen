module Externs.Parse.TypeData where

import Prelude

import Data.Array (unsnoc)
import Data.Codec.Argonaut (JsonCodec)
import Data.Lens (Prism', prism')
import Data.Map (Map)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), joinWith, split)
import Externs.Parse.AKind (codecAKindV)
import Externs.Parse.Names (codecStrMapish, ensureProper, parseModule)
import Types (AKindV, Proper, Qualified(..))

type TypeKindData = Map (Qualified Proper) AKindV

prismPQ :: Prism' String (Qualified Proper)
prismPQ = prism' show \s -> do
  let parts = split (Pattern ".") s
  { init, last } <- unsnoc parts
  typ <- ensureProper last
  let mod = parseModule (joinWith "." init)
  pure case mod of
    Nothing -> Unqualified typ
    Just m  -> Qualified m typ

codecTypeKindData :: JsonCodec TypeKindData
codecTypeKindData = codecStrMapish prismPQ codecAKindV
