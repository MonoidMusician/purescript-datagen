module Annot where

import Prelude

import Data.Maybe (Maybe, maybe)

data Annot = FnParen | AppParen | FnAppParen | None
derive instance eqAnnot :: Eq Annot
needsFnParen :: Annot -> Boolean
needsFnParen FnParen = true
needsFnParen FnAppParen = true
needsFnParen _ = false
needsAppParen :: Annot -> Boolean
needsAppParen AppParen = true
needsAppParen FnAppParen = true
needsAppParen _ = false
mayNeedFnParen :: Maybe Annot -> Boolean
mayNeedFnParen = maybe false needsFnParen
mayNeedAppParen :: Maybe Annot -> Boolean
mayNeedAppParen = maybe false needsAppParen
-- instance heytingAlgebraAnnot :: HeytingAlgebra Annot
