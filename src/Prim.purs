module Prim.Repr where

import Data.Const (Const(..))
import Data.Functor.Mu (Mu, roll)
import Data.Functor.Variant (FProxy, VariantF, inj)
import Data.Identity (Identity(..))
import Data.NonEmpty ((:|))
import Data.Pair (Pair(..))
import Data.Tuple (Tuple(..))
import Prelude (($), (<<<))
import Types (AKindV, Module(..), Proper(..), Qualified(..), ATypeV, _fun, _name, _row)

kindArrow :: AKindV -> AKindV -> AKindV
kindArrow arg res = roll $ inj _fun $ Pair arg res

rowKind :: AKindV -> AKindV
rowKind = roll <<< inj _row <<< Identity

typeArg :: AKindV -> AKindV
typeArg = kindArrow primKinds."Type"

functor :: AKindV
functor = typeArg primKinds."Type"

bifunctor :: AKindV
bifunctor = typeArg $ typeArg primKinds."Type"

prim :: Module
prim = Module (Proper "Prim" :| [])

primitive :: forall v. String ->
  Mu (VariantF ( name :: FProxy (Const (Qualified Proper)) | v ))
primitive = roll <<< inj _name <<< Const <<< Qualified prim <<< Proper

primTypes ::
  { "Function" :: Tuple AKindV ATypeV
  , "Array"    :: Tuple AKindV ATypeV
  , "Record"   :: Tuple AKindV ATypeV
  , "Int"      :: Tuple AKindV ATypeV
  , "Number"   :: Tuple AKindV ATypeV
  , "String"   :: Tuple AKindV ATypeV
  , "Char"     :: Tuple AKindV ATypeV
  , "Boolean"  :: Tuple AKindV ATypeV
  }
primTypes =
  { "Function": Tuple bifunctor $ primitive "Function"
  , "Array": Tuple functor $ primitive "Array"
  , "Record": Tuple (kindArrow (rowKind primKinds."Type") primKinds."Type") $ primitive "Record"
  , "Int": Tuple primKinds."Type" $ primitive "Int"
  , "Number": Tuple primKinds."Type" $ primitive "Number"
  , "String": Tuple primKinds."Type" $ primitive "String"
  , "Char": Tuple primKinds."Type" $ primitive "Char"
  , "Boolean": Tuple primKinds."Type" $ primitive "Boolean"
  }

primKinds ::
  { "Type"   :: AKindV
  , "Symbol" :: AKindV
  }
primKinds =
  { "Type": primitive "Type"
  , "Symbol": primitive "Symbol"
  }
