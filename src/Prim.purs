module Prim.Repr where

import Data.Bifunctor (bimap)
import Data.Const (Const(..))
import Data.Functor.Mu (Mu, roll)
import Data.Functor.Variant (FProxy, VariantF, inj)
import Data.Identity (Identity(..))
import Data.Map (fromFoldable)
import Data.NonEmpty ((:|))
import Data.Pair (Pair(..))
import Data.Tuple (Tuple(..), fst)
import Externs.Codec.TypeData (TypeKindData)
import Prelude (($), (<$>), (<<<))
import Types (AKindV, Module(..), Proper(..), Qualified(..), ATypeV, _fun, _name, _row)

mPrim :: Module
mPrim = Module (Proper "Prim" :| [])

inPrim :: forall a. a -> Qualified a
inPrim = Qualified mPrim

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

primTypesMap :: TypeKindData
primTypesMap = fromFoldable $ bimap (inPrim <<< Proper) fst <$>
  [ Tuple "Function" primTypes."Function"
  , Tuple "Array" primTypes."Array"
  , Tuple "Record" primTypes."Record"
  , Tuple "Int" primTypes."Int"
  , Tuple "Number" primTypes."Number"
  , Tuple "String" primTypes."String"
  , Tuple "Char" primTypes."Char"
  , Tuple "Boolean" primTypes."Boolean"
  ]

primKinds ::
  { "Type"   :: AKindV
  , "Symbol" :: AKindV
  }
primKinds =
  { "Type": primitive "Type"
  , "Symbol": primitive "Symbol"
  }
