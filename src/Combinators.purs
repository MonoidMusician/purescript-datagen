module Combinators where

import Types

import Control.Apply (lift2)
import Data.Array (uncons, unsnoc)
import Data.Const (Const(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant as VF
import Data.Lens (Prism', prism')
import Data.Map (insert) as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Monoid (mempty)
import Data.Newtype (un)
import Data.NonEmpty (NonEmpty, (:|))
import Data.Pair (Pair(..))
import Data.Symbol (class IsSymbol, SProxy)
import Data.Traversable (class Traversable)
import Data.Tuple (Tuple(..))
import Data.Variant.Internal (FProxy)
import Matryoshka (transAna, transCata, transCataM)
import Prelude (class Applicative, class Functor, class Monad, compose, pure, ($), (<<<), (<@>))

onlyType :: Proper -> Import
onlyType = Type <@> mempty
dataModule :: Array Proper -> Module
dataModule rest = Module (Proper "Data" :| rest)
dataImport :: Proper -> Tuple Module ImportModule
dataImport name =
  pure (Type name mempty) `importFrom`
    dataModule (pure name)
importAll :: ImportModule
importAll = ImportModule (pure mempty) mempty
importAllFrom :: Module -> Tuple Module ImportModule
importAllFrom = Tuple <@> importAll
importFrom :: Imports -> Module -> Tuple Module ImportModule
importFrom is = Tuple <@> ImportModule (pure is) mempty

aType :: ATypeVF ATypeV -> ATypeV
aType = roll

aTypeConst ::
  forall sym a bleh.
    IsSymbol sym =>
    RowCons sym (FProxy (Const a)) bleh ATypeVR =>
  SProxy sym -> a -> ATypeV
aTypeConst k a = aType $ VF.inj k $ Const a

aTypePair ::
  forall sym bleh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
  SProxy sym -> ATypeV -> ATypeV -> ATypeV
aTypePair k a b  = aType $ VF.inj k $ Pair a b

aTypeProduct ::
  forall sym f g bleh.
    IsSymbol sym =>
    Functor f =>
    Functor g =>
    RowCons sym (FProxy (Product f g)) bleh ATypeVR =>
  SProxy sym -> f ATypeV -> g ATypeV -> ATypeV
aTypeProduct k a b = aType $ VF.inj k $ Product $ Tuple a b

aTypeApp :: ATypeV -> ATypeV -> ATypeV
aTypeApp = aTypePair _app

aTypeFunction :: ATypeV -> ATypeV -> ATypeV
aTypeFunction = aTypePair _fun

aTypeName :: Qualified Proper -> ATypeV
aTypeName = aTypeConst _name

aTypeVar :: Ident -> ATypeV
aTypeVar = aTypeConst _var

typeAbsType :: Ident -> TypeAbs
typeAbsType = TypeAbs <@> Nothing

newType :: Proper -> ATypeV -> DataTypeDef
newType name typ = DataTypeDef mempty $ SumType [Tuple name $ pure typ]

namedNewType :: Proper -> ATypeV -> Tuple Proper DataTypeDef
namedNewType = lift2 compose Tuple newType

alias :: Proper -> NonEmpty Array (Qualified Proper) -> Tuple Proper DataTypeDef
alias name as = Tuple name $ DataTypeDef mempty $ TypeAlias (chainl aTypeApp as)

chainl :: (ATypeV -> ATypeV -> ATypeV) -> NonEmpty Array (Qualified Proper) -> ATypeV
chainl app (fn :| args) = go (aTypeName fn) args
  where
    go :: ATypeV -> Array (Qualified Proper) -> ATypeV
    go f as = case uncons as of
      Nothing -> f
      Just { head, tail } ->
        go (app f (aTypeName head)) tail

chainr :: (ATypeV -> ATypeV -> ATypeV) -> NonEmpty Array (Qualified Proper) -> ATypeV
chainr app (fn :| args) = go (aTypeName fn) args
  where
    go :: ATypeV -> Array (Qualified Proper) -> ATypeV
    go f as = case unsnoc as of
      Nothing -> f
      Just { init, last } ->
        go (app (aTypeName last) f) init

qualifyP :: Proper -> Qualified Proper
qualifyP p@(Proper name) = case name of
  "NonEmpty" -> qualifyData p
  "Either" -> qualifyData p
  "Map" -> qualifyData p
  "String" -> prim p
  _ -> Unqualified p

qualifyData :: Proper -> Qualified Proper
qualifyData p = Qualified (dataModule $ pure p) p

prim :: Proper -> Qualified Proper
prim = Qualified (Module (Proper "Prim" :| mempty))

qualify :: Tuple Module ImportModule -> Imports -> Tuple Module ImportModule
qualify (Tuple name (ImportModule mims mp)) is =
  Tuple name (ImportModule mims mp')
  where
    mp' = Map.insert (Module (lastOf name :| [])) is mp

-- | Transform between a partial tree (which may stop prematurely, with
-- | `Compose Nothing`) and a full one.
certainty :: forall f. Traversable f => Prism' (Mu (Compose Maybe f)) (Mu f)
certainty = prism' fear certify

-- | Fear breeds uncertainty...
fear :: forall f g. Functor f => Applicative g =>
  Mu f -> Mu (Compose g f)
fear = transAna (Compose <<< pure)

-- | ... But there is a chance at regaining it.
certify :: forall f g. Traversable f => Monad g => Traversable g =>
  Mu (Compose g f) -> g (Mu f)
certify = transCataM (un Compose)

-- | Assumptions are dangerous.
assume :: forall f. Functor f => Mu f -> Mu (Compose Maybe f) -> Mu f
assume e = transCata (fromMaybe ue <<< un Compose) where ue = unroll e
