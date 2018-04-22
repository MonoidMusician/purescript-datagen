module KindChecking where

import Prelude

import Combinators (fear)
import Control.Comonad (extract)
import Control.Monad.State (State, evalState, get, modify)
import Control.Plus (empty)
import Data.Const (Const(..))
import Data.Eq (class Eq1)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(In), transMu)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.List.Lazy (uncons)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Pair (Pair(..))
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), fst, snd)
import Externs.Codec.TypeData (TypeKindData)
import Matryoshka (class Corecursive, cata, embed, project)
import Prim.Repr (primKinds)
import Reprinting (showAKind)
import Types (AKindV, AKindVF, AKindVM, AKindVR, ATypeV, ATypeVM, Ident, Proper, Qualified, _fun, _name, _row)
import Zippers (ParentCtxs, fromDF, fromParentCtx)
import Complex.Validation as CV

type Kinded = Tuple ATypeV AKindV
newtype KindChecked = KindChecked Kinded
derive instance newtypeKindChecked :: Newtype KindChecked _

type KindedM = Tuple ATypeVM AKindV
newtype KindCheckedM = KindCheckedM KindedM
derive instance newtypeKindCheckedM :: Newtype KindCheckedM _

type AllTypeKindData = Tuple TypeKindData (Map Ident AKindV)

type Hm = Tuple (forall e. e) Unit
type CONST a = FProxy (Const a)
type TUPLE a = FProxy (Tuple a)
type KindErrorVRBase t k r =
  ( unknownName :: CONST (Qualified Proper)
  , unknownVar  :: CONST Ident
  , doesNotMatch :: CONST (Tuple k k)
  , needsFunctor :: CONST (Tuple t k)
  , whileInferring :: TUPLE t
  , whileChecking  :: TUPLE (Tuple t k)
  | r )
type KindErrorVFBase t k r = VariantF (KindErrorVRBase t k r)
type KindErrorVBase t k r = Mu (KindErrorVFBase t k r)

type KindError t k = KindErrorVBase t k ()
type ComputeKind t k = CV.ERrors (KindErrorVRBase t k ())

unknownName :: forall t k r. Qualified Proper -> KindErrorVBase t k r
unknownName = embed <<< VF.inj (SProxy :: SProxy "unknownName") <<< Const
unknownVar :: forall t k r. Ident -> KindErrorVBase t k r
unknownVar = embed <<< VF.inj (SProxy :: SProxy "unknownVar") <<< Const
doesNotMatch :: forall t k r. k -> k -> KindErrorVBase t k r
doesNotMatch k1 k2 = embed $ VF.inj (SProxy :: SProxy "doesNotMatch") $ Const $ Tuple k1 k2
needsFunctor :: forall t k r. t -> k -> KindErrorVBase t k r
needsFunctor t k = embed $ VF.inj (SProxy :: SProxy "needsFunctor") $ Const $ Tuple t k
whileInferring :: forall t k r. t -> KindErrorVBase t k r -> KindErrorVBase t k r
whileInferring t e = embed $ VF.inj (SProxy :: SProxy "whileInferring") $ Tuple t e
whileChecking :: forall t k r. t -> k -> KindErrorVBase t k r -> KindErrorVBase t k r
whileChecking t k e = embed $ VF.inj (SProxy :: SProxy "whileChecking") $ Tuple (Tuple t k) e

showKindError :: forall t. (t -> String) -> KindError t AKindV -> String
showKindError showt = cata $ VF.case_
  # VF.on (SProxy :: SProxy "unknownName")
    (un Const >>> \q -> "Unknown name " <> show q)
  # VF.on (SProxy :: SProxy "unknownVar")
    (un Const >>> \v -> "Unknown variable " <> show v)
  # VF.on (SProxy :: SProxy "doesNotMatch")
    (un Const >>> \(Tuple k1 k2) -> "Kind " <> showAKind k1 <> " does not match " <> showAKind k2)
  # VF.on (SProxy :: SProxy "needsFunctor")
    (un Const >>> \(Tuple t k) -> "Type " <> showt t <> " needs to be a functor from kind " <> showAKind k)
  # VF.on (SProxy :: SProxy "whileInferring")
    (\(Tuple t e) -> "An error occurred while inferring the kind of " <> showt t <> ": " <> e)
  # VF.on (SProxy :: SProxy "whileChecking")
    (\(Tuple (Tuple t k) e) -> "An error occurred while checking that " <> showt t <> " has kind " <> showAKind k <> ": " <> e)

emjJ ::
  forall t f s r r'.
    IsSymbol s =>
    RowCons s (FProxy f) r' r =>
    Functor f =>
    Corecursive t (Compose Maybe (VariantF r)) =>
  SProxy s -> f t -> t
emjJ s = embed <<< Compose <<< Just <<< VF.inj s

hole :: forall t f. Corecursive t (Compose Maybe f) => t
hole = embed (Compose Nothing)

extractCase ::
  forall s f v' v a r.
    IsSymbol s =>
    RowCons s (FProxy f) v' v =>
  SProxy s -> VariantF v a -> r -> (f a -> r) -> r
extractCase label value df handle =
  VF.on label handle (const df) value

extractCaseIn ::
  forall s f v' v a r.
    IsSymbol s =>
    RowCons s (FProxy f) v' v =>
  SProxy s -> Mu (VariantF v) -> r -> (f (Mu (VariantF v)) -> r) -> r
extractCaseIn label value df handle =
  extractCase label (project value) df handle

requireCaseIn ::
  forall s f v' v e t es' es a a.
    IsSymbol s =>
    RowCons s (FProxy f) v' v =>
    IsSymbol e =>
    RowCons e (FProxy (Const t)) es' es =>
  Mu (VariantF v) -> SProxy s ->
  SProxy e -> t ->
  (f (Mu (VariantF v)) -> a) ->
  CV.ERrors es a
requireCaseIn value label errL errV handle =
  extractCaseIn label value (CV.errorSimple errL errV) (pure <<< handle)

-- | Check that `t` has kind `k` in the given environment.
kindCheck :: Kinded -> AllTypeKindData -> ComputeKind ATypeV AKindV KindChecked
kindCheck (Tuple t k) env = CV.errorScoped (SProxy :: SProxy "whileChecking") (Tuple t k) $
  inferKind t env >>= \k' -> KindChecked (Tuple t k) <$ matchKind k' k
-- | Infer the kind of `t` in the given environment
inferKind :: ATypeV -> AllTypeKindData -> ComputeKind ATypeV AKindV AKindV
inferKind t env = CV.errorScoped (SProxy :: SProxy "whileInferring") t $
  VF.match
    { name:
        un Const >>> \(q :: Qualified Proper) ->
          CV.note (unknownName q) $
            Map.lookup q (fst env)
    , var:
        un Const >>> \(v :: Ident) ->
          CV.note (unknownVar v) $
            Map.lookup v (snd env)
    , app: \(Pair fnc arg) -> do
        -- infer the kinds of the functor and argument independently
        Tuple kfnc karg <- Tuple <$> inferKind fnc env <*> inferKind arg env
        -- make sure the functor has a fun kind
        join $ requireCaseIn kfnc _fun
          -- if not, emit the needsFunctor error
          (SProxy :: SProxy "needsFunctor") (Tuple fnc kfnc)
          -- but if its kind is of the form (a -> r), make sure a matches the
          -- kind of the argument, then return the resultant kind `r`.
          \(Pair ka kr) -> kr <$ matchKind karg ka
    , fun: \(Pair arg res) ->
        -- a function is of kind Type, given two arguments of kind Type
        primKinds."Type"
        <$ kindCheck (Tuple arg primKinds."Type") env
        <* kindCheck (Tuple res primKinds."Type") env
    } $ project t

-- | Check that `t` has kind `k` in the given environment.
kindCheckM :: KindedM -> AllTypeKindData -> ComputeKind ATypeVM AKindV KindCheckedM
kindCheckM (Tuple t k) env = CV.errorScoped (SProxy :: SProxy "whileChecking") (Tuple t k) $
  inferKindM t env >>= case _ of
    Nothing -> KindCheckedM (Tuple t k) # pure
    Just k' -> KindCheckedM (Tuple t k) <$ matchKind k' k
-- | Infer the kind of the partial expression `t` in the given environment.
-- | Returns `Nothing` if the kind is unconstrained (i.e. may be anything).
inferKindM :: ATypeVM -> AllTypeKindData -> ComputeKind ATypeVM AKindV (Maybe AKindV)
inferKindM t env = CV.errorScoped (SProxy :: SProxy "whileInferring") t $
  (VF.match
    { name: map pure <<<
        un Const >>> \(q :: Qualified Proper) ->
          CV.note (unknownName q) $
            Map.lookup q (fst env)
    , var: map pure <<<
        un Const >>> \(v :: Ident) ->
          CV.note (unknownVar v) $
            Map.lookup v (snd env)
    , app: \(Pair fnc arg) -> do
        Tuple kfnc karg <- Tuple <$> inferKindM fnc env <*> inferKindM arg env
        case kfnc of
          Nothing -> pure Nothing
          Just kfnc' ->
            join $ requireCaseIn kfnc' _fun
              (SProxy :: SProxy "needsFunctor") (Tuple fnc kfnc')
              \(Pair ka kr) ->
                case karg of
                  Nothing -> pure (pure kr)
                  Just karg' -> pure kr <$ matchKind karg' ka
    , fun: \(Pair arg res) ->
        -- a function is of kind Type, given two arguments of kind Type
        pure primKinds."Type"
        <$ kindCheckM (Tuple arg primKinds."Type") env
        <* kindCheckM (Tuple res primKinds."Type") env
    } # maybe (pure Nothing)) $ un Compose $ project t

-- | Todo: emit partial kinds
inferKindHole :: ParentCtxs ATypeVM -> AllTypeKindData -> AKindVM
inferKindHole pars env = uncons pars # maybe hole \{ head: par, tail: pars' } ->
  VF.match
    { name: un Const >>> absurd, var: un Const >>> absurd
    , app: case _ of
        Tuple false r ->
          let
            from = inferKindMM r env
            to = inferKindHole pars' env
          in emjJ _fun $ Pair from to
        Tuple true l ->
          inferKindMM l env # project >>> un Compose >>>
            ( VF.default hole
            # VF.on _fun (\(Pair from _) -> from)
            # maybe hole
            )
    , fun: \_ -> fear primKinds."Type"
    } $ extract $ un Product $ fromDF $ fromParentCtx par
  where
    -- FIXME
    inferKindMM :: ATypeVM -> AllTypeKindData -> AKindVM
    inferKindMM t env = case join $ CV.hush (inferKindM t env) of
      Nothing -> hole
      Just k -> fear k

matchPartialKind :: AKindVM -> AKindV -> Boolean
matchPartialKind (In (Compose Nothing)) _ = true
matchPartialKind (In (Compose (Just k))) (In k') =
  ( VF.case_
  # VF.on _name (
    \(Const q) ->
      ( VF.default false
      # VF.on _name (eq q <<< unwrap)
      ) k')
  # VF.on _row (
    \(Identity r) ->
      ( VF.default false
      # VF.on _row (matchPartialKind r <<< unwrap)
      ) k')
  # VF.on _fun \(Pair l r) ->
    ( VF.default false
    # VF.on _fun \(Pair x y) ->
        matchPartialKind l x && matchPartialKind r y
    ) k'
  ) k

-- | An associative, commutative, idempotent "join" operation on partial kinds.
-- | Looks to replace a hole with a full type, won't merge leafs that are unequal.
-- | I wish there was a way to abstract this for a class of functors ... hm ...
-- | Maybe variants of distributive functors.
-- |
-- | Examples:
-- | ```
-- | (_        \/ _ -> _) ==> _ -> _
-- | (  a -> _ \/ _ -> b) ==> a -> b
-- | (# a -> _ \/ a -> b) fails
-- | ```
mergeKindMs :: AKindVM -> AKindVM -> Maybe AKindVM
mergeKindMs (In (Compose Nothing)) k = pure k
mergeKindMs k (In (Compose Nothing)) = pure k
mergeKindMs l@(In (Compose (Just k1))) (In (Compose (Just k2))) =
  let fail = empty in
  ( VF.case_
  # VF.on _name (
    \(Const q1) ->
      ( VF.default fail
      # VF.on _name \(Const q2) ->
        if q1 == q2 then pure l else fail
      ) k2)
  # VF.on _row (
    \(Identity r1) ->
      ( VF.default fail
      # VF.on _row \(Identity r2) ->
        mergeKindMs r1 r2 <#> \r ->
          In (Compose (Just (VF.inj _row (Identity r))))
      ) k2)
  # VF.on _fun (
    \(Pair i1 o1) ->
      ( VF.default fail
      # VF.on _fun \(Pair i2 o2) ->
        let combPair i o = In (Compose (Just (VF.inj _fun (Pair i o))))
        in combPair <$> mergeKindMs i1 i2 <*> mergeKindMs o1 o2
      ) k2)
  ) k1

type CheckAKindR =
  ( unify :: FProxy Pair
  , var :: FProxy (Const Int)
  | AKindVR
  )
type CheckAKindF = VariantF CheckAKindR
type CheckAKind = Mu CheckAKindF

_unify = SProxy :: SProxy "unify"

type Fresh = State Int

fresh :: Fresh Int
fresh = get <* modify ((+) 1)

runFresh :: forall a. Fresh a -> a
runFresh = evalState <@> 0

{-




byAssumption :: forall a. a -> WhyKChecked a
byAssumption = ?help

inferKindsIn :: forall t. Traversable t =>
  Map Ident (WhyKChecked CheckAKindM) ->
  t ATypeVM ->
  Either WhyNotKChecked (Map Ident (WhyKChecked CheckAKindM))
inferKindsIn = ...

inferKindsOf :: Array Ident -> Array ATypeVM -> Either WhyNotKChecked (Map Ident (WhyKChecked AKindVM))
inferKindsOf vars usages =
  let
    startWith = Map.fromFoldable $ runFresh $ for vars
      \v -> Tuple v <<< byAssumption <<< emjJ _var <$> fresh
  in do
    applied <- inferKindsIn startWith usages
    result <- examineImplications startWith applied
    doubleCheck result usages

defaultKinds :: WhyKChecked AKindVM -> WhyKChecked AKindV
defaultKinds = map (assume primKinds."Type")
-}

vfEqCase ::
  forall sym fnc v' v v1' v1 a.
    IsSymbol sym =>
    Eq (fnc a) =>
    RowCons sym (FProxy fnc) v' v =>
    RowCons sym (FProxy fnc) v1' v1 =>
  SProxy sym ->
  (VariantF v' a -> VariantF v1 a -> Boolean) ->
  VariantF v a -> VariantF v1 a -> Boolean
vfEqCase k = VF.on k (\a -> VF.default false # VF.on k (eq a))

newtype Eq1AKindVF a = Eq1AKindVF (AKindVF a)
derive instance newtypeEq1AKindVF :: Newtype (Eq1AKindVF a) _
derive newtype instance functorEq1AKindVF :: Functor Eq1AKindVF
instance eq1AKindVF :: Eq1 Eq1AKindVF where
  eq1 = (VF.case_ # vfEqCase _name # vfEqCase _row # vfEqCase _fun) `on` unwrap

eqKind :: AKindV -> AKindV -> Boolean
eqKind = eq `on` transMu Eq1AKindVF

matchKind :: forall t r. AKindV -> AKindV -> CV.ERrors (KindErrorVRBase t AKindV r) Unit
matchKind k1 k2 | k1 `not eqKind` k2 = CV.erroring $ doesNotMatch k1 k2
matchKind _ _ = pure unit
