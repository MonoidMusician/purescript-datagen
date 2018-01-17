module KindChecking where

import Prelude

import Combinators (certainty)
import Control.Comonad (extract)
import Data.Bifunctor (lmap)
import Data.Const (Const(..))
import Data.Either (Either(..), hush, note)
import Data.Eq (class Eq1)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu(In), roll, transMu, unroll)
import Data.Functor.Product (Product(..))
import Data.Functor.Variant (FProxy, SProxy(..), VariantF)
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.Lens (review)
import Data.List.Lazy (uncons)
import Data.Map (Map, lookup)
import Data.Maybe (Maybe(..), maybe)
import Data.Newtype (class Newtype, un, unwrap)
import Data.Pair (Pair(..))
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), fst, snd)
import Externs.Codec.TypeData (TypeKindData)
import Matryoshka (cata)
import Prim.Repr (primKinds)
import Reprinting (showAKind)
import Types (AKindV, AKindVF, ATypeV, ATypeVM, Ident, Proper, Qualified, AKindVM, _app, _fun, _name, _row, _var)
import Zippers (ParentCtxs, fromDF, fromParentCtx)

type Kinded = Tuple ATypeV AKindV
newtype KindChecked = KindChecked Kinded
derive instance newtypeKindChecked :: Newtype KindChecked _

type KindedM = Tuple ATypeVM AKindV
newtype KindCheckedM = KindCheckedM KindedM
derive instance newtypeKindCheckedM :: Newtype KindCheckedM _

type AllTypeKindData = Tuple TypeKindData (Map Ident AKindV)

type KindErrorVRBase t k r =
  ( unknownName :: FProxy (Const (Qualified Proper))
  , unknownVar  :: FProxy (Const Ident)
  , doesNotMatch :: FProxy (Const (Tuple k k))
  , needsFunctor :: FProxy (Const (Tuple t k))
  , whileInferring :: FProxy (Tuple t)
  , whileChecking  :: FProxy (Tuple (Tuple t k))
  | r )
type KindErrorVFBase t k r = VariantF (KindErrorVRBase t k r)
type KindErrorVBase t k r = Mu (KindErrorVFBase t k r)

type KindError t k = KindErrorVBase t k ()
type KindErrorM t k = KindErrorVBase t k ( typeHole :: FProxy (Const Unit) )

unknownName :: forall t k r. Qualified Proper -> KindErrorVBase t k r
unknownName = roll <<< VF.inj (SProxy :: SProxy "unknownName") <<< Const
unknownVar :: forall t k r. Ident -> KindErrorVBase t k r
unknownVar = roll <<< VF.inj (SProxy :: SProxy "unknownVar") <<< Const
doesNotMatch :: forall t k r. k -> k -> KindErrorVBase t k r
doesNotMatch k1 k2 = roll $ VF.inj (SProxy :: SProxy "doesNotMatch") $ Const $ Tuple k1 k2
needsFunctor :: forall t k r. t -> k -> KindErrorVBase t k r
needsFunctor t k = roll $ VF.inj (SProxy :: SProxy "needsFunctor") $ Const $ Tuple t k
whileInferring :: forall t k r. t -> KindErrorVBase t k r -> KindErrorVBase t k r
whileInferring t e = roll $ VF.inj (SProxy :: SProxy "whileInferring") $ Tuple t e
whileChecking :: forall t k r. t -> k -> KindErrorVBase t k r -> KindErrorVBase t k r
whileChecking t k e = roll $ VF.inj (SProxy :: SProxy "whileChecking") $ Tuple (Tuple t k) e
typeHole :: forall t k r. KindErrorVBase t k ( typeHole :: FProxy (Const Unit) | r )
typeHole = roll $ VF.inj (SProxy :: SProxy "typeHole") $ Const unit

showKindError :: forall t. (t -> String) -> KindErrorM t AKindV -> String
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
  # VF.on (SProxy :: SProxy "typeHole")
    (\_ -> "Type hole has no discernable kind")

-- | Check that `t` has kind `k` in the given environment.
kindCheck :: Kinded -> AllTypeKindData -> Either (KindError ATypeV AKindV) KindChecked
kindCheck (Tuple t k) env = lmap (whileChecking t k) $
  inferKind t env >>= (matchKind (KindChecked (Tuple t k)) <@> k)
-- | Infer the kind of `t` in the given environment
inferKind :: ATypeV -> AllTypeKindData -> Either (KindError ATypeV AKindV) AKindV
inferKind t env = lmap (whileInferring t) $
  ( VF.case_
  # VF.on _name
    (un Const >>> \q -> lookup q (fst env) # note (unknownName q))
  # VF.on _app
    (\(Pair fnc arg) -> do
      karg <- inferKind arg env
      kfnc <- inferKind fnc env
      (VF.on _fun \(Pair ka kr) -> matchKind kr karg ka)
        (VF.default (Left $ needsFunctor fnc kfnc))
        (unroll kfnc)
    )
  # VF.on _fun
    (\(Pair arg res) -> do
      _ <- kindCheck (Tuple arg primKinds."Type") env
      _ <- kindCheck (Tuple res primKinds."Type") env
      pure primKinds."Type"
    )
  # VF.on _var
    (un Const >>> \v -> lookup v (snd env) # note (unknownVar v))
  ) $ unroll t

-- | Check that `t` has kind `k` in the given environment.
kindCheckM :: KindedM -> AllTypeKindData -> Either (KindErrorM ATypeVM AKindV) KindCheckedM
kindCheckM (Tuple t k) _ | In (Compose Nothing) <- t =
  Right (KindCheckedM (Tuple t k))
kindCheckM (Tuple t k) env = lmap (whileChecking t k) $
  inferKindM t env >>= (matchKind (KindCheckedM (Tuple t k)) <@> k)
-- | Infer the kind of `t` in the given environment
inferKindM :: ATypeVM -> AllTypeKindData -> Either (KindErrorM ATypeVM AKindV) AKindV
inferKindM t env = lmap (whileInferring t) $
  ( VF.case_
  # VF.on _name
    (un Const >>> \q -> lookup q (fst env) # note (unknownName q))
  # VF.on _app
    (\(Pair fnc arg) -> do
      karg <- inferKindM arg env
      kfnc <- inferKindM fnc env
      (VF.on _fun \(Pair ka kr) -> matchKind kr karg ka)
        (VF.default (Left $ needsFunctor fnc kfnc))
        (unroll kfnc)
    )
  # VF.on _fun
    (\(Pair arg res) -> do
      _ <- kindCheckM (Tuple arg primKinds."Type") env
      _ <- kindCheckM (Tuple res primKinds."Type") env
      pure primKinds."Type"
    )
  # VF.on _var
    (un Const >>> \v -> lookup v (snd env) # note (unknownVar v))
  # maybe (Left typeHole)
  )
  (un Compose $ unroll t)

-- | Todo: emit partial kinds
inferKindHole :: ParentCtxs ATypeVM -> AllTypeKindData -> AKindVM
inferKindHole pars env = uncons pars # maybe hole \{ head: par, tail: pars' } ->
  ( VF.case_
  # VF.on _name (un Const >>> absurd)
  # VF.on _var (un Const >>> absurd)
  # VF.on _app case _ of
      Tuple false r ->
        let
          from = inferKindMM r env
          to = inferKindHole pars' env
        in roll $ Compose $ Just $ VF.inj _fun $ Pair from to
      Tuple true l ->
        inferKindMM l env # unroll >>> un Compose >>>
          ( VF.default hole
          # VF.on _fun (\(Pair from _) -> from)
          # maybe hole
          )
  # VF.on _fun (pure (review certainty primKinds."Type"))
  ) (extract $ un Product $ fromDF $ fromParentCtx par)
  where
    hole = roll $ Compose Nothing
    inferKindMM :: ATypeVM -> AllTypeKindData -> AKindVM
    inferKindMM t env = case hush (inferKindM t env) of
      Nothing -> hole
      Just k -> review certainty k

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

matchKind :: forall a t r. a -> AKindV -> AKindV -> Either (KindErrorVBase t AKindV r) a
matchKind _ k1 k2 | k1 `not eqKind` k2 = Left $ doesNotMatch k1 k2
matchKind a _ _ = Right a
