module Zippers where

import Prelude

import Control.Apply (lift2)
import Control.Comonad (class Comonad)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT(..))
import Control.Extend (class Extend)
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Coproduct (Coproduct, left, right)
import Data.Functor.Product (Product(..), product)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VF
import Data.Identity (Identity)
import Data.Lazy (Lazy, defer, force)
import Data.Lens (Lens', lens, (^.))
import Data.List.Lazy (List, nil, uncons, (:))
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid.Additive (Additive)
import Data.Newtype (unwrap, wrap)
import Data.Pair (Pair(..))
import Data.StrMap (StrMap)
import Data.StrMap as StrMap
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (FProxy(..), RLProxy(..))
import Matryoshka (class Corecursive, class Recursive, Algebra, cata, embed, project)
import Recursion (Alg)
import Test.QuickCheck (class Arbitrary, class Coarbitrary, arbitrary, coarbitrary)
import Type.Row (class ListToRow, class RowToList, Cons, Nil, kind RowList)
import Types (ATypeV, ATypeVF, Ident, Proper, Qualified, _app, _fun, _name, _var)
import Unsafe.Coerce (unsafeCoerce)

type Tag = Tuple (Additive Int) (Additive Int)
type ATypeVC = Cofree ATypeVF Tag

class (Functor f, Functor f') <= Diff1 f f' | f -> f' where
  upF   :: forall x. ZF f x  ->       f x
  downF :: forall x.    f x  -> f (ZF f x)

downFTrivial ::
  forall f x.
    Functor f =>
    Diff1 f (Const Unit) =>
  f x -> f (ZF f x)
downFTrivial = map (pure (toDF (Const unit)) :<-: _)
upFTrivial ::
  forall f x.
    Applicative f =>
    Diff1 f (Const Unit) =>
  ZF f x -> f x
upFTrivial = (_ ^. _focusF) >>> pure

aroundF :: forall f f' f'' x. Diff1 f f' => Diff1 f' f'' => ZF f x  -> ZF f (ZF f x)
aroundF z@(c :<-: f) =
  (_ :<-: z) $ defer \_ ->toDF $
    downF (fromDF (force c)) <#> upZ
  where
    upZ :: ZF f' x -> ZF f x
    upZ z'@(_ :<-: x) = pure (toDF (upF z')) :<-: x

instance derivativeEnvT :: (Functor f, Diff1 f f') => Diff1 (EnvT e f) (EnvT e f') where
  downF (EnvT (Tuple e f)) = EnvT $ Tuple e $ downF f <#>
    injZF (EnvT <<< Tuple e)
  upF (dex :<-: x) =
    case fromDF (force dex) of
      EnvT (Tuple e dfx) ->
        EnvT $ Tuple e $ upF (pure (toDF' (FProxy :: FProxy f) dfx) :<-: x)

foreign import data DF :: (Type -> Type) -> Type -> Type
toDF' :: forall f f' x. Diff1 f f' => FProxy f -> f' x -> DF f x
toDF' _ = toDF
toDF :: forall f f' x. Diff1 f f' => f' x -> DF f x
toDF = unsafeCoerce
fromDF :: forall f f' x. Diff1 f f' => DF f x -> f' x
fromDF = unsafeCoerce
reDF :: forall f g f' x. Diff1 f f' => Diff1 g f' => DF f x -> DF g x
reDF = fromDF >>> toDF
reDF' :: forall f g f' x. Diff1 f f' => Diff1 g f' => FProxy g -> DF f x -> DF g x
reDF' p = fromDF >>> toDF' p
injDF :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall a. a ~> g a) -> DF f x -> DF (g f) x
injDF g = fromDF >>> g >>> toDF
liftDF :: forall f f' g g' x. Diff1 f f' => Diff1 g g' => (f' x -> g' x) -> DF f x -> DF g x
liftDF fg = fromDF >>> fg >>> toDF

instance functorDF :: Diff1 f f' => Functor (DF f) where
  map f = fromDF >>> map f >>> toDF

instance arbitraryDF :: ( Diff1 f f', Arbitrary (f' x), Arbitrary x ) => Arbitrary (DF f x) where
  arbitrary = toDF <$> arbitrary
instance coarbitraryDF :: ( Diff1 f f', Coarbitrary (f' x), Coarbitrary x ) => Coarbitrary (DF f x) where
  coarbitrary = fromDF >>> coarbitrary
instance eqDF :: ( Diff1 f f', Eq (f' x), Eq x ) => Eq (DF f x) where
  eq = eq `on` fromDF

data ZF f x = ZF (Lazy (DF f x)) x
infix 1 ZF as :<-:
toZF :: forall f f' x. Diff1 f f' => Tuple (f' x) x -> ZF f x
toZF (Tuple f'x x) = pure (toDF f'x) :<-: x
fromZF :: forall f f' x. Diff1 f f' => ZF f x -> Tuple (f' x) x
fromZF (f'x :<-: x) = Tuple (fromDF (force f'x)) x
reZF :: forall f g f' x. Diff1 f f' => Diff1 g f' => ZF f x -> ZF g x
reZF (f'x :<-: x) = reDF <$> f'x :<-: x
reZF' :: forall f g f' x. Diff1 f f' => Diff1 g f' => FProxy g -> ZF f x -> ZF g x
reZF' p (f'x :<-: x) = reDF' p <$> f'x :<-: x
injZF :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall a. a ~> g a) -> ZF f x -> ZF (g f) x
injZF g (f'x :<-: x) = injDF g <$> f'x :<-: x
injZF2 :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall a. a ~> g a) -> ZF f (ZF f x) -> ZF (g f) (ZF (g f) x)
injZF2 g (f'x :<-: x) = f'x <#> (injDF g >>> map (injZF g)) :<-: injZF g x
liftZF :: forall f f' g g' x. Diff1 f f' => Diff1 g g' => (f' x -> g' x) -> ZF f x -> ZF g x
liftZF fg (f'x :<-: x) = liftDF fg <$> f'x :<-: x

_contextF :: forall f x. Lens' (ZF f x) (Lazy (DF f x))
_contextF = lens (\(c :<-: _) -> c)
  \(_ :<-: f) c -> c :<-: f

_focusF :: forall f x. Lens' (ZF f x) x
_focusF = lens (\(_ :<-: f) -> f)
  \(c :<-: _) f -> c :<-: f

instance functorZF :: Diff1 f f' => Functor (ZF f) where
  map f (f'x :<-: x) = map f <$> f'x :<-: f x
instance extendZF :: (Diff1 f f', Diff1 f' f'') => Extend (ZF f) where
  extend f = map f <<< aroundF
instance comonadZF :: (Diff1 f f', Diff1 f' f'') => Comonad (ZF f) where
  extract (_ :<-: x) = x

instance arbitraryZF :: ( Diff1 f f', Arbitrary (f' x), Arbitrary x ) => Arbitrary (ZF f x) where
  arbitrary = lift2 ZF arbitrary arbitrary
instance coarbitraryZF :: ( Diff1 f f', Coarbitrary (f' x), Coarbitrary x ) => Coarbitrary (ZF f x) where
  coarbitrary (c :<-: f) = coarbitrary c <<< coarbitrary f
instance eqZF :: ( Diff1 f f', Eq (f' x), Eq x ) => Eq (ZF f x) where
  eq (c1 :<-: f1) (c2 :<-: f2) = eq c1 c2 && eq f1 f2

ixPair :: forall a b. (Boolean -> a -> b) -> Pair a -> Pair b
ixPair f (Pair l r) = Pair (f false l) (f true r)

ixDPair :: forall a. DPair a -> Boolean
ixDPair = fst

instance derivativeofTuple_keepsA :: Diff1 (Tuple a) (Const a) where
  downF (Tuple a b) = Tuple a $ pure (toDF (Const a)) :<-: b
  upF (a :<-: b) = Tuple (unwrap $ fromDF $ force a) b

type DPair = Tuple Boolean
instance derivativeofPair_isDPair :: Diff1 Pair (Tuple Boolean) where
  downF (Pair l r) = Pair
    (pure (toDF (Tuple false r)) :<-: l)
    (pure (toDF (Tuple true  l)) :<-: r)
  upF (c :<-: x) = case fromDF (force c), x of
    Tuple false r, l -> Pair l r
    Tuple true  l, r -> Pair l r

type DStrMap = Compose (Tuple String) StrMap
instance derivativeofStrMap_isDStrMap :: Diff1 StrMap (Compose (Tuple String) StrMap) where
  downF sm = sm # StrMap.mapWithKey \k v -> (_ :<-: v) $ defer \_ ->
    toDF (Compose (Tuple k (StrMap.delete k sm)))
  upF (c :<-: v) = case fromDF $ force c of
    Compose (Tuple k sm) ->
      StrMap.insert k v sm

instance derivativeofConst_isVoid :: Diff1 (Const a) (Const Void) where
  downF (Const a) = Const a
  upF (c :<-: _) = absurd $ unwrap $ fromDF $ force c

instance derivativeofIdentity_isUnit :: Diff1 Identity (Const Unit) where
  downF f = downFTrivial f
  upF z = upFTrivial z
instance derivativeofMaybe_isUnit :: Diff1 Maybe (Const Unit) where
  downF f = downFTrivial f
  upF z = upFTrivial z
instance derivativeofEither_isUnit :: Diff1 (Either e) (Const Unit) where
  downF f = downFTrivial f
  upF z = upFTrivial z

instance chainRule :: ( Functor f, Diff1 f f', Functor g, Diff1 g g' ) =>
  Diff1 (Compose f g) (Product (Compose f' g) g') where
  downF (Compose fg) = Compose $ downF fg <#> \(f'g :<-: g) ->
    downF g <#> liftZF \x ->
      product (Compose (fromDF (force f'g))) x
  upF (c :<-: x) = case lmap unwrap (unwrap (fromDF (force c))) of
    Tuple f'g g' -> Compose $ upF $ pure (toDF f'g) :<-:
      upF (pure (toDF g') :<-: x)

instance derivativeofCoproduct :: ( Functor f, Diff1 f f', Functor g, Diff1 g g' ) =>
  Diff1 (Coproduct f g) (Coproduct f' g') where
  downF = unwrap >>> bimap
    (downF >>> map (liftZF \f' -> left f'))
    (downF >>> map (liftZF \g' -> right g')) >>> wrap
  upF (c :<-: x) = case unwrap (fromDF (force c)) of
    Left  f' -> left  (upF (pure (toDF f') :<-: x))
    Right g' -> right (upF (pure (toDF g') :<-: x))

instance derivativeofProduct :: ( Functor f, Diff1 f f', Functor g, Diff1 g g' ) =>
  Diff1 (Product f g) (Coproduct (Product f' g) (Product f g')) where
  upF (c :<-: x) = case bimap unwrap unwrap (unwrap (fromDF (force c))) of
    Left (Tuple f' g) -> product
      (upF (pure (toDF f') :<-: x))
      (g)
    Right (Tuple f g') -> product
      (f)
      (upF (pure (toDF g') :<-: x))
  downF (Product (Tuple f g)) = product
    (downF f <#> liftZF \f' -> left  (product f' g))
    (downF g <#> liftZF \g' -> right (product f g'))

instance deriveofVariant_isVariantOfDerivatives ::
  ( RowToList r rl
  , DiffVariantF r r' rl rl'
  , ListToRow rl' r'
  ) => Diff1 (VariantF r) (VariantF r') where
  downF = unsafeCoerce (downV (RLProxy :: RLProxy rl))
  upF = unsafeCoerce (upV (RLProxy :: RLProxy rl))

type VF r' a = Tuple (Lazy (VariantF r' a)) a

class DiffVariantF (r :: # Type) (r' :: # Type) (rl :: RowList) (rl' :: RowList) | rl -> r r' rl' where
  upV :: forall a. RLProxy rl -> VF r' a -> VariantF r a
  downV :: forall a. RLProxy rl -> VariantF r a -> VariantF r (VF r' a)

instance diffVNil :: DiffVariantF () () Nil Nil where
  upV _ = fst >>> force >>> VF.case_
  downV _ = VF.case_

instance diffVCons ::
  ( IsSymbol sym
  , Functor f
  , Diff1 f f'
  , RowCons sym (FProxy f) n r
  , ListToRow rl n
  , DiffVariantF n n' rl rl'
  , RowToList n' rl'
  , RowCons sym (FProxy f') n' r'
  , Union n m r
  , Union n' m' r'
  ) => DiffVariantF r r' (Cons sym (FProxy f) rl) (Cons sym (FProxy f') rl') where
    upV _ (Tuple v x) = handleThis handleOther $ force v
      where
        sym = SProxy :: SProxy sym
        handleOther v' = VF.expand $
          upV (RLProxy :: RLProxy rl) (Tuple (pure v') x)
        handleThis = VF.on sym \f' ->
          VF.inj sym $ upF $
            pure (toDF' (FProxy :: FProxy f) f') :<-: x
    downV _ = handleThis handleOther
      where
        sym = SProxy :: SProxy sym
        handleOther v' = VF.expand $ lmap (map VF.expand) <$>
          downV (RLProxy :: RLProxy rl) v'
        handleThis = VF.on sym \f -> VF.inj sym $ downF f <#>
          \(c :<-: f') -> Tuple (defer \_ -> VF.inj sym (fromDF (force c))) f'

type ParentCtx t = DF (Alg t) t
type ParentCtxs t = List (ParentCtx t)
data ZRec t = ZRec (ParentCtxs t) t
infix 1 ZRec as :<<~:

toParentCtx ::
  forall t f f'.
    Recursive t f =>
    Corecursive t f =>
    Diff1 f f' =>
  DF f ~> DF (Alg t)
toParentCtx = unsafeCoerce

fromParentCtx ::
  forall t f f'.
    Recursive t f =>
    Corecursive t f =>
    Diff1 f f' =>
  DF (Alg t) ~> DF f
fromParentCtx = unsafeCoerce

downRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t -> f (ZRec t)
downRec (context :<<~: focus) = downF (project focus) <#>
  case _ of
    cx :<-: fc ->
      toParentCtx (force cx) : context :<<~: fc

upRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t -> Either t (ZRec t)
upRec (cxs :<<~: focus) =
  case uncons cxs of
    Nothing -> Left focus
    Just { head: cx, tail: context } -> Right $
      context :<<~: embed (upF (pure (fromParentCtx cx) :<-: focus))

tipRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  t -> ZRec t
tipRec = ZRec nil

topRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t -> t
topRec z = upRec z # either id topRec

downIntoRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  (f ~> Maybe) -> ZRec t -> ZRec t
downIntoRec f z = maybe z id (f (downRec z))

_contextRec :: forall t. Lens' (ZRec t) (List (DF (Alg t) t))
_contextRec = lens (\(c :<<~: _) -> c)
  \(_ :<<~: f) c -> c :<<~: f

_focusRec :: forall t. Lens' (ZRec t) t
_focusRec = lens (\(_ :<<~: f) -> f)
  \(c :<<~: _) f -> c :<<~: f

type ZipperVRec = ZRec ATypeVC

handleATypeVFByTypes :: forall a r.
  { "Const" :: forall b. Const b a -> r
  , "Pair" :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVFByTypes methods = handleATypeVF
  { name: methods."Const"
  , var: methods."Const"
  , fun: methods."Pair"
  , app: methods."Pair"
  }

handleATypeVFPairs :: forall a r.
  { name :: Const (Qualified Proper) a -> r
  , var :: Const Ident a -> r
  , "Pair" :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVFPairs methods = handleATypeVF
  { name: methods.name
  , var: methods.var
  , fun: methods."Pair"
  , app: methods."Pair"
  }

handleATypeVFConsts :: forall a r.
  { "Const" :: forall b. Const b a -> r
  , fun :: Pair a -> r
  , app :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVFConsts methods = handleATypeVF
  { name: methods."Const"
  , var: methods."Const"
  , fun: methods.fun
  , app: methods.app
  }

handleATypeVF :: forall a r.
  { name :: Const (Qualified Proper) a -> r
  , var :: Const Ident a -> r
  , fun :: Pair a -> r
  , app :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVF methods = VF.case_
  # VF.on _name methods.name
  # VF.on _var methods.var
  # VF.on _fun methods.fun
  # VF.on _app methods.app

handleATypeVFReinjector :: forall a r.
  { "Const" :: forall b.
      (Const b ~> ATypeVF) ->
      (DF (Const b) ~> DF ATypeVF) ->
      Const b a -> r
  , "Pair" ::
      (Pair ~> ATypeVF) ->
      (DF Pair ~> DF ATypeVF) ->
      Pair a -> r
  } -> ATypeVF a -> r
handleATypeVFReinjector methods = VF.case_
  # VF.on _name (methods."Const" (VF.inj _name) (fromDF >>> unwrap >>> absurd))
  # VF.on _var (methods."Const" (VF.inj _var) (fromDF >>> unwrap >>> absurd))
  # VF.on _fun (methods."Pair" (VF.inj _fun) (fromDF >>> VF.inj _fun >>> toDF))
  # VF.on _app (methods."Pair" (VF.inj _app) (fromDF >>> VF.inj _app >>> toDF))

simpleShowZRec :: ZRec ATypeV -> String
simpleShowZRec (context :<<~: focus) = go context cx
  where
    show1 :: Algebra ATypeVF String
    show1 = VF.match
      { name: unwrap >>> show
      , var: unwrap >>> show
      , fun: \(Pair l r) ->
          "(" <> l <> ") -> (" <> r <> ")"
      , app: \(Pair l r) ->
          "(" <> l <> ") (" <> r <> ")"
      }
    showAll = cata show1
    cx = showAll focus
    go ls s = case uncons ls of
      Nothing -> s
      Just { head: h, tail: r } -> go r $ VF.match
        { fun: showBranch " -> " s
        , app: showBranch " " s
        , name: unwrap >>> absurd
        , var: unwrap >>> absurd
        } $ fromDF $ fromParentCtx h
    showBranch :: String -> String -> DPair ATypeV -> String
    showBranch sep s (Tuple false a) = "{" <> s <> "}" <> sep <> showAll a
    showBranch sep s (Tuple true a) = showAll a <> sep <> "{" <> s <> "}"
