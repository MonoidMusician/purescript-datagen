module Zippers where

import Prelude

import Control.Comonad (class Comonad)
import Control.Comonad.Cofree (Cofree)
import Control.Comonad.Env (EnvT(..))
import Control.Extend (class Extend)
import Data.Bifunctor (bimap, lmap)
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VF
import Data.Lazy (Lazy, defer, force)
import Data.Lens (Lens', lens)
import Data.List (List(Nil), (:))
import Data.Maybe (Maybe, maybe)
import Data.Monoid.Additive (Additive)
import Data.Newtype (unwrap)
import Data.Pair (Pair(..))
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (FProxy(..), RLProxy(..))
import Matryoshka (class Corecursive, class Recursive, Algebra, cata, embed, project)
import Recursion (Alg)
import Type.Row (class ListToRow, class RowToList, Cons, Nil, kind RowList)
import Types (ATypeV, ATypeVF, Ident, Proper, Qualified, _app, _function, _name, _var)
import Unsafe.Coerce (unsafeCoerce)

type Tag = Tuple (Additive Int) (Additive Int)
type ATypeVC = Cofree ATypeVF Tag

class (Functor f, Functor f') <= Diff1 f f' | f -> f' where
  upF      ::  forall x. ZF f x  ->                 f x
  downF    ::  forall x.    f x  ->     f (Lazy (ZF f x))
  aroundF  ::  forall x. ZF f x  ->  ZF f       (ZF f x)

instance derivativeEnvT :: (Functor f, Diff1 f f') => Diff1 (EnvT e f) (EnvT e f') where
  downF (EnvT (Tuple e f)) = EnvT $ Tuple e $ downF f <#> map
    (injZF (EnvT <<< Tuple e))
  upF (dex :<-: x) =
    case fromDF dex of
      EnvT (Tuple e dfx) ->
        EnvT $ Tuple e $ upF (toDF' (FProxy :: FProxy f) dfx :<-: x)
  aroundF (dex :<-: x) =
    case fromDF dex of
      EnvT (Tuple e dfx) ->
        injZF2 (EnvT <<< Tuple e) $
        aroundF (toDF' (FProxy :: FProxy f) dfx :<-: x)

foreign import data DF :: (Type -> Type) -> Type -> Type
toDF' :: forall f f' x. Diff1 f f' => FProxy f -> f' x -> DF f x
toDF' _ = toDF
toDF :: forall f f' x. Diff1 f f' => f' x -> DF f x
toDF = unsafeCoerce
fromDF :: forall f f' x. Diff1 f f' => DF f x -> f' x
fromDF = unsafeCoerce
reDF :: forall f g f' x. Diff1 f f' => Diff1 g f' => DF f x -> DF g x
reDF = fromDF >>> toDF
injDF :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall x. x ~> g x) -> DF f x -> DF (g f) x
injDF g = fromDF >>> g >>> toDF

instance functorDF :: Diff1 f f' => Functor (DF f) where
  map f = fromDF >>> map f >>> toDF

data ZF f x = ZF (DF f x) x
infix 1 ZF as :<-:
toZF :: forall f f' x. Diff1 f f' => Tuple (f' x) x -> ZF f x
toZF (Tuple f'x x) = toDF f'x :<-: x
fromZF :: forall f f' x. Diff1 f f' => ZF f x -> Tuple (f' x) x
fromZF (f'x :<-: x) = Tuple (fromDF f'x) x
reZF :: forall f g f' x. Diff1 f f' => Diff1 g f' => ZF f x -> ZF g x
reZF (f'x :<-: x) = reDF f'x :<-: x
injZF :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall x. x ~> g x) -> ZF f x -> ZF (g f) x
injZF g (f'x :<-: x) = injDF g f'x :<-: x
injZF2 :: forall f f' g x. Diff1 f f' => Diff1 (g f) (g f') =>
  (forall x. x ~> g x) -> ZF f (ZF f x) -> ZF (g f) (ZF (g f) x)
injZF2 g (f'x :<-: x) = injDF g f'x <#> injZF g :<-: injZF g x

_contextF :: forall f x. Lens' (ZF f x) (DF f x)
_contextF = lens (\(c :<-: _) -> c)
  \(_ :<-: f) c -> c :<-: f

_focusF :: forall f x. Lens' (ZF f x) x
_focusF = lens (\(_ :<-: f) -> f)
  \(c :<-: _) f -> c :<-: f

instance functorZF :: Diff1 f f' => Functor (ZF f) where
  map f (f'x :<-: x) = map f f'x :<-: f x
instance extendZF :: Diff1 f f' => Extend (ZF f) where
  extend f = map f <<< aroundF
instance comonadZF :: Diff1 f f' => Comonad (ZF f) where
  extract (_ :<-: x) = x

ixPair :: forall a b. (Boolean -> a -> b) -> Pair a -> Pair b
ixPair f (Pair l r) = Pair (f false l) (f true r)

ixDPair :: forall a. DPair a -> Boolean
ixDPair (DPairL' _) = false
ixDPair (DPairR' _) = true

data DPair a = DPairL' a | DPairR' a
derive instance functorDPair :: Functor DPair
instance derivativeofPair_isDPair :: Diff1 Pair DPair where
  downF (Pair l r) = Pair
    (defer \_ -> toZF $ Tuple (DPairL' r) l)
    (defer \_ -> toZF $ Tuple (DPairR' l) r)
  upF z = case fromZF z of
    Tuple (DPairL' r) l -> Pair l r
    Tuple (DPairR' l) r -> Pair l r
  aroundF z = case fromZF z of
    Tuple (DPairL' r) l -> toZF $ flip Tuple z $
      DPairL' z
    Tuple (DPairR' l) r -> toZF $ flip Tuple z $
      DPairR' z

instance derivativeofConst_isVoid :: Diff1 (Const a) (Const Void) where
  downF (Const a) = Const a
  upF z = case fromZF z of
    Tuple (Const v) o -> absurd v
  aroundF z = case fromZF z of
    Tuple (Const v) o -> absurd v

instance deriveofVariant_isVariantOfDerivatives ::
  ( RowToList r rl
  , DiffVariantF r r' rl rl'
  , ListToRow rl' r'
  ) => Diff1 (VariantF r) (VariantF r') where
  downF = unsafeCoerce (downV (RLProxy :: RLProxy rl))
  upF = unsafeCoerce (upV (RLProxy :: RLProxy rl))
  aroundF = unsafeCoerce (aroundV (RLProxy :: RLProxy rl))

type VF r' a = Tuple (VariantF r' a) a

class DiffVariantF (r :: # Type) (r' :: # Type) (rl :: RowList) (rl' :: RowList) | rl -> r r' rl' where
  upV :: forall a. RLProxy rl -> VF r' a -> VariantF r a
  downV :: forall a. RLProxy rl -> VariantF r a -> VariantF r (Lazy (VF r' a))
  aroundV :: forall a. RLProxy rl -> VF r' a -> VF r' (VF r' a)

instance diffVNil :: DiffVariantF () () Nil Nil where
  upV _ = fst >>> VF.case_
  downV _ = VF.case_
  aroundV _ = fst >>> VF.case_

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
    upV _ (Tuple v x) = handleThis handleOther v
      where
        sym = SProxy :: SProxy sym
        handleOther v' = VF.expand $
          upV (RLProxy :: RLProxy rl) (Tuple v' x)
        handleThis = VF.on sym \f' -> VF.inj sym $ upF $
          toDF' (FProxy :: FProxy f) f' :<-: x
    downV _ = handleThis handleOther
      where
        sym = SProxy :: SProxy sym
        handleOther v' = VF.expand $ map (lmap VF.expand) <$>
          downV (RLProxy :: RLProxy rl) v'
        handleThis = VF.on sym \f -> VF.inj sym $
          (map (lmap (VF.inj sym) <<< fromZF) <$> downF f)
    aroundV _ (Tuple v x) = handleThis handleOther v
      where
        sym = SProxy :: SProxy sym
        handleOther v' = bimap
          (VF.expand >>> map (lmap VF.expand))
          (lmap VF.expand)
          $ aroundV (RLProxy :: RLProxy rl) (Tuple v' x)
        inj :: forall a. f' a -> VariantF r' a
        inj = VF.inj sym
        handleThis = VF.on sym \f' ->
          lmap (map (fromZF >>> lmap inj) >>> inj) $
          map (lmap inj <<< fromZF) $ fromZF $
          aroundF $ toDF' (FProxy :: FProxy f) f' :<-: x

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
  ZRec t -> f (Lazy (ZRec t))
downRec (context :<<~: focus) = downF (project focus) <#> map
  case _ of
    cx :<-: fc ->
      toParentCtx cx : context :<<~: fc

upRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t -> Either t (ZRec t)
upRec (Nil :<<~: focus) = Left focus
upRec (cx : context :<<~: focus) = Right $
  context :<<~: embed (upF (fromParentCtx cx :<-: focus))

tipRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  t -> ZRec t
tipRec = ZRec Nil

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
downIntoRec f z = maybe z force (f (downRec z))

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
  , function: methods."Pair"
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
  , function: methods."Pair"
  , app: methods."Pair"
  }

handleATypeVFConsts :: forall a r.
  { "Const" :: forall b. Const b a -> r
  , function :: Pair a -> r
  , app :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVFConsts methods = handleATypeVF
  { name: methods."Const"
  , var: methods."Const"
  , function: methods.function
  , app: methods.app
  }

handleATypeVF :: forall a r.
  { name :: Const (Qualified Proper) a -> r
  , var :: Const Ident a -> r
  , function :: Pair a -> r
  , app :: Pair a -> r } ->
  ATypeVF a -> r
handleATypeVF methods = VF.case_
  # VF.on _name methods.name
  # VF.on _var methods.var
  # VF.on _function methods.function
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
  # VF.on _function (methods."Pair" (VF.inj _function) (fromDF >>> VF.inj _function >>> toDF))
  # VF.on _app (methods."Pair" (VF.inj _app) (fromDF >>> VF.inj _app >>> toDF))

simpleShowZRec :: ZRec ATypeV -> String
simpleShowZRec (context :<<~: focus) = go context cx
  where
    show1 :: Algebra ATypeVF String
    show1 = VF.match
      { name: unwrap >>> show
      , var: unwrap >>> show
      , function: \(Pair l r) ->
          "(" <> l <> ") -> (" <> r <> ")"
      , app: \(Pair l r) ->
          "(" <> l <> ") (" <> r <> ")"
      }
    showAll = cata show1
    cx = showAll focus
    go Nil s = s
    go (h : r) s = go r $ VF.match
      { function: showBranch " -> " s
      , app: showBranch " " s
      , name: unwrap >>> absurd
      , var: unwrap >>> absurd
      } $ fromDF $ fromParentCtx h
    showBranch :: String -> String -> DPair ATypeV -> String
    showBranch sep s (DPairL' a) = "{" <> s <> "}" <> sep <> showAll a
    showBranch sep s (DPairR' a) = showAll a <> sep <> "{" <> s <> "}"
