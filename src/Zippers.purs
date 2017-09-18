module Zippers where

import Prelude

import Control.Apply (lift2)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, head, mkCofree, tail, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Extend (class Extend)
import Data.Bifoldable (class Bifoldable, bifoldlDefault, bifoldrDefault)
import Data.Bifunctor (class Bifunctor, bimap, lmap, rmap)
import Data.Bifunctor.Variant (F2Proxy, VariantF2)
import Data.Bifunctor.Variant as VF2
import Data.Bitraversable (class Bitraversable, bisequenceDefault)
import Data.Const (Const(..))
import Data.Either (Either(..), either)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Variant (VariantF)
import Data.Functor.Variant as VF
import Data.Lazy (Lazy, defer, force)
import Data.Lens (Lens', lens)
import Data.List (List(Nil), (:))
import Data.Maybe (Maybe(..), maybe)
import Data.Monoid.Additive (Additive)
import Data.Newtype (unwrap)
import Data.Pair (Pair(..))
import Data.Pair as Pair
import Data.Symbol (class IsSymbol, SProxy(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Variant.Internal (FProxy(..), RLProxy(..))
import Matryoshka (class Corecursive, class Recursive, Algebra, cata, embed, project)
import Recursion (forget, rewrap)
import Type.Row (class ListToRow, class RowToList, Cons, Nil, kind RowList)
import Types (ATypeV, ATypeVF, ATypeVR, Ident, Proper, Qualified, _app, _function, _name, _var)
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
data DPair2 a da = DPairL da a | DPairR a da
derive instance eqDPair :: (Eq a, Eq da) => Eq (DPair2 a da)
derive instance ordDPair :: (Ord a, Ord da) => Ord (DPair2 a da)
derive instance functorDPair2 :: Functor (DPair2 a)
instance bifunctorDPair :: Bifunctor DPair2 where
  bimap f g = case _ of
    DPairL da a -> DPairL (g da) (f a)
    DPairR a da -> DPairR (f a) (g da)
instance bifoldableDPair :: Bifoldable DPair2 where
  bifoldMap f g = case _ of
    DPairL da a -> g da <> f a
    DPairR a da -> f a <> g da
  bifoldr f g = bifoldrDefault f g
  bifoldl f g = bifoldlDefault f g
instance bitraversableDPair :: Bitraversable DPair2 where
  bitraverse f g = case _ of
    DPairL da a -> DPairL <$> g da <*> f a
    DPairR a da -> DPairR <$> f a <*> g da
  bisequence = bisequenceDefault
instance showDPair :: (Show a, Show da) => Show (DPair2 a da) where
  show (DPairL da a) = "(DPairL " <> show da <> " " <> show a <> ")"
  show (DPairR a da) = "(DPairR " <> show a <> " " <> show da <> ")"
instance extendDPair :: Extend (DPair2 a) where
  extend f p@(DPairL da a) = DPairL (f p) a
  extend f p@(DPairR a da) = DPairR a (f p)
instance comonadDPair :: Comonad (DPair2 a) where
  extract (DPairL da _) = da
  extract (DPairR _ da) = da
instance derivativeofPair_isDPair :: Diff1 Pair DPair where
  downF (Pair l r) = Pair
    (defer \_ -> toZF $ Tuple (DPairL' r) l)
    (defer \_ -> toZF $ Tuple (DPairR' l) r)
  upF z = case fromZF z of
    Tuple (DPairL' l) r -> Pair l r
    Tuple (DPairR' r) l -> Pair l r
  aroundF z = case fromZF z of
    Tuple (DPairL' l) r -> toZF $ flip Tuple z $
      DPairL' z
    Tuple (DPairR' r) l -> toZF $ flip Tuple z $
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

data ZRec t f = ZRec (List (DF f t)) (f t)
infix 1 ZRec as :<<~:

downRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t f -> f (Lazy (ZRec t f))
downRec (context :<<~: focus) = downF focus <#> map
  case _ of
    cx :<-: fc ->
      cx : context :<<~: project fc

upRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t f -> Either t (ZRec t f)
upRec (Nil :<<~: focus) = Left (embed focus)
upRec (cx : context :<<~: focus) = Right $
  context :<<~: (upF (cx :<-: embed focus))

tipRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  t -> ZRec t f
tipRec = ZRec Nil <<< project

topRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  ZRec t f -> t
topRec z = upRec z # either id topRec

downIntoRec ::
  forall t f f'.
    Recursive t f => Corecursive t f =>
    Functor f => Diff1 f f' =>
  (f ~> Maybe) -> ZRec t f -> ZRec t f
downIntoRec f z = maybe z force (f (downRec z))

_contextRec :: forall t f. Lens' (ZRec t f) (List (DF f t))
_contextRec = lens (\(c :<<~: _) -> c)
  \(_ :<<~: f) c -> c :<<~: f

_focusRec :: forall t f. Lens' (ZRec t f) (f t)
_focusRec = lens (\(_ :<<~: f) -> f)
  \(c :<<~: _) f -> c :<<~: f

type ZipperVR =
  ( function :: F2Proxy DPair2
  , app :: F2Proxy DPair2
  )
type ZipperVF = VariantF2 ZipperVR
type ZipperVF' a = Compose Maybe (ZipperVF a)
type ZipperV = Mu (ZipperVF' ATypeV)
type ZipperVC = Cofree (ZipperVF' ATypeVC) Tag
type ZipperVRec = ZRec ATypeVC ATypeVF

downZipperVF :: forall a da. (a -> da) -> ATypeVF a -> ATypeVF (ZipperVF a da)
downZipperVF down = VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair down >>> rePair' _function)
  # VF.on _app (downDPair down >>> rePair' _app)

rePair' ::
  forall a da sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (F2Proxy DPair2) meh ZipperVR =>
  SProxy sym -> Pair (DPair2 a da) -> ATypeVF (ZipperVF a da)
rePair' sym = VF.inj sym <<< map (VF2.inj sym)

{-
downZipperVF' :: forall a da. (a -> da) -> ATypeVF a -> ZipperVF' a da
downZipperVF' down = VF.default (Compose Nothing)
    # VF.on _function (downDPair down >>> map (VF.inj _function) >>> Just >>> Compose)
    # VF.on _app (downDPair down >>> map (VF.inj _app) >>> Just >>> Compose)
-}

{-
     ATypeV
down (a -> b) =
              ATypeVF ()
              ->
  (a, _ -> b)    (b, a -> _)
  Tuple ATypeV ZipperV

_ -> b == inj "function" $ DPairL Unit (b :: ATypeV)
(a, _ -> b) == inj "function" $ DPairL (a :: ATypeV) (b :: ATypeV)
-}

downZipper1 :: ATypeV -> ATypeVF (ZipperVF ATypeV ATypeV)
downZipper1 v =
  ( VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair id >>> rePair' _function)
  # VF.on _app (downDPair id >>> rePair' _app)
  ) (unroll v)

extract1 ::
  (Pair ATypeV -> Tuple (DPair2 ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple (Maybe (ZipperVF ATypeV Unit)) ATypeV
extract1 choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF2.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF2.inj _app) <<< choose)
  ) (unroll this)

extract1' ::
  (Pair ATypeV -> Tuple (DPair2 ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple ZipperV ATypeV
extract1' choose = extract1 choose >>> lmap unroll1

extract1C ::
  (Pair ATypeVC -> Tuple (DPair2 ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple (Maybe (ZipperVF ATypeVC Tag)) ATypeVC
extract1C choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF2.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF2.inj _app) <<< choose)
  ) (tail this)

extract1C' ::
  (Pair ATypeVC -> Tuple (DPair2 ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple ZipperVC ATypeVC
extract1C' choose v =
  extract1C choose v # lmap (unroll1C (head v))

left :: forall a. Pair a -> Tuple (DPair2 a Unit) a
left (Pair l r) = Tuple (DPairL unit r) l

right :: forall a. Pair a -> Tuple (DPair2 a Unit) a
right (Pair l r) = Tuple (DPairR l unit) r

leftC :: Pair ATypeVC -> Tuple (DPair2 ATypeVC Tag) ATypeVC
leftC (Pair l r) = Tuple (DPairL (head l) r) l

rightC :: Pair ATypeVC -> Tuple (DPair2 ATypeVC Tag) ATypeVC
rightC (Pair l r) = Tuple (DPairR l (head r)) r

unroll1 :: Maybe (ZipperVF ATypeV Unit) -> ZipperV
unroll1 = roll <<< Compose <<< map (rmap (const (roll (Compose Nothing))))

unroll1C :: Tag -> Maybe (ZipperVF ATypeVC Tag) -> ZipperVC
unroll1C h v = h :< Compose (rmap (mkCofree <@> Compose Nothing) <$> v)

downDPair :: forall a da. (a -> da) -> Pair a -> Pair (DPair2 a da)
downDPair down (Pair l r) = Pair
  (DPairL (down l) r)
  (DPairR l (down r))

upDPair :: forall da a. (da -> a) -> DPair2 a da -> Pair a
upDPair up = case _ of
  DPairL da a -> Pair (up da) a
  DPairR a da -> Pair a (up da)

dis :: forall f d w a. Functor f => Comonad w => f (w (Tuple d a)) -> f (Tuple d (w a))
dis = map (lift2 Tuple (fst <<< extract) (map snd))

downZipperC :: Tuple ATypeVC ZipperVC -> Tuple Tag (ATypeVF (Tuple ATypeVC ZipperVC))
downZipperC (Tuple a da) = Tuple (head a) $
  ( VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (mkZipperC _function (head a))
  # VF.on _app (mkZipperC _app (head a))
  ) (tail a)

emptyZipperC :: forall f a. a -> Cofree (Compose Maybe f) a
emptyZipperC = mkCofree <@> Compose Nothing

emptyZipper :: forall f. Mu (Compose Maybe f)
emptyZipper = roll $ Compose Nothing

zLeftC :: Tuple Tag (ATypeVF (Tuple ATypeVC ZipperVC)) -> Tuple ATypeVC ZipperVC
zLeftC (Tuple tag f) =
  ( VF.case_
  # handleConst _name
  # handleConst _var
  # VF.on _function Pair.fst
  # VF.on _app Pair.fst
  ) f
  where
    handleConst ::
      forall sym a bleh r' r.
        IsSymbol sym =>
        RowCons sym (FProxy (Const a)) bleh ATypeVR =>
        RowCons sym (FProxy (Const a)) r' r =>
      SProxy sym ->
      (VariantF r' (Tuple ATypeVC ZipperVC) -> Tuple ATypeVC ZipperVC) ->
      VariantF r (Tuple ATypeVC ZipperVC) ->
      Tuple ATypeVC ZipperVC
    handleConst sym = VF.on sym (reconstitute <<< VF.inj sym <<< rewrap)
    reconstitute = withEmptyZipper <<< mkCofree tag
    withEmptyZipper = Tuple <@> emptyZipperC tag

zLeft :: ATypeVF (Tuple ATypeV ZipperV) -> Tuple ATypeV ZipperV
zLeft = VF.case_
  # handleConst _name
  # handleConst _var
  # VF.on _function Pair.fst
  # VF.on _app Pair.fst
  where
    handleConst ::
      forall sym a bleh r' r.
        IsSymbol sym =>
        RowCons sym (FProxy (Const a)) bleh ATypeVR =>
        RowCons sym (FProxy (Const a)) r' r =>
      SProxy sym ->
      (VariantF r' (Tuple ATypeV ZipperV) -> Tuple ATypeV ZipperV) ->
      VariantF r (Tuple ATypeV ZipperV) ->
      Tuple ATypeV ZipperV
    handleConst sym = VF.on sym (reconstitute <<< VF.inj sym <<< rewrap)
    reconstitute = withEmptyZipper <<< roll
    withEmptyZipper = Tuple <@> emptyZipper

downZipper :: Tuple ATypeV ZipperV -> ATypeVF (Tuple ATypeV ZipperV)
downZipper (Tuple a da) =
  ( VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (mkZipper _function)
  # VF.on _app (mkZipper _app)
  ) (unroll a)

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

{-
meh :: forall a r.
  { "Const" ::
      forall sym b bleh.
        IsSymbol sym =>
        RowCons sym (FProxy (Const b)) bleh ATypeVR =>
      SProxy sym -> Const b a -> r
  , "Pair" ::
      forall a' sym bleh meh.
        IsSymbol sym =>
        RowCons sym (FProxy Pair) bleh ATypeVR =>
        RowCons sym (FProxy (DPair a')) meh (ZipperVR a') =>
      SProxy sym -> Pair a -> r
  } -> ATypeVF a -> r
meh methods = VF.case_
  # VF.on _name (onName _name)
  # VF.on _var (methods."Const" _var)
  # VF.on _function (methods."Pair" _function)
  # VF.on _app (methods."Pair" _app)
  where
    onName :: forall b. SProxy "name" -> Const b a -> r
    onName = methods."Const"
-}

addLayerC :: Tag -> ZipperVF ATypeVC ZipperVC -> ZipperVC
addLayerC tag = mkCofree tag <<< Compose <<< Just

addLayer :: ZipperVF ATypeV ZipperV -> ZipperV
addLayer = roll <<< Compose <<< Just

digC :: forall a f g. Cofree f a -> Tuple (Cofree f a) (Cofree (Compose Maybe g) a)
digC v = Tuple v (head v :< Compose Nothing)

dig :: forall f g. Mu f -> Tuple (Mu f) (Mu (Compose Maybe g))
dig = Tuple <@> roll (Compose Nothing)

mkZipperC ::
  forall sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (F2Proxy DPair2) meh ZipperVR =>
  SProxy sym ->
  Tag ->
  Pair ATypeVC ->
  ATypeVF (Tuple ATypeVC ZipperVC)
mkZipperC sym tag p = VF.inj sym $
  dis (downDPair digC p) <#> map
    (VF2.inj sym >>> addLayerC tag)

mkZipper ::
  forall sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (F2Proxy DPair2) meh ZipperVR =>
  SProxy sym ->
  Pair ATypeV ->
  ATypeVF (Tuple ATypeV ZipperV)
mkZipper sym p = VF.inj sym $
  dis (downDPair dig p) <#> map
    (VF2.inj sym >>> addLayer)

simpleShowZ :: forall a. (a -> String) -> Algebra (ZipperVF a) String
simpleShowZ inner = VF2.match
  { function: showBranch " -> "
  , app: showBranch " "
  --, row: const "()"
  }
  where
    showBranch :: String -> DPair2 a String -> String
    showBranch s (DPairL da a) = "{" <> da <> "}" <> s <> inner a
    showBranch s (DPairR a da) = inner a <> s <> "{" <> da <> "}"

simpleShowZ1 :: forall a s. Show s => (a -> String) -> ZipperVF a s -> String
simpleShowZ1 inner v = simpleShowZ inner (rmap show v)

simpleShowZRec :: ZipperVRec -> String
simpleShowZRec (context :<<~: focus) = go context cx
  where
    meh :: Algebra ATypeVF String
    meh = VF.match
      { name: unwrap >>> show
      , var: unwrap >>> show
      , function: \(Pair l r) ->
          "(" <> l <> ") -> (" <> r <> ")"
      , app: \(Pair l r) ->
          "(" <> l <> ") (" <> r <> ")"
      }
    meh2 = forget >>> cata meh
    meh3 = map forget >>> embed >>> cata meh
    cx = meh3 focus
    go Nil s = s
    go (h : r) s = go r $ VF.match
      { function: showBranch " -> " s
      , app: showBranch " " s
      , name: unwrap >>> absurd
      , var: unwrap >>> absurd
      } $ fromDF h
    showBranch :: String -> String -> DPair ATypeVC -> String
    showBranch sep s (DPairL' a) = "{" <> meh2 a <> "}" <> sep <> s
    showBranch sep s (DPairR' a) = s <> sep <> "{" <> meh2 a <> "}"
