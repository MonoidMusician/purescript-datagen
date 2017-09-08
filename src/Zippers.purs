module Zippers where

import Prelude

import Control.Apply (lift2)
import Control.Comonad (class Comonad, extract)
import Control.Comonad.Cofree (Cofree, head, mkCofree, tail, (:<))
import Control.Extend (class Extend)
import Data.Bifunctor (lmap)
import Data.Const (Const)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Mu (Mu, roll, unroll)
import Data.Functor.Variant (SProxy, VariantF)
import Data.Functor.Variant as VF
import Data.Maybe (Maybe(..))
import Data.Monoid.Additive (Additive)
import Data.Pair (Pair(..))
import Data.Pair as Pair
import Data.StrMap (StrMap)
import Data.Symbol (class IsSymbol)
import Data.Tuple (Tuple(..), fst, snd)
import Data.Variant.Internal (FProxy)
import Matryoshka (Algebra)
import Recursion (rewrap)
import Types (ATypeV, ATypeVF, ATypeVR, _app, _function, _name, _var)

type Tag = Tuple (Additive Int) (Additive Int)
type ATypeVC = Cofree ATypeVF Tag

data DPair' a da = DPairL' da a | DPairR' a da
derive instance functorDPair' :: Functor (DPair' a)
instance showDPair' :: (Show a, Show da) => Show (DPair' a da) where
  show (DPairL' da a) = "(DPairL' " <> show da <> " " <> show a <> ")"
  show (DPairR' a da) = "(DPairR' " <> show a <> " " <> show da <> ")"
instance extendDPair' :: Extend (DPair' a) where
  extend f p@(DPairL' da a) = DPairL' (f p) a
  extend f p@(DPairR' a da) = DPairR' a (f p)
instance comonadDPair' :: Comonad (DPair' a) where
  extract (DPairL' da _) = da
  extract (DPairR' _ da) = da
data DStrMap' a da = DStrMap' String da (StrMap a)
type DATypeVR' a da =
  ( name     :: Unit
  , var      :: Unit
  , function :: DPair' a da
  , app      :: DPair' a da
  -- , row      :: Tuple (DStrMap' a da) da
  )
data DMu' f df = DIn' (df (Mu f) (DMu' f df)) (DMu' f df)

type ZipperVR a =
  ( function :: FProxy (DPair' a)
  , app :: FProxy (DPair' a)
  )
type ZipperVF a = VariantF (ZipperVR a)
type ZipperVF' a = Compose Maybe (ZipperVF a)
type ZipperVF'' a = Compose Maybe (Compose (Tuple Tag) (ZipperVF a))
type ZipperV = Mu (ZipperVF' ATypeV)
type ZipperVC = Cofree (ZipperVF' ATypeVC) Tag


downZipperVF :: forall a da. (a -> da) -> ATypeVF a -> ATypeVF (ZipperVF a da)
downZipperVF down = VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair' down >>> rePair' _function)
  # VF.on _app (downDPair' down >>> rePair' _app)

rePair' ::
  forall a da sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (FProxy (DPair' a)) meh (ZipperVR a) =>
  SProxy sym -> Pair (DPair' a da) -> ATypeVF (ZipperVF a da)
rePair' sym = VF.inj sym <<< map (VF.inj sym)

{-
downZipperVF' :: forall a da. (a -> da) -> ATypeVF a -> ZipperVF' a da
downZipperVF' down = VF.default (Compose Nothing)
    # VF.on _function (downDPair' down >>> map (VF.inj _function) >>> Just >>> Compose)
    # VF.on _app (downDPair' down >>> map (VF.inj _app) >>> Just >>> Compose)
-}

{-
     ATypeV
down (a -> b) =
              ATypeVF ()
              ->
  (a, _ -> b)    (b, a -> _)
  Tuple ATypeV ZipperV

_ -> b == inj "function" $ DPairL' Unit (b :: ATypeV)
(a, _ -> b) == inj "function" $ DPairL' (a :: ATypeV) (b :: ATypeV)
-}

downZipper1 :: ATypeV -> ATypeVF (ZipperVF ATypeV ATypeV)
downZipper1 v =
  ( VF.case_
  # VF.on _name (VF.inj _name <<< rewrap)
  # VF.on _var (VF.inj _var <<< rewrap)
  # VF.on _function (downDPair' id >>> rePair' _function)
  # VF.on _app (downDPair' id >>> rePair' _app)
  ) (unroll v)

extract1 ::
  (Pair ATypeV -> Tuple (DPair' ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple (Maybe (ZipperVF ATypeV Unit)) ATypeV
extract1 choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF.inj _app) <<< choose)
  ) (unroll this)

extract1' ::
  (Pair ATypeV -> Tuple (DPair' ATypeV Unit) ATypeV) ->
  ATypeV -> Tuple ZipperV ATypeV
extract1' choose = extract1 choose >>> lmap unroll1

extract1C ::
  (Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple (Maybe (ZipperVF ATypeVC Tag)) ATypeVC
extract1C choose this =
  ( VF.default (Tuple Nothing this)
  # VF.on _function (lmap (Just <<< VF.inj _function) <<< choose)
  # VF.on _app (lmap (Just <<< VF.inj _app) <<< choose)
  ) (tail this)

extract1C' ::
  (Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC) ->
  ATypeVC -> Tuple ZipperVC ATypeVC
extract1C' choose v =
  extract1C choose v # lmap (unroll1C (head v))

left :: forall a. Pair a -> Tuple (DPair' a Unit) a
left (Pair l r) = Tuple (DPairL' unit r) l

right :: forall a. Pair a -> Tuple (DPair' a Unit) a
right (Pair l r) = Tuple (DPairR' l unit) r

leftC :: Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC
leftC (Pair l r) = Tuple (DPairL' (head l) r) l

rightC :: Pair ATypeVC -> Tuple (DPair' ATypeVC Tag) ATypeVC
rightC (Pair l r) = Tuple (DPairR' l (head r)) r

unroll1 :: Maybe (ZipperVF ATypeV Unit) -> ZipperV
unroll1 = roll <<< Compose <<< map (_ $> roll (Compose Nothing))

unroll1C :: Tag -> Maybe (ZipperVF ATypeVC Tag) -> ZipperVC
unroll1C h v = h :< Compose (map (mkCofree <@> Compose Nothing) <$> v)

downDPair' :: forall a da. (a -> da) -> Pair a -> Pair (DPair' a da)
downDPair' down (Pair l r) = Pair
  (DPairL' (down l) r)
  (DPairR' l (down r))

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

addLayerC :: Tag -> ZipperVF ATypeVC ZipperVC -> ZipperVC
addLayerC tag = mkCofree tag <<< Compose <<< Just

addLayer :: ZipperVF ATypeV ZipperV -> ZipperV
addLayer = roll <<< Compose <<< Just

digC :: forall a f g. Cofree f a -> Tuple (Cofree f a) (Cofree (Compose Maybe g) a)
digC v = Tuple v (head v :< Compose Nothing)

dig :: forall f g. Mu f -> Tuple (Mu f) (Mu (Compose Maybe g))
dig = Tuple <@> roll (Compose Nothing)

mkZipperC ::
  forall a da sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (FProxy (DPair' ATypeVC)) meh (ZipperVR ATypeVC) =>
  SProxy sym ->
  Tag ->
  Pair ATypeVC ->
  ATypeVF (Tuple ATypeVC ZipperVC)
mkZipperC sym tag p = VF.inj sym $
  dis (downDPair' digC p) <#> map
    (VF.inj sym >>> addLayerC tag)

mkZipper ::
  forall a da sym bleh meh.
    IsSymbol sym =>
    RowCons sym (FProxy Pair) bleh ATypeVR =>
    RowCons sym (FProxy (DPair' ATypeV)) meh (ZipperVR ATypeV) =>
  SProxy sym ->
  Pair ATypeV ->
  ATypeVF (Tuple ATypeV ZipperV)
mkZipper sym p = VF.inj sym $
  dis (downDPair' dig p) <#> map
    (VF.inj sym >>> addLayer)

simpleShowZ :: forall a. (a -> String) -> Algebra (ZipperVF a) String
simpleShowZ inner = VF.match
  { function: showBranch " -> "
  , app: showBranch " "
  --, row: const "()"
  }
  where
    showBranch :: String -> DPair' a String -> String
    showBranch s (DPairL' da a) = "{" <> da <> "}" <> s <> inner a
    showBranch s (DPairR' a da) = inner a <> s <> "{" <> da <> "}"

simpleShowZ1 :: forall a s. Show s => (a -> String) -> ZipperVF a s -> String
simpleShowZ1 inner v = simpleShowZ inner (v <#> show)
