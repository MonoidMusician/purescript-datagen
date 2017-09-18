module Reprinting where

import Prelude

import Annot (Annot(..), mayNeedAppParen, mayNeedFnParen)
import Control.Comonad (class Comonad)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.State (State, evalState, get, gets, modify, runState)
import Data.Bifunctor (lmap)
import Data.Bifunctor.Variant as VF2
import Data.Bitraversable (class Bitraversable, bitraverse)
import Data.Const (Const)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant as VF
import Data.Identity (Identity(..))
import Data.Map (toAscUnfoldable) as Map
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (unwrap)
import Data.Pair (Pair(..))
import Data.Spliceable (class Spliceable, length, splice)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy)
import Data.Tuple (Tuple(..), fst, swap)
import Data.Variant.Internal (FProxy)
import Matryoshka (class Recursive, Algebra)
import Printing (joinWithIfNE)
import Recursion (modifyHead, rewrap, whileAnnotatingDown)
import Types (ATypeV, ATypeVF, ATypeVR, DataType(..), DataTypeDecls, DataTypeDef(..), ModuleData, _app, _function, _name, _var, declKeyword, showImportModules)
import Zippers (DPair2(..), ZipperVC, dis, upDPair)

-- | A tag consists of the following:
-- |   1. the starting index *relative to the parent*
-- |   2. the length of the string that represents this chunk
type Tag = Tuple (Additive Int) (Additive Int)
-- | A tagged recursive structure of `Cofree` and `Tag`.
type Tagged f = Cofree f Tag
-- | Used before a Cofree is tagged.
type Untagged f = f (Tagged f)
-- | While building up a tag, accumulate a `String` of the current content,
-- | which also gives the index relative to the parent (see `Tag`).
type Tagging a = State String a

type ATypeVC = Tagged ATypeVF

newtype Reprinter f f' m ann = Reprinter
  { print :: ann -> Algebra f (Tuple m (Untagged f))
  }

tag ::
  forall m.
    Monoid m =>
  State m (Untagged ATypeVF) ->
  Tuple m (Untagged ATypeVF)
tag = swap <<< (runState <@> mempty)

recur ::
  forall m.
    Spliceable m =>
  Tuple m (Untagged ATypeVF) ->
  State m (Tagged ATypeVF)
recur (Tuple s r) = do
  offset <- gets length
  literal s
  pure $ Tuple offset (length s) :< r

literal :: forall m. Monoid m => m -> State m Unit
literal s = modify (_ <> s)

simple :: forall f m. Functor f =>
  f Void -> m -> Tuple m (Untagged f)
simple v s = Tuple s $ map absurd v

simpleShowConst ::
  forall a b sym bleh.
    IsSymbol sym =>
    RowCons sym (FProxy (Const a)) bleh ATypeVR =>
    Show a =>
  SProxy sym -> Const a b -> Tuple String (ATypeVF (Tagged ATypeVF))
simpleShowConst k v = simple (VF.inj k $ rewrap v) $ show $ unwrap v

showTagged1P :: Maybe Annot -> Algebra ATypeVF (Tuple String (Untagged ATypeVF))
showTagged1P p = VF.match
  { name: simpleShowConst _name
  , var: simpleShowConst _var
  , function: \(Pair l r) -> wrapTagIf mayNeedFnParen do
      a <- recur l
      literal " -> "
      b <- recur r
      pure (VF.inj _function (Pair a b))
  , app: \(Pair l r) -> wrapTagIf mayNeedAppParen do
      a <- recur l
      literal " "
      b <- recur r
      pure (VF.inj _app (Pair a b))
  --, row: \meh -> tag do
      --literal "meh"
      --pure (VF.inj (SProxy :: SProxy "row") meh)
  }
  where
    wrapTagIf pred v
      | pred p    = tag $ literal "(" *> v <* literal ")"
      | otherwise = tag v

annotPrec :: forall a. ATypeVF a -> ATypeVF (Tuple Annot a)
annotPrec = VF.match
  { name: VF.inj _name <<< rewrap
  , var: VF.inj _var <<< rewrap
  , function: VF.inj _function <<< bimapPair (Tuple FnParen) (Tuple None)
  , app: VF.inj _app <<< bimapPair (Tuple FnParen) (Tuple FnAppParen)
  } where bimapPair f g (Pair a b) = Pair (f a) (g b)

showTagged :: forall t. Recursive t ATypeVF =>
  t -> Tuple String (Untagged ATypeVF)
showTagged = whileAnnotatingDown Nothing annotPrec showTagged1P

showTagged' :: forall t. Recursive t ATypeVF =>
  Maybe Annot -> t -> Tuple String (Untagged ATypeVF)
showTagged' ann = whileAnnotatingDown ann annotPrec showTagged1P

showAType :: forall t. Recursive t ATypeVF =>
  t -> String
showAType = showTagged >>> fst

showAType' :: forall t. Recursive t ATypeVF =>
  Maybe Annot -> t -> String
showAType' ann = showTagged' ann >>> fst

evalFrom :: forall m. Spliceable m =>
  Additive Int -> Tuple m (Untagged ATypeVF) -> Tuple m ATypeVC
evalFrom st (Tuple s v) =
  Tuple s $ Tuple st (length s) :< v

showTaggedFrom :: forall t. Recursive t ATypeVF =>
  Additive Int -> Maybe Annot -> t -> Tuple String ATypeVC
showTaggedFrom i ann = showTagged' ann >>> evalFrom i

patch ::
  ZipperVC -> ATypeV -> String ->
  Tuple String ATypeVC
patch p replacement old = patchInner p mempty Nothing
  where
    patchInner positioned i =
      let Tuple offset size = head positioned
      in case tail positioned of
        Compose Nothing -> \ann ->
          let start = i <> offset in
          showTaggedFrom offset ann replacement # lmap
            (splice start size <@> old)
        Compose (Just inside) -> const
          let
            handle ::
              (Pair ~> ATypeVF) ->
              DPair2 ATypeVC ZipperVC ->
              Tuple String ATypeVC
            handle inj dpair =
              let
                Tuple new pair = upDPair id <$>
                  patching1 patcher old dpair
                caput = Tuple offset (size <> delta old new)
              in Tuple new $ caput :< inj pair
            patcher da =
              patchInner da (i <> offset) $ Just ann
            isLeft = case _ of
              DPairL _ _ -> true
              DPairR _ _ -> false
            getAnn l r = case _ of
              DPairL _ _ -> l
              DPairR _ _ -> r
            ann = VF2.match
              { function:
                  isLeft >>> if _ then FnParen else None
              , app:
                  isLeft >>> if _ then FnParen else FnAppParen
              } $ inside
          in inside # VF2.match
            { function: handle (VF.inj _function)
            , app: handle (VF.inj _app)
            }

delta :: forall m. Spliceable m =>
  m -> m -> Additive Int
delta old new = Additive $ ((-) `on` (length >>> unwrap)) new old

patching1 ::
  forall r f df a da.
    Bitraversable df =>
    Comonad (df (Cofree f Tag)) =>
    Spliceable r =>
  (da -> Tuple r a) -> r -> df (Cofree f Tag) da ->
  Tuple r (df (Cofree f Tag) a)
patching1 f old = disI <<< run <<< bitraverse term hole
  where
    term t = get <#> \diff ->
      modifyHead (_ <> Tuple diff mempty) t
    hole h = do
      let
        Tuple new n = f h
        diff = delta old new
      modify (_ <> diff)
      pure (Tuple new n)
    disI = unwrap <<< dis <<< Identity
    run = evalState <@> mempty

showDataType :: DataType -> String
showDataType (TypeAlias t) = showAType t
showDataType (SumType m) = joinWith " | " $
  Map.toAscUnfoldable m <#> \(Tuple c ts) ->
    show c <> joinWithIfNE " " (showAType' (Just FnAppParen)) ts

showDataTypeDecls :: DataTypeDecls -> String
showDataTypeDecls = joinWith "\n" <<< Map.toAscUnfoldable >>> map
  \(Tuple name (DataTypeDef vs dt)) ->
    let vars = joinWithIfNE " " show vs in
    show (declKeyword dt) <> " " <> show name <> vars <> " = " <> showDataType dt

showModuleData :: ModuleData -> String
showModuleData = do
  imports <- showImportModules <<< _.imports
  datatypes <- showDataTypeDecls <<< _.datatypes
  pure (imports <> "\n\n" <> datatypes)
