module Reprinting where

import Prelude

import Annot (Annot(..), mayNeedAppParen, mayNeedFnParen)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Control.Monad.State (State, gets, modify, runState)
import Data.Bifunctor (lmap)
import Data.Bifunctor.Variant as VF2
import Data.Const (Const)
import Data.Function (on)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Variant as VF
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
import Zippers (DPair(..), ZipperVC)

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
  (Additive Int -> Maybe Annot -> Tuple String ATypeVC)
patch positioned replacement old i =
  let
    Tuple offset size = head positioned
  in case tail positioned of
    Compose Nothing -> \ann ->
      let start = i <> offset in
      showTaggedFrom offset ann replacement # lmap
        (splice start size <@> old)
    Compose (Just inside) -> const
      let
        next da ann f =
          let
            Tuple new updated = patch da replacement old (i <> offset) $ Just ann
            diff = Additive $ ((-) `on` (length >>> unwrap)) new old
          in Tuple new (Tuple offset (size <> diff) :< f diff updated)
        handle ::
          forall sym bleh.
            IsSymbol sym =>
            RowCons sym (FProxy Pair) bleh ATypeVR =>
          SProxy sym -> Annot -> Annot ->
          DPair ATypeVC ZipperVC -> Tuple String ATypeVC
        handle k ann _ (DPairL da a) =
          next da ann
            \diff updated ->
              VF.inj k (Pair updated $ modifyHead (_ <> Tuple diff mempty) a)
        handle k _ ann (DPairR a da) =
          next da ann
            \_ updated ->
              VF.inj k (Pair a updated)
      in inside # VF2.match
        { function: handle _function FnParen None
        , app: handle _app FnParen FnAppParen
        }

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
