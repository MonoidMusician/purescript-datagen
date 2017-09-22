module Reprinting where

import Prelude

import Annot (Annot(..), mayNeedAppParen, mayNeedFnParen)
import Control.Comonad.Cofree (Cofree, head, (:<))
import Control.Comonad.Env (EnvT(..))
import Control.Monad.State (State, gets, modify, runState)
import Data.Bifunctor (lmap, rmap)
import Data.Const (Const)
import Data.Function (on)
import Data.Functor.Variant as VF
import Data.List.Lazy as List
import Data.Map (toAscUnfoldable) as Map
import Data.Maybe (Maybe(..))
import Data.Monoid (class Monoid, mempty)
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (un, unwrap)
import Data.Pair (Pair(..))
import Data.Spliceable (class Spliceable, length, splice)
import Data.String (joinWith)
import Data.Symbol (class IsSymbol, SProxy)
import Data.Traversable (mapAccumL)
import Data.Tuple (Tuple(..), fst, snd, swap)
import Data.Variant.Internal (FProxy)
import Matryoshka (class Recursive, Algebra)
import Printing (joinWithIfNE)
import Recursion (Alg, modifyHead, rewrap, whileAnnotatingDown)
import Types (ATypeV, ATypeVF, ATypeVR, DataType(..), DataTypeDecls, DataTypeDef(..), ModuleData, _app, _function, _name, _var, declKeyword, showImportModules)
import Zippers (class Diff1, DF, ParentCtxs, ZRec, fromDF, fromParentCtx, toDF, toParentCtx, (:<<~:))

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
  Tuple String (ZRec ATypeVC) -> ATypeV ->
  Tuple String (ZRec ATypeVC)
patch (Tuple old (p :<<~: plug)) replacement = Tuple new (p' :<<~: focus)
  where
    pos = head plug
    extractParentCtx :: forall a f'. Diff1 ATypeVF f' =>
      DF (Alg ATypeVC) a -> Tuple Tag (f' a)
    extractParentCtx = un EnvT <<< fromDF <<< fromParentCtx
    extractParentTag :: forall a. DF (Alg ATypeVC) a -> Tag
    extractParentTag = fst <<< extractParentCtx
    extractParent :: forall a f'. Diff1 ATypeVF f' =>
      DF (Alg ATypeVC) a -> f' a
    extractParent = snd <<< extractParentCtx
    isLeft = not fst
    getAnnFromParent :: forall a. DF (Alg ATypeVC) a -> Annot
    getAnnFromParent = VF.match
      { function:
          isLeft >>> if _ then FnParen else None
      , app:
          isLeft >>> if _ then FnParen else FnAppParen
      , name: absurd <<< unwrap
      , var: absurd <<< unwrap
      } <<< extractParent
    ann = getAnnFromParent <$> List.head p
    Tuple shown focus = showTaggedFrom (fst pos) ann replacement
    d = (delta `on` snd) pos (head focus)
    adj = append d -- technically this would prepend, but Abelian so it works out
    adjIdx = lmap adj
    adjLen = rmap adj
    updateOtherChildTag priorIdxOfUpdated t =
      if fst t > priorIdxOfUpdated
        then adjIdx t
        else t
    adjustAll :: Additive Int -> ParentCtxs ATypeVC -> ParentCtxs ATypeVC
    adjustAll c1 cfs = (mapAccumL go c1 cfs).value
      where
        go childIdx cf = case extractParentCtx cf of
          Tuple t@(Tuple idx _) cx ->
            let
              children = modifyHead (updateOtherChildTag childIdx) <$> cx
              adjusted = EnvT $ Tuple (adjLen t) children
            in { accum: idx, value: toParentCtx (toDF adjusted) }
    p' = adjustAll (fst pos) p
    realPos = fst pos <> List.foldMap
      (fst <<< extractParentTag) p
    new = splice realPos (snd pos) shown old

delta :: Additive Int -> Additive Int -> Additive Int
delta old new = Additive $ ((-) `on` unwrap) new old

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
