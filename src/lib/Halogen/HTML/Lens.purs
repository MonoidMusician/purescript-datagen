module Halogen.HTML.Lens (Query(UpdateState), eval) where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff)
import Control.Monad.State (class MonadState)
import DOM (DOM)
import Data.Array (fromFoldable, mapWithIndex)
import Data.Lens (Lens', Prism', Setter', Traversal', element, preview, toListOf, view)
import Data.Maybe (Maybe, fromMaybe)
import Data.Tuple (Tuple)
import Halogen as H
import Halogen.HTML as HH

data Query s a = UpdateState (forall eff. Eff (dom :: DOM | eff) (s -> s)) a

eval ::
  forall m eff s.
    Bind m =>
    MonadEff ( dom :: DOM | eff ) m =>
    MonadState s m =>
  Query s ~> m
eval (UpdateState run next) = do
    reset <- H.liftEff run
    H.modify reset
    pure next

type Pure s = Tuple (s -> s)
type El s = H.HTML Void (Pure s)
type Component s v = Setter' s v -> v -> H.HTML Void (Pure s)

lensed :: forall s v. Component s v -> Lens' s v -> s -> El s
lensed c l s = view l s # c l

prismicDiv :: forall s v. Component s v -> Prism' s v -> s -> El s
prismicDiv c l s = fromMaybe (HH.div_ []) $ prismic c l s

prismicText :: forall s v. Component s v -> Prism' s v -> s -> El s
prismicText c l s = fromMaybe (HH.text "") $ prismic c l s

prismic :: forall s v. Component s v -> Prism' s v -> s -> Maybe (El s)
prismic c l s = preview l s <#> c l

traversalDiv :: forall s v. Component s v -> Traversal' s v -> s -> El s
traversalDiv c l s = HH.div_ $ traversal c l s

traversalSpan :: forall s v. Component s v -> Traversal' s v -> s -> El s
traversalSpan c l s = HH.span_ $ traversal c l s

traversal :: forall i s v. Component s v -> Traversal' s v -> s -> Array (El s)
traversal c l s = toListOf l s # fromFoldable # mapWithIndex \i -> c (element i l)
