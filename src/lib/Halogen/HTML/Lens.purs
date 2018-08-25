module Halogen.HTML.Lens (Query(UpdateState), eval) where

import Prelude

import Effect (Effect)
import Effect.Class (class MonadEffect)
import Control.Monad.State (class MonadState)

import Data.Array (fromFoldable, mapWithIndex)
import Data.Lens (Lens', Prism', Setter', Traversal', element, preview, toListOf, view)
import Data.Maybe (Maybe, fromMaybe)
import Data.Tuple (Tuple)
import Halogen as H
import Halogen.HTML as HH

data Query s a = UpdateState (Effect (s -> s)) a

eval ::
  forall m s.
    Bind m =>
    MonadEffect m =>
    MonadState s m =>
  Query s ~> m
eval (UpdateState run next) = do
    reset <- H.liftEffect run
    H.modify_ reset
    pure next

type Pure s = Tuple (s -> s)
type El s = HH.HTML Void (Pure s Unit)
type Component s v = Setter' s v -> v -> El s

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

traversal :: forall s v. Component s v -> Traversal' s v -> s -> Array (El s)
traversal c l s = toListOf l s # fromFoldable # mapWithIndex \i -> c (element i l)
