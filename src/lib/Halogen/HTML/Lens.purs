module Halogen.HTML.Lens (Query(UpdateState), eval) where

import Prelude

import Control.Monad.Aff (Aff)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Class (class MonadEff)
import Control.Monad.State (class MonadState)
import DOM (DOM)
import Halogen as H

data Query s a = UpdateState (forall eff. Eff (dom :: DOM | eff) (s -> s)) a

--eval :: forall s eff. Query s ~> H.ComponentDSL s (Query s) Void (Aff (dom :: DOM | eff))
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
