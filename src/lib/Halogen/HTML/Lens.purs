module Halogen.HTML.Lens (Query(UpdateState), eval) where

import Prelude
import Halogen as H
import Control.Monad.Aff (Aff)
import Control.Monad.Eff (Eff)
import DOM (DOM)

data Query s a = UpdateState (forall eff. Eff (dom :: DOM | eff) (s -> s)) a

eval :: forall s eff. Query s ~> H.ComponentDSL s (Query s) Void (Aff (dom :: DOM | eff))
eval (UpdateState run next) = do
    reset <- H.liftEff run
    H.modify reset
    pure next
