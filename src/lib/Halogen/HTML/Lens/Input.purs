module Halogen.HTML.Lens.Input
    ( setter, query, attr,
    render, renderAsField
    ) where

import Prelude
import Halogen.HTML.Lens (Query(..))
import DOM.Event.Event as Event
import DOM.HTML.HTMLInputElement as HInput
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Control.Monad.Eff (Eff)
import Control.Monad.Except (runExcept)
import DOM (DOM)
import DOM.Event.Types (Event)
import DOM.HTML.Types (readHTMLInputElement)
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')

type Property s p = H.IProp p (Query s)
type Element s p = H.HTML p (Query s)

setter :: forall s eff. Lens' s String -> Event -> Eff (dom :: DOM | eff) (s -> s)
setter lens e =
    case runExcept $ readHTMLInputElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
            value <- H.liftEff $ HInput.value node
            pure (lens .~ value)

query :: forall s a. Lens' s String -> Event -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. Lens' s String -> Property s (onInput :: Event | p)
attr lens = HE.onInput (HE.input (query lens))

render :: forall s p. Lens' s String -> s -> Element s p
render lens state = HH.input
    [ attr lens
    , HP.value (state ^. lens)
    ]

renderAsField :: forall s p. String -> Lens' s String -> s -> Element s p
renderAsField label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , render lens state
        , HH.text if value == "" then ""
          else " (" <> value <> ")"
        ]
    where value = state ^. lens
