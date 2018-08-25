module Halogen.HTML.Lens.Input
    ( setter, query, attr,
    render, renderAsField
    ) where

import Prelude
import Halogen.HTML.Lens (Query(..))
import Web.Event.Event as Event
import Web.HTML.HTMLInputElement as HInput
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect (Effect)
import Control.Monad.Except (runExcept)

import Web.Event.Event (Event)
import Data.Maybe (Maybe(..))
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')

type Property s p = HH.IProp p (Query s Unit)
type Element s p = HH.HTML p (Query s Unit)

setter :: forall s. Lens' s String -> Event -> Effect (s -> s)
setter lens e =
    case HInput.fromEventTarget =<< Event.target e of
        Nothing -> pure identity
        Just node -> do
            value <- H.liftEffect $ HInput.value node
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
