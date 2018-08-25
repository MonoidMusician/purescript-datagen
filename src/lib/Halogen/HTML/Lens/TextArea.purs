module Halogen.HTML.Lens.TextArea
    ( setter, query, attr
    , render, renderAsField
    ) where

import Prelude

import Effect (Effect)
import Control.Monad.Except (runExcept)

import Web.Event.Event as Event
import Web.Event.Event (Event)
import Web.HTML.HTMLTextAreaElement as HTextArea
import Data.Maybe (Maybe(..))
import Data.Lens (Lens', (.~), (^.))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties as HP

type Property s p = HH.IProp p (Query s Unit)
type Element s p = HH.HTML p (Query s Unit)

setter :: forall s. Lens' s String -> Event -> Effect (s -> s)
setter lens e =
    case HTextArea.fromEventTarget =<< Event.target e of
        Nothing -> pure identity
        Just node -> do
            value <- HTextArea.value node
            pure (lens .~ value)

query :: forall s a. Lens' s String -> Event -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. Lens' s String -> Property s (onInput :: Event | p)
attr lens = HE.onInput (HE.input (query lens))

render :: forall s p. Lens' s String -> s -> Element s p
render lens state = HH.textarea
    [ attr lens
    , HP.value (state ^. lens)
    ]

renderAsField :: forall s p. String -> Lens' s String -> s -> Element s p
renderAsField label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , render lens state
        ]
    where value = state ^. lens
