module Halogen.HTML.Lens.TextArea
    ( setter, query, attr
    , render, renderAsField
    ) where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Except (runExcept)
import DOM (DOM)
import DOM.Event.Event as Event
import DOM.Event.Types (Event)
import DOM.HTML.HTMLTextAreaElement as HTextArea
import DOM.HTML.Types (readHTMLTextAreaElement)
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens (Lens', (.~), (^.))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties as HP

type Property s p = H.IProp p (Query s)
type Element s p = H.HTML p (Query s)

setter :: forall s eff. Lens' s String -> Event -> Eff (dom :: DOM | eff) (s -> s)
setter lens e =
    case runExcept $ readHTMLTextAreaElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
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
