module Halogen.HTML.Lens.Checkbox
    ( setter
    , query
    , attr
    , render
    , renderAsField
    ) where

import Prelude
import Web.Event.Event as Event
import Web.HTML.HTMLInputElement as HInput
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect (Effect)
import Control.Monad.Except (runExcept)

import Web.Event.Event (Event)
import Data.Array (singleton)
import Data.Maybe (Maybe(..))
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties (InputType(InputCheckbox))

type Property s p = HH.IProp p (Query s Unit)
type Element s p = HH.HTML p (Query s Unit)

setter :: forall s. Lens' s Boolean -> Event -> Effect (s -> s)
setter lens e =
    case HInput.fromEventTarget =<< Event.target e of
        Nothing -> pure identity
        Just node -> do
            value <- H.liftEffect $ HInput.checked node
            pure (lens .~ value)

query :: forall s a. Lens' s Boolean -> Event -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. Lens' s Boolean -> Property s (onChange :: Event | p)
attr lens = HE.onChange (HE.input (query lens))

render :: forall s p. Lens' s Boolean -> s -> Element s p
render lens state = HH.input
    [ attr lens
    , HP.type_ InputCheckbox
    , HP.checked (state ^. lens)
    ]

renderAsField :: forall s p. String -> Lens' s Boolean -> s -> Element s p
renderAsField label lens state =
    HH.div_ $ singleton $ HH.label_
        [ render lens state
        , HH.text label
        ]
    where value = state ^. lens
