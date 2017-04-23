module Halogen.HTML.Lens.Checkbox
    ( setter
    , query
    , attr
    , render
    , renderAsField
    ) where

import Prelude
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
import Data.Array (singleton)
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties (InputType(InputCheckbox))

type Property s p = H.IProp p (Query s)
type Element s p = H.HTML p (Query s)

setter :: forall s eff. Lens' s Boolean -> Event -> Eff (dom :: DOM | eff) (s -> s)
setter lens e =
    case runExcept $ readHTMLInputElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
            value <- H.liftEff $ HInput.checked node
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
