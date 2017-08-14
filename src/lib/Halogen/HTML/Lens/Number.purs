module Halogen.HTML.Lens.Number
    ( setter
    , query
    , attr
    , render
    , renderBounded
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
import Data.Array (cons)
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')
import Data.Maybe (Maybe(..))
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties (InputType(InputNumber))

type Property s p = H.IProp p (Query s)
type Element s p = H.HTML p (Query s)

setter :: forall s eff. Lens' s Number -> Event -> Eff (dom :: DOM | eff) (s -> s)
setter lens e =
    case runExcept $ readHTMLInputElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
            value <- H.liftEff $ HInput.valueAsNumber node
            pure (lens .~ value)

query :: forall s a. Lens' s Number -> Event -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. Lens' s Number -> Property s (onChange :: Event | p)
attr lens = HE.onChange (HE.input (query lens))

renderBounded :: forall s p. Maybe Number -> Maybe Number -> Lens' s Number -> s -> Element s p
renderBounded low high lens state = HH.input (
    [ attr lens
    , HP.value $ show (state ^. lens)
    , HP.type_ InputNumber
    ] `mattr` (HP.min <$> low)
      `mattr` (HP.max <$> high)
    )
  where
    mattr tail = case _ of
      Just head -> cons head tail
      Nothing -> tail

--render :: forall s p. Lens' s Number -> s -> Element s p
render = renderBounded Nothing Nothing

renderAsField :: forall s p. String -> Lens' s Number -> s -> Element s p
renderAsField label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , render lens state
        , HH.text (" (" <> show value <> ")")
        ]
    where value = state ^. lens
