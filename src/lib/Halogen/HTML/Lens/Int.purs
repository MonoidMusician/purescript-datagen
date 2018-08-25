module Halogen.HTML.Lens.Int
    ( setter
    , query
    , attr
    , render
    , renderBounded
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
import Data.Array (cons)
import Data.Maybe (Maybe(..))
import Data.Int (round, toNumber)
import Data.Lens ((.~), (^.))
import Data.Lens.Types (Lens')
import Data.Maybe (Maybe(..))
import Halogen.HTML.Lens (Query(..))
import Halogen.HTML.Properties (InputType(InputNumber))

type Property s p = HH.IProp p (Query s Unit)
type Element s p = HH.HTML p (Query s Unit)

setter :: forall s. Lens' s Int -> Event -> Effect (s -> s)
setter lens e =
    case HInput.fromEventTarget =<< Event.target e of
        Nothing -> pure identity
        Just node -> do
            value <- H.liftEffect $ round <$> HInput.valueAsNumber node
            pure (lens .~ value)

query :: forall s a. Lens' s Int -> Event -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. Lens' s Int -> Property s (onChange :: Event | p)
attr lens = HE.onChange (HE.input (query lens))

renderBounded :: forall s p. Maybe Int -> Maybe Int -> Lens' s Int -> s -> Element s p
renderBounded low high lens state = HH.input (
    [ attr lens
    , HP.value $ show (state ^. lens)
    , HP.type_ InputNumber
    ] `mattr` (HP.min <$> toNumber <$> low)
      `mattr` (HP.max <$> toNumber <$> high)
    )
  where
    mattr tail = case _ of
      Just head -> cons head tail
      Nothing -> tail

--render :: forall s p. Lens' s Int -> s -> Element s p
render = renderBounded Nothing Nothing

renderAsField :: forall s p. String -> Lens' s Int -> s -> Element s p
renderAsField label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , render lens state
        , HH.text (" (" <> show value <> ")")
        ]
    where value = state ^. lens
