module Halogen.HTML.Lens.Button
    ( setter
    , query
    , attr
    , render
    , renderAsField
    ) where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Effect (Effect)

import Web.UIEvent.MouseEvent (MouseEvent)
import Data.Array (singleton)
import Halogen.HTML.Lens (Query(..))

type Property s p = HH.IProp p (Query s Unit)
type Element s p = HH.HTML p (Query s Unit)

setter :: forall s. (s -> s) -> MouseEvent -> Effect (s -> s)
setter lens e = pure lens

query :: forall s a. (s -> s) -> MouseEvent -> a -> Query s a
query lens e = UpdateState (setter lens e)

attr :: forall s p. (s -> s) -> Property s (onClick :: MouseEvent | p)
attr lens = HE.onClick (HE.input (query lens))

render :: forall s p. (s -> s) -> s -> Element s p
render lens state = HH.button [ attr lens ] []

renderAsField :: forall s p. String -> (s -> s) -> Boolean -> Element s p
renderAsField label lens disabled =
    HH.button
        [ attr lens, HP.disabled disabled ]
        [ HH.text label ]
