module HoTT where

import Prelude

import Data.Bifunctor (bimap)
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Data.Variant (Variant)
import Data.Variant as Variant
import Effect (Effect)
import Effect.Aff (Aff)
import Halogen as H
import Halogen.Aff (awaitBody, runHalogenAff)
import Halogen.Autocomplete.Component as Autocomplete
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.VDom.Driver (runUI)
import Halogen.Pager (renderPage)

type StaticSlot = H.Slot (Tuple (Variant Pages)) (Either (Variant Pages) Void) Unit
type Slots =
  ( intro :: StaticSlot
  , functions :: StaticSlot
  )
type StaticPage = Tuple Unit Unit
type Pages =
  ( intro :: StaticPage
  , functions :: StaticPage
  )
type State =
  { page :: Variant Pages }
data Query a = ToPage a (Variant Pages)

static :: forall p. HH.HTML Void p -> H.Component HH.HTML (Tuple p) Unit (Either p Void) Aff
static visor = H.component
  { eval: \(Tuple p a) -> a <$ H.raise (Left p)
  , render: const (bimap absurd (Tuple <@> unit) visor)
  , initialState: const unit
  , receiver: const Nothing
  , initializer: Nothing
  , finalizer: Nothing
  }

staticPage :: HH.HTML Void (Variant Pages) ->
  Tuple
    (H.Component HH.HTML (Tuple (Variant Pages)) Unit (Either (Variant Pages) Void) Aff)
    (Either (Variant Pages) Void -> Maybe (Query Unit))
staticPage visor = Tuple (static visor) (pure <<< either (ToPage unit) absurd)

component :: H.Component HH.HTML Query Unit Void Aff
component = H.component
  { eval
  , render
  , initialState: const { page: intro }
  , receiver: const Nothing
  , initializer: Nothing
  , finalizer: Nothing
  } where
    noLink = HP.href "javascript:void(0)"
    pageLink pg = HH.a [ noLink, HE.onClick (pure $ pure pg) ]
    intro = Variant.inj (SProxy :: SProxy "intro") mempty
    functions = Variant.inj (SProxy :: SProxy "functions") mempty
    pager :: Variant Pages -> H.ComponentHTML Query Slots Aff
    pager = renderPage
      { intro: staticPage $
          pageLink functions
            [ HH.text "About functions." ]
      , functions: staticPage $
          pageLink intro
            [ HH.text "Back to beginning." ]
      }

    render :: State -> H.ComponentHTML Query Slots Aff
    render = pager <<< _.page

    eval :: Query ~> H.HalogenM State Query Slots Void Aff
    eval (ToPage a p) = a <$ H.modify_ _ { page = p }

main :: Effect Unit
main = runHalogenAff do
  body <- awaitBody
  runUI component unit body
