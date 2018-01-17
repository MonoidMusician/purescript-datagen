module Autocomplete where

import Prelude

import Control.Monad.Eff (Eff)
import DOM.Node.ParentNode (QuerySelector(..))
import Data.Array (unsnoc)
import Data.Bifunctor (lmap)
import Data.Foldable (traverse_)
import Data.Function (on)
import Data.Maybe (Maybe(..))
import Data.NonEmpty ((:|))
import Data.String (Pattern(..), joinWith, split)
import Data.String as String
import Data.Tuple (Tuple(..))
import Halogen.Aff as HA
import Halogen.Autocomplete.Component as AC
import Halogen.HTML as HH
import Halogen.VDom.Driver (runUI)
import Prim.Repr (kindArrow, primKinds, rowKind, functor)
import Reprinting (showAKind)
import Types (AKindV, Module(..), Proper(..), Qualified(..))

containsInsensitive :: String -> String -> Boolean
containsInsensitive = (String.contains <<< String.Pattern) `on` String.toLower

decompose :: String -> Maybe (Tuple (Array String) String)
decompose s = unsnoc (split (Pattern ".") s) <#>
  \{ init, last } -> Tuple init last

customElemConf :: forall r. AC.Config { name :: Qualified Proper, kind :: AKindV | r }
customElemConf = AC.defaultConfig
  { itemText = itemText
  , itemDisplay = \{ name: p, kind: k } -> HH.div_ [ HH.text (show p), HH.br_ , HH.code_ [HH.text ("Kind: " <> showAKind k)] ]
  , itemFilter = itemFilter
  }
  where
    itemText = _.name >>> show
    itemFilter input = case decompose input of
      Nothing -> const false
      Just (Tuple moduleInput typeInput) -> \{ name: q } ->
        let
          Tuple mod typ = case q of
            Unqualified typ -> Tuple Nothing typ
            Qualified mod typ -> Tuple (Just mod) typ
          matchModule = case mod of
            Nothing -> moduleInput == []
            Just modul -> containsInsensitive
              (joinWith "." moduleInput)
              (show modul)
          matchType = containsInsensitive typeInput (show typ)
        in matchModule && matchType

items :: Array (Tuple (Qualified Proper) AKindV)
items = lmap (Qualified (Module (Proper "Zippers" :| []))) <$>
  [ Tuple (Proper "DStrMap")    $ functor
  , Tuple (Proper "VF")         $ kindArrow (rowKind primKinds."Type") functor
  , Tuple (Proper "DF")         $ kindArrow functor functor
  , Tuple (Proper "ATypeVR")    $ rowKind primKinds."Type"
  , Tuple (Proper "DPair")      $ functor
  , Tuple (Proper "ParentCtxs") $ functor
  , Tuple (Proper "ParentCtx")  $ functor
  , Tuple (Proper "Tag")        $ primKinds."Type"
  , Tuple (Proper "ZRec")       $ functor
  , Tuple (Proper "ZF")         $ kindArrow functor functor
  , Tuple (Proper "ZipperVRec") $ primKinds."Type"
  ]

main :: Eff (HA.HalogenEffects ()) Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  HA.selectElement (QuerySelector "#customElement") >>= traverse_
    (runUI (AC.component customElemConf) $ items <#> \(Tuple q k) -> { name: q, kind: k })
