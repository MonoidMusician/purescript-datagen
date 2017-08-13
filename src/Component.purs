module Component where

import Prelude

import Control.Monad.Aff (Aff)
import DOM (DOM)
import Data.Array (filter, foldr, intercalate)
import Data.Array as Array
import Data.Char (toUpper)
import Data.Lens.Suggestion (Lens', lens, suggest)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), joinWith, singleton, split, uncons)
import Data.String (toUpper, toLower) as Str
import Data.String.Utils (words)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Lens as HL
import Halogen.HTML.Lens.Checkbox as HL.Checkbox
import Halogen.HTML.Lens.Input as HL.Input
import Halogen.HTML.Lens.TextArea as HL.TextArea
import Halogen.HTML.Properties as HP

type Query = HL.Query State

type Element p = H.HTML p Query

type State =
  { description :: String
  , name :: String
  , fieldPrefix :: String
  , hasSourceAnn :: Boolean
  }

descriptionL :: Lens' State String
descriptionL = lens (_.description) (\s d -> s { description = d })

nameL :: Lens' State String
nameL = lens (_.name) (\s n -> s { name = n })

fieldPrefixL :: Lens' State String
fieldPrefixL = lens (_.fieldPrefix) (\s e -> s { fieldPrefix = e })

hasSourceAnnL :: Lens' State Boolean
hasSourceAnnL = lens (_.hasSourceAnn) (\s i -> s { hasSourceAnn = i })

toName :: String -> String
toName = words >>> exclude >>> map camel >>> joinWith ""
    where
    blacklist = ["this", "the","a","an","it"]
    exclude ws =
        foldr (\w -> filter (not eq w <<< Str.toLower)) ws blacklist
    camel s =
        case uncons s of
            Nothing -> s
            Just { head, tail } ->
                (head # toUpper # singleton) <> tail

suggestDescriptionL :: Lens' State String
suggestDescriptionL = suggest descriptionL toName nameL

descriptionComponent :: forall p. State -> Element p
descriptionComponent = HL.Input.renderAsField "Description" suggestDescriptionL

nameComponent :: forall p. State -> Element p
nameComponent = HL.Input.renderAsField "Name" nameL

fieldPrefixComponent :: forall p. State -> Element p
fieldPrefixComponent = HL.Input.renderAsField "Prefix for the fields" fieldPrefixL

hasSourceAnnComponent :: forall p. State -> Element p
hasSourceAnnComponent = HL.Checkbox.renderAsField "Contains a source annotation" hasSourceAnnL

component :: forall eff. H.Component HH.HTML Query Unit Void (Aff (dom :: DOM | eff))
component =
  H.component
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    }
  where

  initialState :: State
  initialState =
    { description: "A type declaration"
    , name: "TypeDeclaration"
    , fieldPrefix: "tydecl"
    , hasSourceAnn: true
    }

  render :: State -> H.ComponentHTML Query
  render state@{ description, name } =
    HH.div_
      [ HH.h1_
          [ HH.text "Create PureScript Compiler Data Type" ]
      , descriptionComponent state
      , nameComponent state
      , fieldPrefixComponent state
      , hasSourceAnnComponent state
      , generateSource state
      ]

  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval = HL.eval

texts :: forall p. Array String -> Array (Element p)
texts = map HH.text

from :: forall p. Array String -> Element p
from = HH.span_ <<< texts

commentline :: forall p. String -> Element p
commentline text = from [ "-- ", text, "\n" ]

separate :: forall p i. HH.HTML p i -> Array (HH.HTML p i) -> HH.HTML p i
separate sep = HH.span_ <<< intercalate [sep] <<< map Array.singleton

generateSource :: forall p. State -> Element p
generateSource state@{ description, name, fieldPrefix, hasSourceAnn } = HH.pre_ $
    [ commentline description
    , HH.div_ $ pure $ from ["data ", name, " = ", name]
    , HH.div_ $ HH.div_ <<< pure <<< HH.text <$> record allFields
    ]
    where
    allFields = if hasSourceAnn then [fieldPrefix <> "SourceAnn :: SourceAnn"] else []
    record [] = ["  {}"]
    record [f] = ["  { " <> f <> " }"]
    record fs = fs
