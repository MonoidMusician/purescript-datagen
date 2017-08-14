module Component where

import Prelude

import Control.Monad.Aff (Aff)
import DOM (DOM)
import Data.Array (filter, foldr, intercalate, mapWithIndex)
import Data.Array as Array
import Data.Char (fromCharCode, toUpper)
import Data.Char.Unicode (isAlphaNum, isSpace)
import Data.Foldable (fold)
import Data.Lens.Suggestion (Lens', lens, suggest)
import Data.Maybe (Maybe(..))
import Data.String (joinWith, singleton, uncons)
import Data.String.CodePoints as Str
import Data.String.Regex (split) as Re
import Data.String.Regex.Flags (unicode) as Re
import Data.String.Regex.Unsafe (unsafeRegex) as Re
import Data.String.Utils (words)
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Lens as HL
import Halogen.HTML.Lens.Button as HL.Button
import Halogen.HTML.Lens.Checkbox as HL.Checkbox
import Halogen.HTML.Lens.Input as HL.Input
import Halogen.HTML.Properties as HP

type Query = HL.Query State

type Element p = H.HTML p Query

type Annotation =
  { name :: String
  , typ :: String
  }

type State =
  { description :: String
  , name :: String
  , fieldPrefix :: String
  , hasSourceAnn :: Boolean
  , fields :: Array Annotation
  }

descriptionL :: Lens' State String
descriptionL = lens (_.description) (\s d -> s { description = d })

nameL :: Lens' State String
nameL = lens (_.name) (\s n -> s { name = n })

fieldPrefixL :: Lens' State String
fieldPrefixL = lens (_.fieldPrefix) (\s e -> s { fieldPrefix = e })

hasSourceAnnL :: Lens' State Boolean
hasSourceAnnL = lens (_.hasSourceAnn) (\s i -> s { hasSourceAnn = i })

ccwords :: String -> Array String
ccwords = filter (not eq "") <<< Re.split re
  where re = Re.unsafeRegex "([A-Z][a-z]+|[A-Z]+(?=[A-Z][a-z]))" Re.unicode

toName :: String -> String
toName = firstpart >>> words >>> exclude >>> map camel >>> joinWith ""
    where
    unsafeChar = Str.codePointToInt >>> fromCharCode
    firstpart = Str.takeWhile $ unsafeChar >>> (isAlphaNum || isSpace)
    blacklist = ["this","the","a","an","it"]
    exclude ws =
        foldr (\w -> filter (not eq w <<< Str.toLower)) ws blacklist
    camel s =
        case uncons s of
            Nothing -> s
            Just { head, tail } ->
                (head # toUpper # singleton) <> tail

toPrefix :: String -> String
toPrefix = fold <<< ccwords >>> map case _ of
  "Type" -> "ty"
  "Declaration" -> "decl"
  s -> Str.toLower (Str.take 1 s)

suggestDescriptionL :: Lens' State String
suggestDescriptionL = suggest descriptionL toName suggestFieldPrefixL

suggestFieldPrefixL :: Lens' State String
suggestFieldPrefixL = suggest nameL toPrefix fieldPrefixL

descriptionComponent :: forall p. State -> Element p
descriptionComponent = HL.Input.renderAsField "Description" suggestDescriptionL

nameComponent :: forall p. State -> Element p
nameComponent = HL.Input.renderAsField "Name" suggestFieldPrefixL

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
    , fields: []
    }

  render :: State -> H.ComponentHTML Query
  render state@{ description, name, fields } =
    HH.div_
      [ HH.h1_
          [ HH.text "Create PureScript Compiler Data Type" ]
      , descriptionComponent state
      , nameComponent state
      , fieldPrefixComponent state
      , hasSourceAnnComponent state
      , HH.h2_ [ HH.text "Fields" ]
      , HH.ol_ $ HH.li_ <<< pure <<< renderField <$> fields
      , HH.h2_ [ HH.text "Generated code" ]
      , generateSource state
      --, HL.Button.ren
      ]

  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval = HL.eval

renderField :: forall p. Annotation -> Element p
renderField = HH.text <<< showField

showField :: Annotation -> String
showField { name, typ } = name <> " :: " <> typ

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
    allFields = if hasSourceAnn then
      [ { name: "SourceAnn", typ: "SourceAnn" }
      ] else []
    record [] = ["  {}"]
    record [f] = ["  { " <> fieldPrefix <> showField f <> " }"]
    record fs = (_ <> pure "  }") $ fs # mapWithIndex \i f ->
      (if i == 0 then "  { " else "  , ") <> fieldPrefix <> showField f
