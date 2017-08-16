module Component where

import Prelude

import Control.Monad.Aff (Aff)
import DOM (DOM)
import Data.Array (filter, foldr, intercalate, mapWithIndex)
import Data.Array as Array
import Data.Char (fromCharCode, toUpper)
import Data.Char.Unicode (isAlphaNum, isSpace)
import Data.Foldable (fold)
import Data.Lens (ALens', Traversal', cloneLens, (%~), (.~), (^.), (^?))
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.Lens.Suggestion (Lens', lens, suggest)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (joinWith, singleton, uncons)
import Data.String.CodePoints as Str
import Data.String.Regex (split) as Re
import Data.String.Regex.Flags (unicode) as Re
import Data.String.Regex.Unsafe (unsafeRegex) as Re
import Data.String.Utils (words)
import Data.Symbol (SProxy(..))
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

_description :: Lens' State String
_description = lens (_.description) (\s d -> s { description = d })

_name :: Lens' State String
_name = lens (_.name) (\s n -> s { name = n })

_fieldPrefix :: Lens' State String
_fieldPrefix = lens (_.fieldPrefix) (\s e -> s { fieldPrefix = e })

_hasSourceAnn :: Lens' State Boolean
_hasSourceAnn = lens (_.hasSourceAnn) (\s i -> s { hasSourceAnn = i })

_fields :: Lens' State (Array Annotation)
_fields = lens _.fields _ { fields = _ }

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
  "Data" -> ""
  s -> Str.toLower (Str.take 1 s)

_suggestDescription :: Lens' State String
_suggestDescription = suggest _description toName _suggestFieldPrefix

_suggestFieldPrefix :: Lens' State String
_suggestFieldPrefix = suggest _name toPrefix _fieldPrefix

descriptionComponent :: forall p. State -> Element p
descriptionComponent = HL.Input.renderAsField "Description" _suggestDescription

nameComponent :: forall p. State -> Element p
nameComponent = HL.Input.renderAsField "Name" _suggestFieldPrefix

fieldPrefixComponent :: forall p. State -> Element p
fieldPrefixComponent = HL.Input.renderAsField "Prefix for the fields" _fieldPrefix

hasSourceAnnComponent :: forall p. State -> Element p
hasSourceAnnComponent = HL.Checkbox.renderAsField "Contains a source annotation" _hasSourceAnn

addField :: State -> State
addField s = s { fields = nonEmptyFields s.fields <> [{ name: "", typ: "" }] }

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
      , HH.ol_ $ HH.li_ <$> withLenses renderField _fields state
      , HH.div_ [ HL.Button.renderAsField "Add field" addField false ]
      , HH.h2_ [ HH.text "Generated code" ]
      , generateSource state
      ]

  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval = HL.eval

traversalDefault :: forall a b. b -> Traversal' a b -> Lens' a b
traversalDefault b l = lens
  (\v -> fromMaybe b (v ^? l))
  (\v b' -> (l .~ b') v)

withLenses :: forall a b r. (Int -> a -> ALens' a b -> r) -> Lens' a (Array b) -> a -> Array r
withLenses lenser getarr st =
  Array.mapWithIndex (\i v -> (getarr <<< (traversalDefault v (ix i))) # lenser i st)
    (st ^. getarr)

tryDeleteAt :: Int -> Array ~> Array
tryDeleteAt i a = Array.deleteAt i a # fromMaybe a

renderField :: forall p. Int -> State -> ALens' State Annotation -> Array (Element p)
renderField i state alens =
  [ HL.Button.renderAsField "\x2212" (_fields %~ tryDeleteAt i) false
  , HH.text " "
  , HL.Input.render _suggestTyp state
  , HH.text " :: "
  , HL.Input.render _typ state
  ]
  where
    thislens :: Lens' State Annotation
    thislens = cloneLens alens
    _name :: Lens' State String
    _name = thislens <<< prop (SProxy :: SProxy "name")
    _typ :: Lens' State String
    _typ = thislens <<< prop (SProxy :: SProxy "typ")
    _suggestTyp :: Lens' State String
    _suggestTyp = suggest _name id _typ

showField :: Annotation -> String
showField { name, typ } = name <> " :: " <> typ

showStrictField :: Annotation -> String
showStrictField { name, typ } = name <> " :: !" <> typ

nonEmptyFields :: Array Annotation -> Array Annotation
nonEmptyFields = filter \{ name, typ } ->
  name /= "" && typ /= ""

texts :: forall p. Array String -> Array (Element p)
texts = map HH.text

from :: forall p. Array String -> Element p
from = HH.span_ <<< texts

commentline :: forall p. String -> Element p
commentline text = from [ "-- ", text, "\n" ]

separate :: forall p i. HH.HTML p i -> Array (HH.HTML p i) -> HH.HTML p i
separate sep = HH.span_ <<< intercalate [sep] <<< map Array.singleton

defn :: forall p. Annotation -> Array String -> String -> Array (Element p)
defn { name, typ } args body = HH.div_ <<< pure <<< HH.text <$>
  [ name <> " :: " <> typ
  , name <> " " <> joinWith " " args <> " = " <> body
  ]

generateSource :: forall p. State -> Element p
generateSource state@{ description, name, fieldPrefix, hasSourceAnn, fields } = HH.pre_ $
    [ commentline description
    , HH.div_ $ pure $ from ["data ", tyname, " = ", tyname]
    , HH.div_ $ HH.div_ <<< pure <<< HH.text <$>
        record allFields " deriving (Show, Eq)"
    ] <> clsSourceAnn <> unwrapper
    where
    tyname = name <> "Data"
    realFields = nonEmptyFields fields
    allFields = (if hasSourceAnn then
      [ { name: "SourceAnn", typ: "SourceAnn" }
      ] else []) <> realFields
    record [] s = ["  {}" <> s]
    record [f] s = ["  { " <> fieldPrefix <> showField f <> " }" <> s]
    record fs s = (_ <> pure ("  }" <> s)) $ fs # mapWithIndex \i f ->
      (if i == 0 then "  { " else "  , ") <> fieldPrefix <> showStrictField f
    clsSourceAnn = if hasSourceAnn then
      [ HH.br_
      , HH.div_ $ pure $ HH.text $ "instance HasSourceAnn " <> tyname <> " where"
      , HH.div_ $ pure $ HH.text $ "  getSourceAnn = " <> fieldPrefix <> "SourceAnn"
      ] else []
    unwrapper =
      let mkTuple f = "(" <> joinWith ", " (f <$> realFields) <> ")" in
      if Array.null realFields then []
      else Array.cons HH.br_ $ defn
        { name: "unwrap" <> name
        , typ: tyname <> " -> " <> mkTuple _.typ
        } [fieldPrefix] $ mkTuple \{ name } -> (fieldPrefix <> name <> " " <> fieldPrefix)
