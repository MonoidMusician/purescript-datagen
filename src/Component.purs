module Component where

import Prelude

import Combinators (aTypeVar)
import Control.Alt ((<|>))
import Effect.Aff (Aff)

import Data.Array (filter, foldr, intercalate)
import Data.Array as Array
import Data.Char (fromCharCode)
import Data.Char.Unicode (isAlphaNum, isSpace)
import Data.Const (Const(..))
import Data.Functor.Mu (roll)
import Data.Functor.Variant as VF
import Data.Lens (ALens', Prism', Traversal', _1, _2, anyOf, cloneLens, iso, preview, prism', (.~), (^.), (^?))
import Data.Lens.Index (ix)
import Data.Lens.Record (prop)
import Data.Lens.Suggestion (Lens', lens, suggest)
import Data.Maybe (Maybe(..), fromMaybe, maybe)
import Data.String (joinWith, singleton, uncons, toUpper)
import Data.String as Str
import Data.String.Regex (split) as Re
import Data.String.Regex.Flags (unicode) as Re
import Data.String.Regex.Unsafe (unsafeRegex) as Re
import Data.String.Utils (words)
import Data.Symbol (SProxy(..))
import Data.Tuple (Tuple(..))
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Lens as HL
import Halogen.HTML.Lens.Button as HL.Button
import Halogen.HTML.Lens.Checkbox as HL.Checkbox
import Halogen.HTML.Lens.Input as HL.Input
import Reprinting (showAType, showDataType)
import Types (ATypeV, DataType(..), DataTypeDecl, DataTypeDef(..), Proper(..), Ident(..), Qualified(..), TypeAbses, TypeAbs(..), declKeyword)
import Types as T
import Repr.Prim (primKinds)
import Data.Enum (fromEnum)

type Query = HL.Query State

type Element p = HH.HTML p (Query Unit)

type Annotation =
  { name :: String
  , typ :: String
  }

type State =
  { description :: String
  , datatype :: DataTypeDecl
  }

_description :: Lens' State String
_description = prop (SProxy :: SProxy "description")

_datatype :: Lens' State DataTypeDecl
_datatype = prop (SProxy :: SProxy "datatype")

_name :: Lens' State Proper
_name = _datatype <<< _1

_vars :: Lens' State TypeAbses
_vars = _datatype <<< _2 <<< lens
  (\(DataTypeDef as _) -> as)
  (\(DataTypeDef _ d) as -> DataTypeDef as d)

_typedata :: Lens' State DataType
_typedata = _datatype <<< _2 <<< lens
  (\(DataTypeDef _ d) -> d)
  (\(DataTypeDef as _) d -> DataTypeDef as d)

_typeAlias :: Prism' DataType ATypeV
_typeAlias = prism' TypeAlias case _ of
  TypeAlias m -> Just m
  _ -> Nothing

_sumType :: Prism' DataType (Array (Tuple Proper (Array ATypeV)))
_sumType = prism' SumType case _ of
  SumType m -> Just m
  _ -> Nothing

_typeAliasData :: Traversal' State ATypeV
_typeAliasData = _typedata <<< _typeAlias

_sumTypeData :: Traversal' State (Array (Tuple Proper (Array ATypeV)))
_sumTypeData = _typedata <<< _sumType

ccwords :: String -> Array String
ccwords = filter (not eq "") <<< Re.split re
  where re = Re.unsafeRegex "([A-Z][a-z]+|[A-Z]+(?=[A-Z][a-z]))" Re.unicode

toName :: String -> String
toName = firstpart >>> words >>> exclude >>> map camel >>> joinWith ""
    where
    unsafeChar = fromEnum >>> fromCharCode
    firstpart = Str.takeWhile $ unsafeChar >>> maybe false (isAlphaNum || isSpace)
    blacklist = ["this","the","a","an","it"]
    exclude ws =
        foldr (\w -> filter (not eq w <<< Str.toLower)) ws blacklist
    camel s =
        case uncons s of
            Nothing -> s
            Just { head, tail } ->
                (head # singleton # toUpper) <> tail

_suggestDescription :: Lens' State String
_suggestDescription = suggest _description toName (_name <<< iso show Proper)

descriptionComponent :: forall p. State -> Element p
descriptionComponent = HL.Input.renderAsField "Description" _suggestDescription

nameComponent :: forall p. State -> Element p
nameComponent = HL.Input.renderAsField "Name" (_name <<< iso show Proper)

emptyAlias :: DataType
emptyAlias = TypeAlias $ roll $ VF.inj T._name $ Const $ Unqualified $ Proper "_"

_isTypeAlias :: Lens' State Boolean
_isTypeAlias = lens
  (anyOf _typeAliasData (const true))
  (\s alias -> (_typedata .~ if alias then emptyAlias else SumType []) s)

typeComponent :: forall p. State -> Element p
typeComponent = HL.Checkbox.renderAsField "Simple type alias" _isTypeAlias

component :: H.Component HH.HTML Query Unit Void Aff
component =
  H.component
    { initialState: const initialState
    , render
    , eval
    , receiver: const Nothing
    , initializer: Nothing
    , finalizer: Nothing
    }
  where

  initialState :: State
  initialState =
    { description: "A data type definition"
    , datatype: Tuple (Proper "These") $
        DataTypeDef
          [ TypeAbs (Ident "left") (Just primKinds."Type")
          , TypeAbs (Ident "right") (Just primKinds."Type")
          ] $
          SumType
            [ Tuple (Proper "This")
              [ aTypeVar $ Ident "left" ]
            , Tuple (Proper "That")
              [ aTypeVar $ Ident "right" ]
            , Tuple (Proper "These")
              [ aTypeVar $ Ident "left"
              , aTypeVar $ Ident "right"
              ]
            ]
    }

  render :: State -> H.ComponentHTML Query () Aff
  render state@{ description, datatype } =
    HH.div_
      [ HH.h1_
          [ HH.text "Create PureScript Data Type" ]
      , descriptionComponent state
      , nameComponent state
      , typeComponent state
      , HH.h2_ [ HH.text if state ^. _isTypeAlias then "Type" else "Constructors" ]
      , fromMaybe (HH.text "") (renderedTypeAlias <|> renderedConstructors)
      --, HH.ol_ $ HH.li_ <$> withLenses renderField _constructors state
      --, HH.div_ [ HL.Button.renderAsField "Add constructor" addField false ]
      , HH.h2_ [ HH.text "Generated code" ]
      , generateSource state
      ]
      where
        renderedTypeAlias = preview _typeAliasData state <#>
          \atype -> HH.text $ showAType atype
        renderedConstructors = preview _sumTypeData state <#>
          \constructors -> HH.ol_ $ constructors <#> \(Tuple constructor args) ->
            HH.li_ $ append [HH.text $ show constructor] $ args <#> \arg ->
              HH.div_ [HH.text $ showAType arg]


  eval :: Query ~> H.HalogenM State Query () Void Aff
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
tryDeleteAt i = fromMaybe <*> Array.deleteAt i

renderField :: forall p. Int -> State -> ALens' State Annotation -> Array (Element p)
renderField i state alens =
  [ HL.Button.renderAsField "\x2212" (identity {-_constructors %~ tryDeleteAt i-}) false
  , HH.text " "
  , HL.Input.render _suggestTyp state
  , HH.text " :: "
  , HL.Input.render _thistyp state
  ]
  where
    thislens :: Lens' State Annotation
    thislens = cloneLens alens
    _thisname :: Lens' State String
    _thisname = thislens <<< prop (SProxy :: SProxy "name")
    _thistyp :: Lens' State String
    _thistyp = thislens <<< prop (SProxy :: SProxy "typ")
    _suggestTyp :: Lens' State String
    _suggestTyp = suggest _thisname identity _thistyp

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
generateSource state@{ description, datatype } = HH.pre_ $
    [ commentline description
    , HH.div_ $ pure $ from [show (declKeyword (state ^. _typedata)), " ", name, sep, definition]
    ]
    where
      name = show (state ^. _name)
      sep = if definition /= "" then " = " else ""
      definition = showDataType (state ^. _typedata)
