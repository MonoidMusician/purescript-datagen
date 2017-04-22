module Component where

import Prelude
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Halogen.HTML.Lens as HL
import Halogen.HTML.Lens.Input as HL.Input
import Control.Monad.Aff (Aff)
import DOM (DOM)
import Data.Array (filter, foldr, intercalate)
import Data.Array as Array
import Data.Char (toUpper)
import Data.Maybe (Maybe(..))
import Data.Lens.Suggestion (Lens', lens, suggest)
import Data.String (joinWith, singleton, uncons)
import Data.String.Utils (words)

type Query = HL.Query State

type Element p = H.HTML p Query

type State =
  { description :: String
  , name :: String
  }

descriptionL :: Lens' State String
descriptionL = lens (_.description) (\s d -> s { description = d })

nameL :: Lens' State String
nameL = lens (_.name) (\s d -> s { name = d })

toName :: String -> String
toName = words >>> exclude >>> map camel >>> joinWith ""
    where
    blacklist = ["this", "the","a","an","it"]
    exclude ws =
        foldr (\w -> filter (w /= _)) ws blacklist
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
    { description: "Aim the camera"
    , name: "AimCamera"
    }

  render :: State -> H.ComponentHTML Query
  render state@{ description, name } =
    HH.div_
      [ HH.h1_
          [ HH.text "Create FRC Command" ]
      , descriptionComponent state
      , nameComponent state
      , HH.a_ $ texts ["Commands/", name, ".h" ]
      , generateHeader state
      , HH.a_ $ texts ["Commands/", name, ".cpp" ]
      , generateSource state
      ]

  eval :: Query ~> H.ComponentDSL State Query Void (Aff (dom :: DOM | eff))
  eval = HL.eval

texts :: forall p. Array String -> Array (Element p)
texts = map HH.text

from :: forall p. Array String -> Element p
from = HH.span_ <<< texts

commentline :: forall p. String -> Element p
commentline text = from [ "// ", text, "\n" ]

separate :: forall p i. HH.HTML p i -> Array (HH.HTML p i) -> HH.HTML p i
separate sep = HH.span_ <<< intercalate [sep] <<< map Array.singleton

generateHeader :: forall p. State -> Element p
generateHeader state@{ description, name } = HH.pre_ $
    [ commentline description
    , from [ "class ", name, " : public frc::Command {\n"]
    , HH.text "private:\n"
    , HH.text "public:\n"
    , from [ "\t", name, "();\n" ]
    , HH.text "}"
    ]

generateSource :: forall p. State -> Element p
generateSource state@{ description, name } = HH.pre_ $
    [ commentline description
    , method name [] []
    , method "Initialize" [] []
    , method "Execute" [] []
    , method "IsFinished" [] []
    , method "Done" [] []
    , method "Interrupted" [] []
    ]
    where
    method mname args body = HH.span_
        [ from
            [ name
            , "::"
            , mname
            , "("
            ]
        , separate (HH.text ", ") args
        , from [ ") {\n" ]
        , separate (HH.text "\n\t") body
        , from [ "}\n\n" ]
        ]
