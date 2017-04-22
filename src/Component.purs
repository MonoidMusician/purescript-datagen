module Component where

import Prelude
import DOM.Event.Event as Event
import DOM.HTML.HTMLInputElement as HInput
import Halogen as H
import Halogen.HTML as HH
import Halogen.HTML.Events as HE
import Halogen.HTML.Properties as HP
import Control.Monad.Aff (Aff)
import Control.Monad.Eff (Eff)
import Control.Monad.Except (runExcept)
import DOM (DOM)
import DOM.Event.Types (Event)
import DOM.HTML.Types (readHTMLInputElement)
import Data.Array (filter, foldr, intercalate)
import Data.Array as Array
import Data.Char (toUpper)
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens (lens, (.~))
import Data.Lens.Getter ((^.))
import Data.Lens.Types (Lens')
import Data.Maybe (Maybe(..))
import Data.String (joinWith, singleton, uncons)
import Data.String.Utils (words)

data Query a
    = LensSetAff (forall eff. Eff (dom :: DOM | eff) (State -> State)) a

type Property p = H.IProp p Query
type AnyProperty = forall p. Property p
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

suggest ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    (s -> a -> s)
suggest main convert goal state value
    | (state ^. main # convert) == state ^. goal
    = main .~ value $ goal .~ (convert value) $ state
    | otherwise = main .~ value $ state

suggestL ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    Lens' s a
suggestL main convert goal =
    lens (_ ^. main) (suggest main convert goal)

suggestDescriptionL :: Lens' State String
--suggestDescriptionL = lens (_.description) suggestDescription
suggestDescriptionL = suggestL descriptionL toName nameL

inputlensset :: forall s eff. Lens' s String -> Event -> Eff (dom :: DOM | eff) (s -> s)
inputlensset lens e =
    case runExcept $ readHTMLInputElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
            value <- H.liftEff $ HInput.value node
            pure (lens .~ value)

inputlensquery :: forall a. Lens' State String -> Event -> a -> Query a
inputlensquery lens e = LensSetAff (inputlensset lens e)

inputlensattr :: forall p. Lens' State String -> Property (onInput :: Event | p)
inputlensattr lens = HE.onInput (HE.input (inputlensquery lens))

inputlens :: forall p. Lens' State String -> State -> Element p
inputlens lens state = HH.input
    [ inputlensattr lens
    , HP.value (state ^. lens)
    ]

fieldlens :: forall p. String -> Lens' State String -> State -> Element p
fieldlens label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , inputlens lens state
        , HH.text if value == "" then ""
          else " (" <> value <> ")"
        ]
    where value = state ^. lens

descriptionComponent :: forall p. State -> Element p
descriptionComponent = fieldlens "Description" suggestDescriptionL

nameComponent :: forall p. State -> Element p
nameComponent = fieldlens "Name" nameL

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
  eval (LensSetAff run next) = do
    reset <- H.liftEff run
    H.modify reset
    pure next

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
