module Halogen.HTML.Lens
    ( Query,
    suggestionSetter, suggestionLens,
    inputSetter, inputQuery, inputAttr, inputHTML,
    fieldHTML, eval,
    module EssentialLens
    ) where

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
import Data.Either (Either(..))
import Data.Foreign (toForeign)
import Data.Lens (lens, (.~))
import Data.Lens (lens, Lens') as EssentialLens
import Data.Lens.Getter ((^.))
import Data.Lens.Types (Lens')

data Query s a = UpdateState (forall eff. Eff (dom :: DOM | eff) (s -> s)) a

type Property s p = H.IProp p (Query s)
type Element s p = H.HTML p (Query s)

suggestionSetter ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    (s -> a -> s)
suggestionSetter main convert goal state value
    | (state ^. main # convert) == state ^. goal
    = main .~ value $ goal .~ (convert value) $ state
    | otherwise = main .~ value $ state

suggestionLens ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    Lens' s a
suggestionLens main convert goal =
    lens (_ ^. main) (suggestionSetter main convert goal)

inputSetter :: forall s eff. Lens' s String -> Event -> Eff (dom :: DOM | eff) (s -> s)
inputSetter lens e =
    case runExcept $ readHTMLInputElement $ toForeign $ Event.target e of
        Left _ -> pure id
        Right node -> do
            value <- H.liftEff $ HInput.value node
            pure (lens .~ value)

inputQuery :: forall s a. Lens' s String -> Event -> a -> Query s a
inputQuery lens e = UpdateState (inputSetter lens e)

inputAttr :: forall s p. Lens' s String -> Property s (onInput :: Event | p)
inputAttr lens = HE.onInput (HE.input (inputQuery lens))

inputHTML :: forall s p. Lens' s String -> s -> Element s p
inputHTML lens state = HH.input
    [ inputAttr lens
    , HP.value (state ^. lens)
    ]

fieldHTML :: forall s p. String -> Lens' s String -> s -> Element s p
fieldHTML label lens state =
    HH.div_
        [ HH.text (label <> ": ")
        , inputHTML lens state
        , HH.text if value == "" then ""
          else " (" <> value <> ")"
        ]
    where value = state ^. lens

eval :: forall s eff. Query s ~> H.ComponentDSL s (Query s) Void (Aff (dom :: DOM | eff))
eval (UpdateState run next) = do
    reset <- H.liftEff run
    H.modify reset
    pure next
