module Data.Lens.Suggestion
    ( setter
    , suggest
    , module EssentialLens
    ) where

import Prelude ((==), class Eq, (#), ($), otherwise)
import Data.Lens (Lens', (^.), (.~), lens)
import Data.Lens (lens, Lens') as EssentialLens

setter ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    (s -> a -> s)
setter main convert goal state value
    | (state ^. main # convert) == state ^. goal
    = main .~ value $ goal .~ (convert value) $ state
    | otherwise = main .~ value $ state

suggest ::
    forall s a b.
    Eq b =>
    Lens' s a ->
    (a -> b) ->
    Lens' s b ->
    Lens' s a
suggest main convert goal =
    lens (_ ^. main) (setter main convert goal)
