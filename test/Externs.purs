module Test.Externs where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Control.Monad.Eff.Exception (EXCEPTION)
import Data.Argonaut (fromArray, fromString, jsonParser)
import Data.Array (filterA, mapMaybe)
import Data.Foldable (for_, traverse_)
import Data.String (Pattern(..), split)
import Data.Tuple (Tuple(..))
import Externs.Parse (externsJustTypes)
import Externs.Parse.Names (parseModule)
import Node.Encoding (Encoding(..))
import Node.FS (FS)
import Node.FS.Sync (exists, readTextFile, readdir)
import Reprinting (showAKind)
import Types (Module, Qualified(..))

main :: Eff ( fs :: FS, exception :: EXCEPTION, console :: CONSOLE ) Unit
main = do
  let
    externsFor :: Module -> String
    externsFor m = "output/" <> show m <> "/externs.json"
  dirs <- readdir "output/"
  let modulos = dirs # mapMaybe \m ->
    parseModule (fromArray (fromString <$> split (Pattern ".") m))
  modules <- filterA (exists <<< externsFor) modulos
  logShow modules
  for_ modules \modul -> do
    file <- readTextFile UTF8 $ externsFor modul
    -- logShow file
    let mp = jsonParser file
    -- logShow mp
    for_ (mp <#> externsJustTypes) $ traverse_ $ traverse_ \(Tuple name k) ->
      let q = Qualified modul name
      in log ("Type " <> show q <> " has kind " <> showAKind k)
  pure unit
