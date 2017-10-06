module Test.Externs where

import Prelude

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log, logShow)
import Control.Monad.Eff.Exception (EXCEPTION)
import Data.Argonaut (jsonParser)
import Data.Array (filterA, mapMaybe)
import Data.Codec.Argonaut (printJsonDecodeError)
import Data.Either (either)
import Data.Foldable (for_, traverse_)
import Data.Map (toUnfoldable)
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
  let modulos = dirs # mapMaybe parseModule
  modules <- filterA (exists <<< externsFor) modulos
  logShow modules
  for_ modules \modul -> do
    file <- readTextFile UTF8 $ externsFor modul
    -- logShow file
    let mp = jsonParser file
    -- logShow mp
    let asArray = id :: Array ~> Array
    for_ (mp <#> externsJustTypes) $
      either (log <<< printJsonDecodeError) $
        toUnfoldable >>> asArray >>> traverse_ \(Tuple name k) ->
          let q = Qualified modul name
          in log ("Type " <> show q <> " has kind " <> showAKind k)
  pure unit
