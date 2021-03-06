module Test.Externs where

import Prelude

import Effect (Effect)
import Effect.Console (log, logShow)
import Control.Semigroupoid (composeFlipped)
import Data.Argonaut (jsonParser, stringify)
import Data.Array (filterA, mapMaybe)
import Data.Codec.Argonaut (encode, printJsonDecodeError)
import Data.Either (either)
import Data.Map as Map
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..))
import Externs.Codec (externsJustTypes)
import Externs.Codec.Names (parseModule)
import Externs.Codec.TypeData (codecTypeKindData)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (exists, readTextFile, readdir, writeTextFile)
import Reprinting (showAKind)
import Types (Module, Qualified(..))

main :: Effect Unit
main = do
  let
    externsFor :: Module -> String
    externsFor m = "output/" <> show m <> "/externs.json"
  dirs <- readdir "output/"
  let modulos = dirs # mapMaybe parseModule
  modules <- filterA (exists <<< externsFor) modulos
  logShow modules
  allTypes <- Map.unions <<< map Map.fromFoldable <$> for modules \modul -> do
    file <- readTextFile UTF8 $ externsFor modul
    -- logShow file
    let
      mp = jsonParser file
      asArray = identity :: Array ~> Array
      none e = e $> []
      handler = either (none <<< log) $ composeFlipped externsJustTypes $
        either (none <<< log <<< printJsonDecodeError) $
          Map.toUnfoldable >>> asArray >>> traverse \(Tuple name k) ->
            let q = Qualified modul name
            in log ("Type " <> show q <> " has kind " <> showAKind k) $>
                Tuple q k
    -- logShow mp
    handler mp
  writeTextFile UTF8 "docs/types.json" $ stringify $ encode codecTypeKindData allTypes
  pure unit
