module Test.Main where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log)
import Prelude (Unit)
import Types (thisModule, showModuleData)

main :: Eff _ Unit
main = do
  log (showModuleData thisModule)
