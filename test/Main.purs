module Test.Main where

import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log, logShow)
import Prelude (Unit, discard, bind)
import Types (thisModule, showModuleData, testTypeLS)
import Unsafe.Coerce (unsafeCoerce)

main :: Eff _ Unit
main = do
  log testTypeLS
  log (showModuleData thisModule)
