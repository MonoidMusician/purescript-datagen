module Test.Main where

import Control.Comonad.Cofree (head)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log, logShow)
import Prelude (Unit, discard, bind)
import Types (thisModule, showModuleData, testTypeLS, testTypeC, testTypeLSC)
import Unsafe.Coerce (unsafeCoerce)

main :: Eff _ Unit
main = do
  log testTypeLS
  logShow (head testTypeC)
  log testTypeLSC
  log (showModuleData thisModule)
