module Test.Main where

import Control.Comonad.Cofree (head)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log, logShow)
import Prelude (Unit, discard, bind)
import Types (thisModule, showModuleData, cofrecurse, testTypeLS, testTypeC, testTypeLSC, testTypeCS, testPatchSameR, testPatchSameL, testPatchExplodeR, testPatchExplodeL)
import Unsafe.Coerce (unsafeCoerce)

main :: Eff _ Unit
main = do
  log testTypeLS
  logShow (head testTypeC)
  log "----------"
  log testTypeCS
  log "---------- SameR"
  log (cofrecurse testPatchSameR)
  log "---------- SameL"
  log (cofrecurse testPatchSameL)
  log "---------- ExplodeR"
  log (cofrecurse testPatchExplodeR)
  log "---------- ExplodeL"
  log (cofrecurse testPatchExplodeL)
  log "---------- "
  log testTypeLSC
  log (showModuleData thisModule)
