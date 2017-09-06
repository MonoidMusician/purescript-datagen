module Test.Main where

import Control.Comonad.Cofree (head)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (log, logShow)
import Data.Bitraversable (bitraverse)
import Data.Tuple (snd)
import Prelude (Unit, bind, discard, map, void, (>>>))
import Types (thisModule, showModuleData, cofrecurse, testTypeLS, testTypeC, testTypeLSC, testTypeCS, testPatchSameR, testPatchSameL, testPatchExplodeR, testPatchExplodeL)
import Unsafe.Coerce (unsafeCoerce)

main :: Eff _ Unit
main = do
  let showy = bitraverse logShow (cofrecurse >>> log) >>> void
  log testTypeLS
  logShow (head (snd testTypeC))
  log "----------"
  log testTypeCS
  log "---------- SameR"
  showy testPatchSameR
  log "---------- SameL"
  showy testPatchSameL
  log "---------- ExplodeR"
  showy testPatchExplodeR
  log "---------- ExplodeL"
  showy testPatchExplodeL
  log "---------- "
  log testTypeLSC
  log (showModuleData thisModule)
