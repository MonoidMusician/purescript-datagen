module Main where

import Prelude
import Halogen.Aff as HA
import Component.AST (component)
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE)
import Halogen.VDom.Driver (runUI)

main :: Eff (HA.HalogenEffects (console :: CONSOLE)) Unit
main = HA.runHalogenAff do
  body <- HA.awaitBody
  runUI component unit body
