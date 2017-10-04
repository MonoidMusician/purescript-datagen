module Printing where

import Prelude

import Control.Comonad.Cofree (Cofree, head, tail)
import Data.Functor.Variant as VF
import Data.Newtype (unwrap)
import Data.Pair (Pair(..))
import Data.StrMap (StrMap)
import Data.StrMap (toUnfoldable) as StrMap
import Data.String (Pattern(..), Replacement(..), joinWith, replaceAll)
import Data.Tuple (Tuple(..))
import Types (ATypeVF, _app, _fun, _name, _var)

indent2 :: String -> String
indent2 = replaceAll (Pattern "\n") (Replacement "\n  ")

wrap :: String -> String
wrap a = "(" <> a <> ")"

joinWithIfNE :: forall a. String -> (a -> String) -> Array a -> String
joinWithIfNE _ _ [] = ""
joinWithIfNE sep f as = sep <> joinWith sep (f <$> as)

showFields :: forall a. StrMap (Tuple a String) -> String
showFields m = joinWith ", " $ StrMap.toUnfoldable m <#> \(Tuple k (Tuple _ v)) ->
  k <> " :: " <> v

cofrecurse :: forall a. Show a => Cofree ATypeVF a -> String
cofrecurse v = let t = " >: " <> show (head v) in
  ( VF.case_
  # VF.on _name (unwrap >>> show >>> (_ <> t))
  # VF.on _var (unwrap >>> show >>> (_ <> t))
  # VF.on _fun (\(Pair l r) -> "fun" <> t <>
      indent2 ("\n" <> cofrecurse l <> "\n" <> cofrecurse r))
  # VF.on _app (\(Pair l r) -> "app" <> t <>
      indent2 ("\n" <> cofrecurse l <> "\n" <> cofrecurse r))
  ) (tail v)
