module Data.Spliceable where

import Data.Array (take, drop, length) as Array
import Data.Monoid (class Monoid, mempty, (<>))
import Data.Monoid.Additive (Additive(..))
import Data.Newtype (over2, unwrap)
import Data.String (take, drop, length) as String
import Prelude ((-), (<<<), (<@>))

-- | Class for monoids that support slicing operations, i.e. indexing a section
-- | of itself.
-- |
-- | Laws (provisional):
-- |   * Length is a monoid morphism:
-- |     * `length mempty == mempty`
-- |     * `length (a <> b) == length a <> length b`
-- |   * `splice mempty (length s) r s == r`
-- |   * `splice i mempty r s == s`
-- |   * `splice i mempty r s == s`
-- |   * `splice (length s) l r s == s`
class Monoid m <= Spliceable m where
  length :: m -> Additive Int
  splice :: Additive Int -> Additive Int -> m -> m -> m

instance spliceableString :: Spliceable String where
  length = Additive <<< String.length
  splice offset size replacement original =
    let
      before = String.take (unwrap (offset)) original
      after  = String.drop (unwrap (offset <> size)) original
    in before <> replacement <> after

instance spliceableArray :: Spliceable (Array a) where
  length = Additive <<< Array.length
  splice offset size replacement original =
    let
      before = Array.take (unwrap (offset)) original
      after  = Array.drop (unwrap (offset <> size)) original
    in before <> replacement <> after

take :: forall m. Spliceable m => Additive Int -> m -> m
take = splice mempty <@> mempty

drop :: forall m. Spliceable m => Additive Int -> m -> m
drop i s = splice i (over2 Additive (-) (length s) i) mempty s
