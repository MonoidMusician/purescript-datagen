module Data.Bifunctor.Variant
  ( VariantF2
  , inj
  , prj
  , on
  , case_
  , default
  , match
  , expand
  , contract
  , module Exports
  , F2Proxy
  , class VariantF2RecordMatching
  , class VariantF2MatchEachCase
  ) where

import Prelude

import Control.Alternative (class Alternative, empty)
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Symbol (SProxy(..)) as Exports
import Data.Symbol (SProxy, class IsSymbol, reflectSymbol)
import Data.Tuple (Tuple(..), fst)
import Data.Variant.Internal (class Contractable, FProxy(..)) as Exports
import Data.Variant.Internal (class Contractable, RProxy(..), VariantCase, contractWith, unsafeGet)
import Partial.Unsafe (unsafeCrashWith)
import Unsafe.Coerce (unsafeCoerce)
import Type.Row as R

data F2Proxy (f ∷ Type → Type → Type) = F2Proxy

class VariantF2RecordMatching
    (variant ∷ # Type)
    (record ∷ # Type)
    typearg
    typearg1
    result
  | → variant record typearg typearg1 result
instance variantF2RecordMatching
  ∷ ( R.RowToList variant vlist
    , R.RowToList record rlist
    , VariantF2MatchEachCase vlist rlist typearg typearg1 result
    , R.ListToRow vlist variant
    , R.ListToRow rlist record )
  ⇒ VariantF2RecordMatching variant record typearg typearg1 result

-- | Checks that a `RowList` matches the argument to be given to the function
-- | in the other `RowList` with the same label, such that it will produce the
-- | result type.
class VariantF2MatchEachCase
    (vlist ∷ R.RowList)
    (rlist ∷ R.RowList)
    typearg
    typearg1
    result
  | vlist → rlist typearg typearg1 result
  , rlist → vlist typearg typearg1 result
instance variantF2MatchNil
  ∷ VariantF2MatchEachCase R.Nil R.Nil a b res
instance variantF2MatchCons
  ∷ VariantF2MatchEachCase v r a b res
  ⇒ VariantF2MatchEachCase
    (R.Cons sym (F2Proxy f) v)
    (R.Cons sym (f a b → res) r)
    a b res

data F2Box (f ∷ Type → Type → Type) x y =
  F2Box (∀ a b c d. (a → b) → (c → d) → f a c → f b d) (f x y)

instance bifunctorF2Box ∷ Bifunctor (F2Box f) where
  bimap f g (F2Box bimap' a) = F2Box bimap' (bimap' f g a)

data VariantF2 (f ∷ # Type) a b

instance bifunctorVariantF2 ∷ Bifunctor (VariantF2 r) where
  bimap f g a =
    case coerceY a of
      Tuple tag a' → coerceV (Tuple tag (bimap f g a'))
    where
    coerceY ∷ ∀ f a b. VariantF2 r a b → Tuple String (F2Box f a b)
    coerceY = unsafeCoerce

    coerceV ∷ ∀ f a b. Tuple String (F2Box f a b) → VariantF2 r a b
    coerceV = unsafeCoerce

-- | Inject into the variant at a given label.
-- | ```purescript
-- | maybeAtFoo :: forall r. VariantF (foo :: FProxy Maybe | r) Int
-- | maybeAtFoo = inj (SProxy :: SProxy "foo") (Just 42)
-- | ```
inj
  ∷ ∀ sym f a b r1 r2
  . RowCons sym (F2Proxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ Bifunctor f
  ⇒ SProxy sym
  → f a b
  → VariantF2 r2 a b
inj p a = coerceV (Tuple (reflectSymbol p) (F2Box bimap a))
  where
  coerceV ∷ Tuple String (F2Box f a b) → VariantF2 r2 a b
  coerceV = unsafeCoerce

-- | Attempt to read a variant at a given label.
-- | ```purescript
-- | case prj (SProxy :: SProxy "foo") maybeAtFoo of
-- |   Just (Just i) -> i + 1
-- |   _ -> 0
-- | ```
prj
  ∷ ∀ sym f a b r1 r2 g
  . RowCons sym (F2Proxy f) r1 r2
  ⇒ Alternative g
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → VariantF2 r2 a b
  → g (f a b)
prj p = on p pure (const empty)

-- | Attempt to read a variant at a given label by providing branches.
-- | The failure branch receives the provided variant, but with the label
-- | removed.
on
  ∷ ∀ sym f a b c r1 r2
  . RowCons sym (F2Proxy f) r1 r2
  ⇒ IsSymbol sym
  ⇒ SProxy sym
  → (f a b → c)
  → (VariantF2 r1 a b → c)
  → VariantF2 r2 a b
  → c
on p f g r =
  case coerceY r of
    Tuple tag (F2Box _ a) | tag == reflectSymbol p → f a
    _ → g (coerceR r)
  where
  coerceY ∷ VariantF2 r2 a b → Tuple String (F2Box f a b)
  coerceY = unsafeCoerce

  coerceR ∷ VariantF2 r2 a b → VariantF2 r1 a b
  coerceR = unsafeCoerce

-- | Combinator for exhaustive pattern matching.
-- | ```purescript
-- | caseFn :: VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String), baz :: FProxy (Either String)) Int -> String
-- | caseFn = case_
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- |  # on (SProxy :: SProxy "baz") (\baz -> "Baz: " <> either id show baz)
-- | ```
case_ ∷ ∀ a b c. VariantF2 () a b → c
case_ r = unsafeCrashWith case unsafeCoerce r of
  Tuple tag _ → "Data.Functor.Variant: pattern match failure [" <> tag <> "]"

-- | Combinator for partial matching with a default value in case of failure.
-- | ```purescript
-- | caseFn :: forall r. VariantF (foo :: FProxy Maybe, bar :: FProxy (Tuple String) | r) Int -> String
-- | caseFn = default "No match"
-- |  # on (SProxy :: SProxy "foo") (\foo -> "Foo: " <> maybe "nothing" show foo)
-- |  # on (SProxy :: SProxy "bar") (\bar -> "Bar: " <> show (snd bar))
-- | ```
default ∷ ∀ a b c r. c → VariantF2 r a b → c
default c _ = c

-- | Match a `variant` with a `record` containing methods to handle each case
-- | to produce a `result`.
-- |
-- | This means that if `variant` contains a row of type `FProxy f`, a row with
-- | the same label must have type `f a -> result` in `record`, where `result`
-- | is the same type for every row of `record`.
-- |
-- | Polymorphic methods in `record` may create problems with the type system
-- | if the polymorphism is not fully generalized to the whole record type
-- | or if not all polymorphic variables are specified in usage. When in doubt,
-- | label methods with specific types, such as `show :: Int -> String`, or
-- | give the whole record an appropriate type.
match
  ∷ ∀ variant record typearg typearg2 result
  . VariantF2RecordMatching variant record typearg typearg2 result
  ⇒ Record record
  → VariantF2 variant typearg typearg2
  → result
match r v =
  case coerceV v of
    Tuple tag (F2Box _ a) →
      a # unsafeGet tag r
  where
  coerceV ∷ ∀ f. VariantF2 variant typearg typearg2 → Tuple String (F2Box f typearg typearg2)
  coerceV = unsafeCoerce

-- | Every `VariantF lt a` can be cast to some `VariantF gt a` as long as `lt` is a
-- | subset of `gt`.
expand
  ∷ ∀ lt mix gt a b
  . Union lt mix gt
  ⇒ VariantF2 lt a b
  → VariantF2 gt a b
expand = unsafeCoerce

-- | A `VariantF gt a` can be cast to some `VariantF lt a`, where `lt` is is a subset
-- | of `gt`, as long as there is proof that the `VariantF`'s runtime tag is
-- | within the subset of `lt`.
contract
  ∷ ∀ lt gt f a b
  . Alternative f
  ⇒ Contractable gt lt
  ⇒ VariantF2 gt a b
  → f (VariantF2 lt a b)
contract v =
  contractWith
    (RProxy ∷ RProxy gt)
    (RProxy ∷ RProxy lt)
    (fst $ coerceV v)
    (coerceR v)
  where
  coerceV ∷ VariantF2 gt a b → Tuple String VariantCase
  coerceV = unsafeCoerce

  coerceR ∷ VariantF2 gt a b → VariantF2 lt a b
  coerceR = unsafeCoerce
