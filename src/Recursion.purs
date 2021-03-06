module Recursion where

import Prelude

import Control.Apply (lift2)
import Control.Comonad.Cofree (Cofree, head, tail, (:<))
import Data.Const (Const(..))
import Data.Functor.Mu (Mu, roll)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Matryoshka (class Corecursive, class Recursive, Algebra, embed, project)
import Type.Proxy (Proxy)
import Unsafe.Coerce (unsafeCoerce)

foreign import data Alg :: Type -> (Type -> Type)
toAlg' :: forall t f. Recursive t f => Corecursive t f => Proxy t -> f ~> Alg t
toAlg' _ = toAlg
toAlg :: forall t f. Recursive t f => Corecursive t f => f ~> Alg t
toAlg = unsafeCoerce
fromAlg :: forall t f. Recursive t f => Corecursive t f => Alg t ~> f
fromAlg = unsafeCoerce

projectAlg :: forall t f. Recursive t f => Corecursive t f => t -> Alg t t
projectAlg = project >>> toAlg

embedAlg :: forall t f. Recursive t f => Corecursive t f => Alg t t -> t
embedAlg = fromAlg >>> embed

forget :: forall f a. Functor f => Cofree f a -> Mu f
forget v = tail v # map forget # roll

rewrap :: forall a b c. Const a b -> Const a c
rewrap (Const a) = Const a

whileAnnotatingDown ::
  forall t f a ann.
    Recursive t f =>
  Maybe ann -> (f t -> f (Tuple ann t)) ->
  (Maybe ann -> Algebra f a) -> t -> a
whileAnnotatingDown ann0 mkAnn f = f ann0 <<< go
  where
    go t = mkAnn (project t) <#>
      \(Tuple ann t') -> f (Just ann) (go t')

modifyHead :: forall f a. (a -> a) -> Cofree f a -> Cofree f a
modifyHead f = lift2 (:<) (f <<< head) tail
