-- | This module defines an applicative list.
-- |
-- | For the purposes of this module, an applicative list is one where
-- | operations are collected into a list. The results of running the
-- | operations can then be passed as a single argument to a function.
-- |
-- | See [Free Applicative Functors in Haskell](https://www.eyrie.org/~zednenem/2013/05/27/freeapp) (Menendez 2013)
module Data.ApList
  ( ApList
  , nil
  , cons
  , reduce
  , hoist
  , traverse
  , rebase
  ) where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Leibniz (type (~), coerceSymm)
import Data.Tuple (Tuple(..))

import Unsafe.Coerce (unsafeCoerce)

data ApList f a = Nil (a ~ Unit) | Cons (Exists (Cons' f a))

data Cons' f a u = Cons' (f a) (ApList f u) (a ~ Tuple a u)

nil :: forall f. ApList f Unit
nil = Nil id

cons :: forall f a u. f a -> ApList f u -> ApList f (Tuple a u)
cons a as = Cons (mkExists cons')
  where
  cons' :: Cons' f (Tuple a u) u
  cons' = unsafeCoerce (Cons' a as z)
    where
    z :: a ~ Tuple a u
    z = unsafeCoerce unit

reduce :: forall f a. Applicative f => ApList f a -> f a
reduce fa =
  case fa of
       Nil z -> pure (coerceSymm z unit)
       Cons x -> runExists cons' x
  where
  cons' :: forall u. Cons' f a u -> f a
  cons' (Cons' a as z) = coerceSymm z <$> (Tuple <$> a <*> reduce as)

hoist :: forall f g a. (f ~> g) -> ApList f a -> ApList g a
hoist k fa =
  case fa of
       Nil z -> Nil z
       Cons x -> runExists cons' x
  where
  cons' :: forall u. Cons' f a u -> ApList g a
  cons' (Cons' a as z) = Cons (mkExists (Cons' (k a) (hoist k as ) z))

traverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> ApList f a -> h (ApList g a)
traverse k fa =
  case fa of
       Nil z -> pure (Nil z)
       Cons x -> runExists cons' x
  where
  cons' :: forall u. Cons' f a u -> h (ApList g a)
  cons' (Cons' a as z) = (\b bs -> Cons (mkExists (Cons' b bs z))) <$> k a <*> traverse k as

rebase :: forall f u v w z. ApList f u -> (forall x. (x -> w) -> ApList f x -> z) -> (v -> u -> w) -> ApList f v -> z
rebase fa k f =
  case fa of
       Nil z -> k (_ `f` (coerceSymm z unit))
       Cons x -> runExists cons' x
  where
  cons' :: forall a. Cons' f u a -> ApList f v -> z
  cons' (Cons' x xs z) =
    rebase xs (\g s -> k (\(Tuple a u) -> g u a) (cons x s))
              (\v u a -> f v (coerceSymm z (Tuple a u)))
