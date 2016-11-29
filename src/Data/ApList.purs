-- | This module defines an applicative list.
-- |
-- | For the purposes of this module, an applicative list is one where
-- | operations are collected into a list. The results of running the
-- | operations can then be passed as a single argument to a function.
-- |
-- | See [Free Applicative Functors in Haskell](https://www.eyrie.org/~zednenem/2013/05/27/freeapp) (Menendez 2013)
module Data.ApList
  ( ApList(..)
  , ApCons'(..)
  , apNil
  , apCons
  , reduceApList
  , hoistApList
  , traverseApList
  , rebaseApList
  ) where

import Prelude

import Data.Exists (Exists, mkExists, runExists)
import Data.Leibniz (type (~), coerceSymm)
import Data.Tuple (Tuple(..))

import Unsafe.Coerce (unsafeCoerce)

data ApList f a = ApNil (a ~ Unit) | ApCons (Exists (ApCons' f a))

data ApCons' f a u = ApCons' (f a) (ApList f u) (a ~ Tuple a u)

apNil :: forall f. ApList f Unit
apNil = ApNil id

apCons :: forall f a u. f a -> ApList f u -> ApList f (Tuple a u)
apCons a as = ApCons (mkExists apCons')
  where
  apCons' :: ApCons' f (Tuple a u) u
  apCons' = unsafeCoerce (ApCons' a as z)
    where
    z :: a ~ Tuple a u
    z = unsafeCoerce unit

reduceApList :: forall f a. Applicative f => ApList f a -> f a
reduceApList fa =
  case fa of
       ApNil z -> pure (coerceSymm z unit)
       ApCons x -> runExists apCons' x
  where
  apCons' :: forall u. ApCons' f a u -> f a
  apCons' (ApCons' a as z) = coerceSymm z <$> (Tuple <$> a <*> reduceApList as)

hoistApList :: forall f g a. (f ~> g) -> ApList f a -> ApList g a
hoistApList k fa =
  case fa of
       ApNil z -> ApNil z
       ApCons x -> runExists apCons' x
  where
  apCons' :: forall u. ApCons' f a u -> ApList g a
  apCons' (ApCons' a as z) = ApCons (mkExists (ApCons' (k a) (hoistApList k as ) z))

traverseApList :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> ApList f a -> h (ApList g a)
traverseApList k fa =
  case fa of
       ApNil z -> pure (ApNil z)
       ApCons x -> runExists apCons' x
  where
  apCons' :: forall u. ApCons' f a u -> h (ApList g a)
  apCons' (ApCons' a as z) = (\b bs -> ApCons (mkExists (ApCons' b bs z))) <$> k a <*> traverseApList k as

rebaseApList :: forall f u v y z. ApList f u -> (forall x. (x -> y) -> ApList f x -> z) -> (v -> u -> y) -> ApList f v -> z
rebaseApList fa k f =
  case fa of
       ApNil z -> k (_ `f` (coerceSymm z unit))
       ApCons x -> runExists apCons' x
  where
  apCons' :: forall a. ApCons' f u a -> ApList f v -> z
  apCons' (ApCons' x xs z) =
    rebaseApList xs (\g s -> k (\(Tuple a u) -> g u a) (apCons x s))
                    (\v u a -> f v (coerceSymm z (Tuple a u)))
