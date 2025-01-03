{-# LANGUAGE
      FunctionalDependencies
  #-}

module Data.GenMapping where

import Data.Functor.Identity (Identity(..))


-- | A generalisation of `Mapping`, with operations valued in a monad.
class (Foldable m, Monad s) => GenMapping s k m | m -> k, m -> s where

  -- | Constant functions
  gencst :: v -> s (m v)

  -- | Realise an element of @m v@ as a function @k -> v@.
  genact :: m v -> k -> v

  -- | Is this a constant mapping, and if so what's the value?
  genIsConst :: Ord v => m v -> Maybe v

  -- | Like `fmap`, but unfortunately some instances require an `Ord`
  -- instance on the values.
  genmmap :: Ord v => (u -> v) -> m u -> s (m v)
  genmmap p = fmap runIdentity . genmtraverse (Identity . p)

  -- | Like `fmap`, but circumvents the need for an `Ord` instance on
  -- @v@ by demanding that the function be injective.
  genmmapInj :: (u -> v) -> m u -> s (m v)

  -- | Like `traverse`, but unfortunately some instances require an
  -- `Ord` instance on the values.
  genmtraverse :: (Applicative f, Ord v) => (u -> f v) -> m u -> s (f (m v))

  -- | Like `traverse`, but circumvents the need for an `Ord` instance
  -- on @v@ by demanding that the function be injective.
  genmtraverseInj :: Applicative f => (u -> f v) -> m u -> s (f (m v))

{-
  genmergeA :: (Applicative f, Ord w) => (u -> v -> f w) -> m u -> m v -> f (m w)

  genmerge :: Ord w => (u -> v -> w) -> m u -> m v -> m w
  genmerge p m n = let
    q x y = Identity $ p x y
    in runIdentity $ genmergeA q m n
-}

