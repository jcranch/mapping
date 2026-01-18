{-# LANGUAGE
      DerivingVia
  #-}

module Data.Mapping.MapWithDefault where

import Prelude hiding (Applicative(..), Foldable(..))
import Control.Applicative (Applicative(..))
import Data.Algebra.Boolean
import Data.Foldable (Foldable(..))
import Data.Functor.Const (Const(..))
import Data.List (groupBy)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import Data.Mapping
import Data.Maybe (fromMaybe, mapMaybe)
import qualified Data.Set as S
import Data.Mapping.Util
import Data.Void (Void)


-- | Mappings constant except on an enumerated set of values
data MapWithDefault k v = MapWithDefault {
  common :: v,
  exceptions :: Map k v
} deriving (Eq, Ord)

fromList :: (Ord k, Eq v) => v -> [(k,v)] -> MapWithDefault k v
fromList a = MapWithDefault a . M.fromList . mapMaybe (traverse (nonDefault a))

instance (Show k, Show v) => Show (MapWithDefault k v) where
  showsPrec d (MapWithDefault x l) =
    ("fromList " <>) .
    showsPrec d x .
    showList (M.toList l)

fromListWithKey :: (Ord k, Eq v) => v -> (k -> u -> v -> v) -> [(k, u)] -> MapWithDefault k v
fromListWithKey a f = let
  g m (k, x) = M.alter (nonDefault a . f k x . fromMaybe a) k m
  in MapWithDefault a . foldl' g M.empty

instance Foldable (MapWithDefault k) where
  foldMap p (MapWithDefault a f) = p a <> foldMap p f

instance Ord k => Mapping k (MapWithDefault k) where

  cst x = MapWithDefault x M.empty

  mmap p (MapWithDefault a f) = let
    b = p a
    q x = let
      y = p x
      in if b == y then Nothing else Just y
    in MapWithDefault b $ M.mapMaybe q f

  mtraverse p (MapWithDefault a f) = let
    b = p a
    e x y = if x == y then Nothing else Just y
    g _ x = liftA2 e b (p x)
    in liftA2 MapWithDefault b $ M.traverseMaybeWithKey g f

  act (MapWithDefault a f) x = fromMaybe a (M.lookup x f)

  isConst (MapWithDefault a f) = if M.null f then Just a else Nothing

  mergeA p (MapWithDefault a f) (MapWithDefault b g) = let
    e x y = if x == y then Just x else Nothing
    c = p a b
    p' x y = liftA2 e c $ p x y
    l = M.traverseMaybeMissing (\_ x -> p' x b)
    r = M.traverseMaybeMissing (\_ y -> p' a y)
    t = M.zipWithMaybeAMatched (const p')
    combine = M.mergeA l r t
    in liftA2 MapWithDefault c $ combine f g

  merge p (MapWithDefault a f) (MapWithDefault b g) = let
    c = p a b
    p' x y = let
      z = p x y
      in if z == c then Nothing else Just z
    l = M.mapMaybeMissing (\_ x -> p' x b)
    r = M.mapMaybeMissing (\_ y -> p' a y)
    t = M.zipWithMaybeMatched (const p')
    combine = M.merge l r t
    in MapWithDefault c $ combine f g

  merge3 p (MapWithDefault a f) (MapWithDefault b g) (MapWithDefault c h) = let
    d = p a b c
    l1 = M.mapMissing (const (,b))
    r1 = M.mapMissing (const (a,))
    t1 = M.zipWithMatched (const (,))
    combine1 = M.merge l1 r1 t1
    p' (x,y) z = let
      v = p x y z
      in if v == d then Nothing else Just v
    l2 = M.mapMaybeMissing (\_ (x,y) -> p' (x,y) c)
    r2 = M.mapMaybeMissing (\_ z -> p' (a,b) z)
    t2 = M.zipWithMaybeMatched (const p')
    combine2 = M.merge l2 r2 t2
    in MapWithDefault d $ combine2 (combine1 f g) h

  mergeA3 p (MapWithDefault a f) (MapWithDefault b g) (MapWithDefault c h) = let
    d = p a b c
    e x y
      | x == y    = Nothing
      | otherwise = Just y
    l1 = M.mapMissing (const (,b))
    r1 = M.mapMissing (const (a,))
    t1 = M.zipWithMatched (const (,))
    combine1 = M.merge l1 r1 t1
    p' (x,y) z = liftA2 e d $ p x y z
    l2 = M.traverseMaybeMissing (\_ (x,y) -> p' (x,y) c)
    r2 = M.traverseMaybeMissing (\_ z -> p' (a,b) z)
    t2 = M.zipWithMaybeAMatched (const p')
    combine2 = M.mergeA l2 r2 t2
    in liftA2 MapWithDefault d $ combine2 (combine1 f g) h

  pairMappings :: forall a b m. Monoid m => (a -> b -> m) -> MapWithDefault k a -> MapWithDefault k b -> m
  pairMappings p (MapWithDefault a f) (MapWithDefault b g) = let
    t = M.zipWithAMatched (\_ x y -> Const $ p x y)
    l = M.traverseMissing (\_ x -> Const $ p x b)
    r = M.traverseMissing (\_ y -> Const $ p a y)
    combine = M.mergeA l r t
    in p a b <> getConst (combine f g :: Const m (Map k Void))

  bind f (MapWithDefault a m) = let
    MapWithDefault b n = f a
    g k x
      | y == b    = Nothing
      | otherwise = Just y where
          y = act (f x) k
    h k x _ = g k x
    combine = M.merge (M.mapMaybeMissing g) M.preserveMissing (M.zipWithMaybeMatched h)
    in MapWithDefault b $ combine m n

-- | This instance assumes that k is unbounded
--
-- It would be possible to do something valid in greater generality (for
-- example, a MaybeBounded class), which might be a good idea.
instance (Enum k, Eq k) => Neighbourly (MapWithDefault k) where
  neighbours (MapWithDefault a f) = let
    c (x,_) (y,_) = succ x == y
    d l = zip ([a] <> l) (l <> [a])
    in S.fromList . concatMap (d . fmap snd) . groupBy c $ M.toAscList f

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Semigroup b) => Semigroup (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Monoid b) => Monoid (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Num b) => Num (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Boolean b) => Boolean (MapWithDefault k b)
