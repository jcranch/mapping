{-# LANGUAGE
      CPP,
      DerivingVia
  #-}

module Data.Mapping.MapWithDefault where

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
#else
import Control.Applicative (liftA2)
#endif
import Data.Algebra.Boolean
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import Data.Mapping
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Mapping.Util


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
  mmapInj p (MapWithDefault a f) = MapWithDefault (p a) (fmap p f)
  mtraverse p (MapWithDefault a f) = let
    b = p a
    e x y = if x == y then Nothing else Just y
    g _ x = liftA2 e b (p x)
    in liftA2 MapWithDefault b $ M.traverseMaybeWithKey g f
  mtraverseInj p (MapWithDefault a f) = liftA2 MapWithDefault (p a) (traverse p f)
  act (MapWithDefault a f) x = fromMaybe a (M.lookup x f)
  isConst (MapWithDefault a f) = if M.null f then Just a else Nothing
  mergeA h (MapWithDefault a f) (MapWithDefault b g) = let
    e x y = if x == y then Just x else Nothing
    c = h a b
    l = M.traverseMissing (\_ x -> h x b)
    r = M.traverseMissing (\_ y -> h a y)
    h' _ x y = liftA2 e c $ h x y
    t = M.zipWithMaybeAMatched h'
    combine = M.mergeA l r t
    in liftA2 MapWithDefault c $ combine f g
  merge h (MapWithDefault a f) (MapWithDefault b g) = let
    c = h a b
    l = M.mapMissing (\_ x -> h x b)
    r = M.mapMissing (\_ y -> h a y)
    h' _ x y = let
      z = h x y
      in if z == c then Nothing else Just z
    t = M.zipWithMaybeMatched h'
    combine = M.merge l r t
    in MapWithDefault c $ combine f g

-- | This is one of several possible concepts of neighbours for a
-- `MapWithDefault`. We assume that @k@ is an unbounded and an `Enum`.
--
-- The associated data is the point at which the new value begins, so
-- > foldmapNeighbours (\d x y -> [(d,x,y)]) (fromList "" [(1,"a"),(2,"a"),(4,"b"),(5,"c")])
-- > [(1,"","a"), (3,"a",""), (4,"","b"), (5,"b","c"), (6,"c","")]
--
-- We could get alternative notions if @k@ had bounds, or if it was
-- continuous (like `Float`, for example).
instance (Enum k, Eq k) => Neighbourly (MapWithDefault k) k where
  foldmapNeighbours p  = let
    inner a = let
      free x []        = x
      free x ((r,u):l) = justHad (x <> p r a u) r u l
      justHad x r u []        = x <> p (succ r) u a
      justHad x r u ((s,v):l)
        | succ r /= s         = justHad (x <> p (succ r) u a <> p s a v) s v l
        | u == v              = justHad x s v l
        | otherwise           = justHad (x <> p s u v) s v l
      in free
    go (MapWithDefault a f) = inner a mempty $ M.toList f
    in go


deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Semigroup b) => Semigroup (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Monoid b) => Monoid (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Num b) => Num (MapWithDefault k b)

deriving via (AlgebraWrapper k (MapWithDefault k) b)
  instance (Ord k, Ord b, Boolean b) => Boolean (MapWithDefault k b)
