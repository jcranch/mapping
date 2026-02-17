{-# LANGUAGE CPP #-}
{-# LANGUAGE DerivingVia #-}

module Data.Mapping.Piecewise where

import Data.Algebra.Boolean
import Data.Foldable (toList)
import qualified Data.Map.Internal as MI
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Mapping


-- | A data structure storing mappings that are constant on
-- intervals.
--
-- If the space of keys not discrete, then these mappings are
-- right-continuous: values are in general defined on intervals $a
-- \leq x < b$ which are closed on the left and open on the right.
data Piecewise k v = Piecewise {
  -- | The value taken for sufficiently small keys
  leftEnd :: v,
  starts :: Map k v
} deriving (Eq, Ord)

-- | The value taken for sufficiently large keys
rightEnd :: Piecewise k v -> v
rightEnd (Piecewise a m) = case M.lookupMax m of
  Nothing    -> a
  Just (_,b) -> b

-- | Assumes the keys are distinct and increasing (but consecutive
-- values may be the same, in which case the intervening keys are
-- removed)
fromAscList :: (Eq v) => v -> [(k,v)] -> Piecewise k v
fromAscList = let
  inner _ [] = []
  inner a ((y,b):r)
    | a == b    = inner a r
    | otherwise = (y,b):inner b r
  run x = Piecewise x . M.fromDistinctAscList . inner x
  in run

instance (Show k, Show v) => Show (Piecewise k v) where
  showsPrec d (Piecewise k m) =
    ("fromAscList " <>) .
    showsPrec d k .
    (" " <>) .
    showList (M.toList m)

-- | Assumes that the keys are distinct and increasing, and also that
-- consecutive values are distinct
fromAscListUnsafe :: v -> [(k,v)] -> Piecewise k v
fromAscListUnsafe k = Piecewise k . M.fromDistinctAscList

-- | Takes value `a` for keys less than `x` and `b` otherwise
changeAt :: v -> k -> v -> Piecewise k v
changeAt a x b = Piecewise a $ M.singleton x b

-- | Is the value greater than or equal to `k`?
greaterThanOrEqual :: k -> Piecewise k Bool
greaterThanOrEqual k = changeAt False k True

-- | Is the value less than `k`?
lessThan :: k -> Piecewise k Bool
lessThan k = changeAt True k False

-- | Is the value greater than `k`? This is subject to the usual
-- concerns about `Enum` (it not to be used with floating-point
-- arithmetic, for example)
greaterThan :: Enum k => k -> Piecewise k Bool
greaterThan = greaterThanOrEqual . succ

-- | Is the value less than or equal to `k`? This is subject to the
-- usual concerns about `Enum` (it not to be used with floating-point
-- arithmetic, for example)
lessThanOrEqual :: Enum k => k -> Piecewise k Bool
lessThanOrEqual = lessThan . succ

instance (Eq k) => Functor (Piecewise k) where
  fmap p (Piecewise a f) = fromAscListUnsafe (p a) (fmap p <$> M.toList f)

instance Foldable (Piecewise k) where
  foldMap f (Piecewise a m) = f a <> foldMap f m


innerMerge :: Ord k => (x -> y -> z) -> x -> y -> [(k,x)] -> [(k,y)] -> [(k,z)]
innerMerge p = let
  go x _ [] v = fmap (p x) <$> v
  go _ y u [] = fmap (flip p y) <$> u
  go x y u@((a,x'):u') v@((b,y'):v') = case compare a b of
    LT -> (a,p x' y):go x' y u' v
    GT -> (b,p x y'):go x y' u v'
    EQ -> (a,p x' y'):go x' y' u' v'
  in go


innerMergeA :: (Ord k, Applicative f)
            => (x -> y -> f z)
            -> x -> y
            -> [(k,x)] -> [(k,y)] -> f [(k,z)]
innerMergeA p = let
  go x _ [] v = traverse (traverse (p x)) v
  go _ y u [] = traverse (traverse (flip p y)) u
  go x y u@((a,x'):u') v@((b,y'):v') = case compare a b of
    LT -> liftA2 (:) ((a,) <$> p x' y) (go x' y u' v)
    GT -> liftA2 (:) ((b,) <$> p x y') (go x y' u v')
    EQ -> liftA2 (:) ((a,) <$> p x' y') (go x' y' u' v')
  in go


innerMerge3 :: Ord k
            => (x -> y -> z -> w)
            -> x -> y -> z
            -> [(k,x)] -> [(k,y)] -> [(k,z)] -> [(k,w)]
innerMerge3 p = let
  go x y z [] v w = innerMerge (p x) y z v w
  go x y z u [] w = innerMerge (\i -> p i y) x z u w
  go x y z u v [] = innerMerge (\i j -> p i j z) x y u v
  go x y z u@((a,x'):u') v@((b,y'):v') w@((c,z'):w') = case compare a b of
    LT -> case compare a c of
      LT -> (a,p x' y z):go x' y z u' v w
      GT -> (c,p x y z'):go x y z' u v w'
      EQ -> (a,p x' y z'):go x' y z' u' v w'
    GT -> case compare b c of
      LT -> (b,p x y' z):go x y' z u v' w
      GT -> (c,p x y z'):go x y z' u v w'
      EQ -> (b,p x y' z'):go x y' z' u v' w'
    EQ -> case compare a c of
      LT -> (a,p x' y' z):go x' y' z u' v' w
      GT -> (c,p x y z'):go x y z' u v w'
      EQ -> (a,p x' y' z'):go x' y' z' u' v' w'
  in go


innerMergeA3 :: (Applicative f, Ord k)
             => (x -> y -> z -> f w)
             -> x -> y -> z
             -> [(k,x)] -> [(k,y)] -> [(k,z)] -> f [(k,w)]
innerMergeA3 p = let
  go x y z [] v w = innerMergeA (p x) y z v w
  go x y z u [] w = innerMergeA (\i -> p i y) x z u w
  go x y z u v [] = innerMergeA (\i j -> p i j z) x y u v
  go x y z u@((a,x'):u') v@((b,y'):v') w@((c,z'):w') = case compare a b of
    LT -> case compare a c of
      LT -> liftA2 (:) ((a,) <$> p x' y z) (go x' y z u' v w)
      GT -> liftA2 (:) ((c,) <$> p x y z') (go x y z' u v w')
      EQ -> liftA2 (:) ((a,) <$> p x' y z') (go x' y z' u' v w')
    GT -> case compare b c of
      LT -> liftA2 (:) ((b,) <$> p x y' z) (go x y' z u v' w)
      GT -> liftA2 (:) ((c,) <$> p x y z') (go x y z' u v w')
      EQ -> liftA2 (:) ((b,) <$> p x y' z') (go x y' z' u v' w')
    EQ -> case compare a c of
      LT -> liftA2 (:) ((a,) <$> p x' y' z) (go x' y' z u' v' w)
      GT -> liftA2 (:) ((c,) <$> p x y z') (go x y z' u v w')
      EQ -> liftA2 (:) ((a,) <$> p x' y' z') (go x' y' z' u' v' w')
  in go


instance Ord k => Mapping Eq k (Piecewise k) where

  cst x = Piecewise x M.empty

  act (Piecewise a f) x = case M.lookupLE x f of
    Nothing -> a
    Just (_,b) -> b

  isConst (Piecewise a f) = if M.null f then Just a else Nothing

  mmap p (Piecewise a f) = fromAscList (p a) . fmap (fmap p) $ M.toList f

  mtraverse p (Piecewise a f) = liftA2 fromAscList (p a) . traverse (traverse p) $ M.toList f

  merge p (Piecewise a f) (Piecewise b g) =
    fromAscList (p a b) $ innerMerge p a b (M.toList f) (M.toList g)

  mergeA p (Piecewise a f) (Piecewise b g) =
    liftA2 fromAscList (p a b) $ innerMergeA p a b (M.toList f) (M.toList g)

  merge3 p (Piecewise a f) (Piecewise b g) (Piecewise c h) =
    fromAscList (p a b c) $ innerMerge3 p a b c (M.toList f) (M.toList g) (M.toList h)

  mergeA3 p (Piecewise a f) (Piecewise b g) (Piecewise c h) =
    liftA2 fromAscList (p a b c) $ innerMergeA3 p a b c (M.toList f) (M.toList g) (M.toList h)

  pairMappings p = let

    inner z a b r@((x,a'):r') s@((y,b'):s') = case compare x y of
      LT -> inner (z <> p a' b) a' b r' s
      GT -> inner (z <> p a b') a b' r s'
      EQ -> inner (z <> p a' b') a' b' r' s'
    inner z a _ [] s = z <> foldMap (p a . snd) s
    inner z _ b r [] = z <> foldMap (flip p b . snd) r

    run (Piecewise a f) (Piecewise b g) = inner (p a b) a b (M.toList f) (M.toList g)

    in run

  bind f (Piecewise a m) = let
    inner p []        = p
    inner p ((k,q):l) = let
      (p',  _) = splitPiecewise k p
      (_ , q') = splitPiecewise k q
      in gluePiecewise p' k $ inner q' l
    in inner (f a) (fmap f <$> M.toList m)

instance Neighbourly (Piecewise k) where
  neighbours m = let
    pairs (x:r@(y:_)) = (x,y):pairs r
    pairs _           = []
    in S.fromList . pairs $ toList m

deriving via (AlgebraWrapper Eq k (Piecewise k) b)
  instance (Ord k, Ord b, Semigroup b) => Semigroup (Piecewise k b)

deriving via (AlgebraWrapper Eq k (Piecewise k) b)
  instance (Ord k, Ord b, Monoid b) => Monoid (Piecewise k b)

deriving via (AlgebraWrapper Eq k (Piecewise k) b)
  instance (Ord k, Ord b, Num b) => Num (Piecewise k b)

deriving via (AlgebraWrapper Eq k (Piecewise k) b)
  instance (Ord k, Ord b, Boolean b) => Boolean (Piecewise k b)

-- | Alter keys according to a function, assumed to be monotone (not checked)
mapKeysMonotonic :: (k -> l) -> Piecewise k v -> Piecewise l v
mapKeysMonotonic f (Piecewise a m) = Piecewise a (M.mapKeysMonotonic f m)

-- | Alter keys according to a function, assumed to be antitone (not checked)
mapKeysAntitonic :: (k -> l) -> Piecewise k v -> Piecewise l v
mapKeysAntitonic f = let

  inner a MI.Tip = (a, MI.Tip)
  inner a (MI.Bin s x b l r) = let
    (a', l') = inner a l
    (b', r') = inner b r
    in (b', MI.Bin s (f x) a' r' l')

  start (Piecewise a m) = uncurry Piecewise $ inner a m
  in start

-- | Split in two: one which assumes keys are less than `k`, and one
-- which assumes them greater than or equal to `k`.
splitPiecewise :: Ord k => k -> Piecewise k v -> (Piecewise k v, Piecewise k v)
splitPiecewise k (Piecewise a m) = case M.splitLookup k m of
  (m1, Just b, m2) -> (Piecewise a m1, Piecewise b m2)
  (m1, Nothing, m2) -> let
    p1 = Piecewise a m1
    in (p1, Piecewise (rightEnd p1) m2)

-- | Assemble two maps; it is assumed that all keys in the left-hand
-- map are less than `k` and all keys in the right-hand map are
-- greater than or equal to `k` (which is not checked).
gluePiecewise :: (Eq v) => Piecewise k v -> k -> Piecewise k v -> Piecewise k v
gluePiecewise p@(Piecewise a m) k (Piecewise c n) = let
  b = rightEnd p
  in Piecewise a (if b == c then MI.link2 m n else MI.link k c m n)
