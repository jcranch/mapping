{-# LANGUAGE
    CPP,
    DeriveFunctor,
    DerivingVia,
    FlexibleInstances,
    FunctionalDependencies,
    QuantifiedConstraints,
    ScopedTypeVariables
  #-}

module Data.Mapping where

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
#else
import Control.Applicative (liftA2)
#endif
import Prelude hiding (not, (&&), (||))
import Data.Algebra.Boolean (Boolean(..))
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Function (on)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Monoid (All(..))
import Data.PartialOrd
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void (Void)


-- | If @Mapping k m@, then @m v@ represents a function @k -> v@.
--
-- `Mapping` requires an instance of `Foldable`, folding over the
-- values that appear. Given that a value can be associated with a
-- very large collection of keys, the only folds that normally make
-- sense are those over idempotent monoids.
class Foldable m => Mapping k m | m -> k where
  cst :: v -> m v

  act :: m v -> k -> v

  isConst :: Ord v => m v -> Maybe v

  mtraverse :: (Applicative f, Ord v) => (u -> f v) -> m u -> f (m v)

  mmap :: Ord v => (u -> v) -> m u -> m v
  mmap p = runIdentity . mtraverse (Identity . p)

  mergeA :: (Applicative f, Ord w) => (u -> v -> f w) -> m u -> m v -> f (m w)

  merge :: Ord w => (u -> v -> w) -> m u -> m v -> m w
  merge p m n = let
    q x y = Identity $ p x y
    in runIdentity $ mergeA q m n


-- | A simultaneous foldMap over two maps
pairMappings :: forall k m u v a. (Mapping k m, Monoid a) => (u -> v -> a) -> m u -> m v -> a
pairMappings p m n = let
  q :: u -> v -> Const a Void
  q x y = Const $ p x y
  in getConst (mergeA q m n)

-- | What values can these two take simultaneously?
mutualValues :: (Ord u, Ord v, Mapping k m) => m u -> m v -> Set (u, v)
mutualValues = pairMappings $ curry S.singleton



-- | A class representing data structures which have a concept of neighbouring
-- values
class Neighbourly m where
  neighbours :: Ord v => m v -> Set (v, v)


-- | A wrapper for representing pointwise algebraic structures on a Mapping
--
-- Eventually would like to use this only for "deriving via"
newtype AlgebraWrapper k m a = AlgebraWrapper { algebraUnwrap :: m a }

instance (Mapping k m, Ord a, Semigroup a) => Semigroup (AlgebraWrapper k m a) where
  (<>) = (AlgebraWrapper .) . merge (<>) `on` algebraUnwrap

instance (Mapping k m, Ord a, Monoid a) => Monoid (AlgebraWrapper k m a) where
  mempty = AlgebraWrapper $ cst mempty

instance (Mapping k m, Ord a, Num a) => Num (AlgebraWrapper k m a) where
  (+) =  (AlgebraWrapper .) . merge (+) `on` algebraUnwrap
  (-) =  (AlgebraWrapper .) . merge (-) `on` algebraUnwrap
  (*) =  (AlgebraWrapper .) . merge (*) `on` algebraUnwrap
  fromInteger = AlgebraWrapper . cst . fromInteger
  abs = AlgebraWrapper . mmap abs . algebraUnwrap
  negate = AlgebraWrapper . mmap negate . algebraUnwrap
  signum = AlgebraWrapper . mmap signum . algebraUnwrap

instance (Mapping k m, Ord a, Boolean a) => Boolean (AlgebraWrapper k m a) where
  true = AlgebraWrapper $ cst true
  false = AlgebraWrapper $ cst false
  not = AlgebraWrapper . mmap not . algebraUnwrap
  (&&) = (AlgebraWrapper .) . merge (&&) `on` algebraUnwrap
  (||) = (AlgebraWrapper .) . merge (||) `on` algebraUnwrap
  xor = (AlgebraWrapper .) . merge xor `on` algebraUnwrap
  (-->) = (AlgebraWrapper .) . merge (-->) `on` algebraUnwrap
  (<-->) = (AlgebraWrapper .) . merge (<-->) `on` algebraUnwrap


-- | Constant functions (on any domain)
newtype Constant k v = Constant { constantValue :: v }

instance Foldable (Constant k) where
  foldMap f (Constant a) = f a

instance Mapping k (Constant k) where
  cst = Constant
  act (Constant x) _ = x
  mmap f (Constant x) = Constant $ f x
  mtraverse f (Constant x) = Constant <$> f x
  isConst (Constant x) = Just x
  merge f (Constant x) (Constant y) = Constant $ f x y
  mergeA f (Constant x) (Constant y) = Constant <$> f x y

instance Neighbourly (Constant k) where
  neighbours = const S.empty

{-
deriving via (AlgebraWrapper k (Constant k) v)
  instance (Ord v, Semigroup v) => Semigroup (Constant k v)

deriving via (AlgebraWrapper k (Constant k) v)
  instance (Ord v, Monoid v) => Monoid (Constant k v)

deriving via (AlgebraWrapper k (Constant k) v)
  instance (Ord v, Num v) => Num (Constant k v)
-}


-- | Binary decisions, as functions defined on Bool
data OnBool a = OnBool {
  onFalse :: a,
  onTrue :: a
} deriving (Eq, Ord, Show, Functor)

instance Foldable OnBool where
  foldMap p (OnBool x y) = p x <> p y

instance FoldableWithIndex Bool OnBool where
  ifoldMap p (OnBool x y) = p False x <> p True y

instance Traversable OnBool where
  traverse f (OnBool x y) = liftA2 OnBool (f x) (f y)

instance Mapping Bool OnBool where
  cst x = OnBool x x
  mmap = fmap
  mtraverse = traverse
  act (OnBool x _) False = x
  act (OnBool _ x) True = x
  isConst (OnBool x y)
    | x == y    = Just x
    | otherwise = Nothing
  mergeA h (OnBool x1 y1) (OnBool x2 y2) = liftA2 OnBool (h x1 x2) (h y1 y2)
  merge h (OnBool x1 y1) (OnBool x2 y2) = OnBool (h x1 x2) (h y1 y2)

instance Neighbourly OnBool where
  neighbours (OnBool x y)
    | x == y    = S.empty
    | otherwise = S.singleton (x, y)

{-
-- May work with a future version of cond
deriving via (AlgebraWrapper Bool OnBool b)
  instance (Ord b, Boolean b) => Boolean (OnBool b)
-}


-- | Maps on Maybe
data OnMaybe k m v = OnMaybe {
  onNothing :: v,
  onJust :: m v
}

instance Foldable m => Foldable (OnMaybe k m) where
  foldMap f (OnMaybe x a) = f x <> foldMap f a

instance FoldableWithIndex k m => FoldableWithIndex (Maybe k) (OnMaybe k m) where
  ifoldMap f (OnMaybe x a) = f Nothing x <> ifoldMap (f . Just) a

instance Mapping k m => Mapping (Maybe k) (OnMaybe k m) where
  cst x = OnMaybe x $ cst x
  mmap p (OnMaybe x a) = OnMaybe (p x) (mmap p a)
  mtraverse p (OnMaybe x a) = liftA2 OnMaybe (p x) (mtraverse p a)
  act (OnMaybe x _) Nothing = x
  act (OnMaybe _ a) (Just y) = act a y
  isConst (OnMaybe x a) = do
    y <- isConst a
    if x == y then Just x else Nothing
  merge h (OnMaybe x a) (OnMaybe y b) = OnMaybe (h x y) (merge h a b)
  mergeA h (OnMaybe x a) (OnMaybe y b) = liftA2 OnMaybe (h x y) (mergeA h a b)


-- | Maps on Either
data OnEither k l m n v = OnEither {
  onLeft :: m v,
  onRight :: n v
} deriving (Eq, Ord)

instance (Foldable m, Foldable n) => Foldable (OnEither k l m n) where
  foldMap p (OnEither f g) = foldMap p f <> foldMap p g

instance (FoldableWithIndex k m, FoldableWithIndex l n) => FoldableWithIndex (Either k l) (OnEither k l m n) where
  ifoldMap p (OnEither f g) = ifoldMap (p . Left) f <> ifoldMap (p . Right) g

instance (Mapping k m,
          Mapping l n)
       => Mapping (Either k l) (OnEither k l m n) where
  cst x = OnEither (cst x) (cst x)
  mmap p (OnEither f g) = OnEither (mmap p f) (mmap p g)
  mtraverse p (OnEither f g) = liftA2 OnEither (mtraverse p f) (mtraverse p g)
  act (OnEither f _) (Left x) = act f x
  act (OnEither _ g) (Right y) = act g y
  isConst (OnEither f g) = do
    x <- isConst f
    y <- isConst g
    if x == y then Just x else Nothing
  mergeA h (OnEither f1 g1) (OnEither f2 g2) = liftA2 OnEither (mergeA h f1 f2) (mergeA h g1 g2)
  merge h (OnEither f1 g1) (OnEither f2 g2) = OnEither (merge h f1 f2) (merge h g1 g2)

{-
-- May work with a future version of cond
deriving via (AlgebraWrapper (Either k l) (OnEither k l m n) b)
  instance (Mapping k m, Mapping l n, Ord b, Boolean b) => Boolean (OnEither k l m n b)
-}


-- | Maps on pairs
newtype OnPair k l m n v = OnPair {
  asComposite :: m (n v)
} deriving (Eq, Ord)

instance (Foldable m, Foldable n) => Foldable (OnPair k l m n) where
  foldMap p (OnPair f) = foldMap (foldMap p) f

instance (Mapping k m,
          Mapping l n,
          forall v. Ord v => Ord (n v))
       => Mapping (k, l) (OnPair k l m n) where
  cst x = OnPair . cst $ cst x
  mmap p (OnPair f) = OnPair (mmap (mmap p) f)
  mtraverse p (OnPair f) = OnPair <$> mtraverse (mtraverse p) f
  act (OnPair f) (x, y) = act (act f x) y
  isConst (OnPair f) = isConst =<< isConst f
  mergeA h (OnPair f) (OnPair g) = OnPair <$> mergeA (mergeA h) f g
  merge h (OnPair f) (OnPair g) = OnPair $ merge (merge h) f g

{-
-- May work with a future version of cond
deriving via (AlgebraWrapper (k, l) (OnPair k l m n) b)
  instance (Mapping k m, Mapping l n, Ord b, Boolean b) => Boolean (OnPair k l m n b)
-}


-- Is the first a subset of the second?
--
-- With a future version of cond, we should be able to generalise this
isSubset :: Mapping k m => m Bool -> m Bool -> Bool
isSubset m n = let
  p True False = All False
  p _ _        = All True
  in getAll $ pairMappings p m n

-- Are the two true on distinct values?
--
-- Again, with a future version of cond, we should be able to generalise this
isDisjoint :: Mapping k m => m Bool -> m Bool -> Bool
isDisjoint m n = let
  p True True = All False
  p _ _       = All True
  in getAll $ pairMappings p m n


-- | A wrapper to allow defining `PartialOrd` instances on mappings whose keys
-- have an `Ord` instance.
newtype OrdWrapper k m v = OrdWrapper {
  getOrdMapping :: m v
}

instance (Mapping k m, Ord v) => PartialOrd (OrdWrapper k m v) where
  compare' (OrdWrapper u) (OrdWrapper v) = pairMappings fromCompare u v


  -- | A wrapper to allow defining `PartialOrd` instances on mappings whose keys
  -- have a `PartialOrd` instance.
newtype PartialOrdWrapper k m v = PartialOrdWrapper {
  getPartialOrdMapping :: m v
}

instance (Mapping k m, PartialOrd v) => PartialOrd (PartialOrdWrapper k m v) where
  compare' (PartialOrdWrapper u) (PartialOrdWrapper v) = pairMappings compare' u v
