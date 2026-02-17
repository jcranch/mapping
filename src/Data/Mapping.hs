{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Mapping where

import Prelude hiding (not, (&&), (||))
import Data.Algebra.Boolean (Boolean(..), AllB(..))
import Data.Bool (bool)
import Data.Constraint.Trivial (Unconstrained)
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Function (on)
import Data.Functor.Const (Const(..))
import Data.Functor.Identity (Identity(..))
import Data.Kind (Constraint, Type)
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
class (Foldable m, forall x. c x => c (m x)) => Mapping (c :: Type -> Constraint) (k :: Type) (m :: Type -> Type) | m -> k, m -> c where

  -- | Form a constant Mapping
  cst :: v -> m v

  -- | Use a Mapping as a function
  act :: m v -> k -> v

  -- | Is the Mapping a constant (and if so with what value)?
  isConst :: c v => m v -> Maybe v

  -- | A constrained Traverse
  mtraverse :: (Applicative f, c v) => (u -> f v) -> m u -> f (m v)

  -- | A constrained Functor
  mmap :: c v => (u -> v) -> m u -> m v
  mmap p = runIdentity . mtraverse (Identity . p)

  -- | Merge two Mappings, valued in an applicative
  mergeA :: (Applicative f, c w) => (u -> v -> f w) -> m u -> m v -> f (m w)

  -- | Merge two Mappings
  merge :: c w => (u -> v -> w) -> m u -> m v -> m w
  merge p m n = let
    q x y = Identity $ p x y
    in runIdentity $ mergeA q m n

  -- | Merge three Mappings
  merge3 :: c x
         => (u -> v -> w -> x)
         -> m u -> m v -> m w -> m x

  -- | Merge three Mappings
  mergeA3 :: (Applicative f, c x)
          => (u -> v -> w -> f x)
          -> m u -> m v -> m w -> f (m x)

  -- | A simultaneous foldMap over two maps; pairMappings is to
  -- foldMap as mmerge is to mmap
  pairMappings :: forall a u v. (Monoid a, c Void) => (u -> v -> a) -> m u -> m v -> a
  pairMappings p m n = let
    q :: u -> v -> Const a Void
    q x y = Const $ p x y
    in getConst (mergeA q m n)

  -- | A monad-like structure
  bind :: (c u, c v, Ord u, c (Either v u)) => (u -> m v) -> m u -> m v
  bind f m = let
    start [] = error "bind: expected some values"
    start [x] = f x
    start (x:xs) = let
      p y z = if y == x then Left z else Right y
      in continue xs $ merge p m (f x)
    continue [] _ = error "bind: expected more values"
    continue [x] n = let
      p (Left z) _ = z
      p (Right _) z = z
      in merge p n (f x)
    continue (x:xs) n = let
      p (Left z) _ = Left z
      p (Right y) z = if y == x then Left z else Right y
      in continue xs $ merge p n (f x)
    in start . S.toList $ values m


-- | This commonly-used function is the reason why we have three-way
-- merges in the typeclass
boolBind :: (Mapping c k m, c v) => m v -> m v -> m Bool -> m v
boolBind = merge3 bool


values :: (Mapping c k m, Ord v) => m v -> Set v
values = foldMap S.singleton


-- | What values can these two take simultaneously?
mutualValues :: (Ord u, Ord v, c Void, Mapping c k m) => m u -> m v -> Set (u, v)
mutualValues = pairMappings $ curry S.singleton


-- | A class representing data structures which have a concept of neighbouring
-- values
class Neighbourly m where
  neighbours :: Ord v => m v -> Set (v, v)


-- | A wrapper for representing pointwise algebraic structures on a Mapping
--
-- Eventually would like to use this only for "deriving via"
newtype AlgebraWrapper (c :: Type -> Constraint) k m a = AlgebraWrapper { algebraUnwrap :: m a }

instance (Mapping c k m, c a, Semigroup a) => Semigroup (AlgebraWrapper c k m a) where
  (<>) = (AlgebraWrapper .) . merge (<>) `on` algebraUnwrap

instance (Mapping c k m, c a, Monoid a) => Monoid (AlgebraWrapper c k m a) where
  mempty = AlgebraWrapper $ cst mempty

instance (Mapping c k m, c a, Num a) => Num (AlgebraWrapper c k m a) where
  (+) =  (AlgebraWrapper .) . merge (+) `on` algebraUnwrap
  (-) =  (AlgebraWrapper .) . merge (-) `on` algebraUnwrap
  (*) =  (AlgebraWrapper .) . merge (*) `on` algebraUnwrap
  fromInteger = AlgebraWrapper . cst . fromInteger
  abs = AlgebraWrapper . mmap abs . algebraUnwrap
  negate = AlgebraWrapper . mmap negate . algebraUnwrap
  signum = AlgebraWrapper . mmap signum . algebraUnwrap

instance (Mapping c k m, c a, Boolean a) => Boolean (AlgebraWrapper c k m a) where
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
  deriving (Eq, Ord)

instance Foldable (Constant k) where
  foldMap f (Constant a) = f a

instance Mapping Unconstrained k (Constant k) where
  cst = Constant
  act (Constant x) _ = x
  isConst (Constant x) = Just x
  mmap f (Constant x) = Constant $ f x
  mtraverse f (Constant x) = Constant <$> f x
  merge f (Constant x) (Constant y) = Constant $ f x y
  merge3 f (Constant x) (Constant y) (Constant z) = Constant $ f x y z
  mergeA f (Constant x) (Constant y) = Constant <$> f x y
  mergeA3 f (Constant x) (Constant y) (Constant z) = Constant <$> f x y z
  pairMappings f (Constant x) (Constant y) = f x y
  bind f (Constant x) = f x

instance Neighbourly (Constant k) where
  neighbours = const S.empty

-- Haven't been able to make deriving via work for this one
instance (Semigroup v) => Semigroup (Constant k v) where
  Constant x <> Constant y = Constant (x <> y)

-- Haven't been able to make deriving via work for this one
instance (Monoid v) => Monoid (Constant k v) where
  mempty = Constant mempty

-- Haven't been able to make deriving via work for this one
instance (Num v) => Num (Constant k v) where
  Constant x + Constant y = Constant (x + y)
  Constant x - Constant y = Constant (x - y)
  Constant x * Constant y = Constant (x * y)
  abs (Constant x) = Constant (abs x)
  negate (Constant x) = Constant (negate x)
  signum (Constant x) = Constant (signum x)
  fromInteger = Constant . fromInteger

-- Haven't been able to make deriving via work for this one
instance (Boolean v) => Boolean (Constant k v) where
  false = Constant false
  true = Constant true
  not (Constant x) = Constant (not x)
  Constant x && Constant y = Constant (x && y)
  Constant x || Constant y = Constant (x || y)
  xor (Constant x) (Constant y) = Constant (xor x y)
  Constant x <--> Constant y = Constant (x <--> y)
  Constant x --> Constant y = Constant (x --> y)



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

instance Mapping Eq Bool OnBool where
  cst x = OnBool x x
  act (OnBool x _) False = x
  act (OnBool _ x) True = x
  isConst (OnBool x y)
    | x == y    = Just x
    | otherwise = Nothing
  mmap = fmap
  mtraverse = traverse
  mergeA h (OnBool x1 y1) (OnBool x2 y2) =
    liftA2 OnBool (h x1 x2) (h y1 y2)
  merge h (OnBool x1 y1) (OnBool x2 y2) =
    OnBool (h x1 x2) (h y1 y2)
  mergeA3 h (OnBool x1 y1) (OnBool x2 y2) (OnBool x3 y3) =
    liftA2 OnBool (h x1 x2 x3) (h y1 y2 y3)
  merge3 h (OnBool x1 y1) (OnBool x2 y2) (OnBool x3 y3) =
    OnBool (h x1 x2 x3) (h y1 y2 y3)
  pairMappings p (OnBool x1 y1) (OnBool x2 y2) = p x1 x2 <> p y1 y2
  bind f (OnBool u v) = OnBool (onFalse (f u)) (onTrue (f v))

instance Neighbourly OnBool where
  neighbours (OnBool x y)
    | x == y    = S.empty
    | otherwise = S.singleton (x, y)

deriving via (AlgebraWrapper Eq Bool OnBool a)
  instance (Eq a, Semigroup a) => Semigroup (OnBool a)

deriving via (AlgebraWrapper Eq Bool OnBool a)
  instance (Eq a, Monoid a) => Monoid (OnBool a)

deriving via (AlgebraWrapper Eq Bool OnBool a)
  instance (Eq a, Num a) => Num (OnBool a)

deriving via (AlgebraWrapper Eq Bool OnBool b)
  instance (Eq b, Boolean b) => Boolean (OnBool b)


-- | Maps on Maybe
data OnMaybe c k m v = OnMaybe {
  onNothing :: v,
  onJust :: m v
} deriving (Eq, Ord)

instance Foldable m => Foldable (OnMaybe c k m) where
  foldMap f (OnMaybe x a) = f x <> foldMap f a

instance FoldableWithIndex k m => FoldableWithIndex (Maybe k) (OnMaybe c k m) where
  ifoldMap f (OnMaybe x a) = f Nothing x <> ifoldMap (f . Just) a

instance (forall x. c x => Eq x, forall x. c x => c (OnMaybe c k m x), Mapping c k m) => Mapping c (Maybe k) (OnMaybe c k m) where
  cst x = OnMaybe x $ cst x
  mmap p (OnMaybe x a) = OnMaybe (p x) (mmap p a)
  mtraverse p (OnMaybe x a) = liftA2 OnMaybe (p x) (mtraverse p a)
  act (OnMaybe x _) Nothing = x
  act (OnMaybe _ a) (Just y) = act a y
  isConst (OnMaybe x a) = do
    y <- isConst a
    if x == y then Just x else Nothing
  merge h (OnMaybe x a) (OnMaybe y b) =
    OnMaybe (h x y) (merge h a b)
  mergeA h (OnMaybe x a) (OnMaybe y b) =
    liftA2 OnMaybe (h x y) (mergeA h a b)
  merge3 h (OnMaybe x a) (OnMaybe y b) (OnMaybe z c) =
    OnMaybe (h x y z) (merge3 h a b c)
  mergeA3 h (OnMaybe x a) (OnMaybe y b) (OnMaybe z c) =
    liftA2 OnMaybe (h x y z) (mergeA3 h a b c)
  pairMappings p (OnMaybe x a) (OnMaybe y b) = p x y <> pairMappings p a b
  bind f (OnMaybe x m) = OnMaybe (onNothing (f x)) (bind (onJust . f) m)

deriving via (AlgebraWrapper c (Maybe k) (OnMaybe c k m) a)
  instance (forall x. c x => Eq x, forall x. c x => c (OnMaybe c k m x), Mapping c k m, c a, Semigroup a) => Semigroup (OnMaybe c k m a)

deriving via (AlgebraWrapper c (Maybe k) (OnMaybe c k m) a)
  instance (forall x. c x => Eq x, forall x. c x => c (OnMaybe c k m x), Mapping c k m, c a, Monoid a) => Monoid (OnMaybe c k m a)

deriving via (AlgebraWrapper c (Maybe k) (OnMaybe c k m) a)
  instance (forall x. c x => Eq x, forall x. c x => c (OnMaybe c k m x), Mapping c k m, c a, Num a) => Num (OnMaybe c k m a)

deriving via (AlgebraWrapper c (Maybe k) (OnMaybe c k m) a)
  instance (forall x. c x => Eq x, forall x. c x => c (OnMaybe c k m x), Mapping c k m, c a, Boolean a) => Boolean (OnMaybe c k m a)


-- | Maps on Either
data OnEither (c :: Type -> Constraint) (k :: Type) (l :: Type) (m :: Type -> Type) (n :: Type -> Type) (v :: Type) = OnEither {
  onLeft :: m v,
  onRight :: n v
} deriving (Eq, Ord)

instance (Foldable m, Foldable n) => Foldable (OnEither c k l m n) where
  foldMap p (OnEither f g) = foldMap p f <> foldMap p g

instance (FoldableWithIndex k m, FoldableWithIndex l n)
    => FoldableWithIndex (Either k l) (OnEither c k l m n) where
  ifoldMap p (OnEither f g) = ifoldMap (p . Left) f <> ifoldMap (p . Right) g

instance (Mapping c k m,
          Mapping c l n,
          forall x. c x => Eq x,
          forall x. c x => c (OnEither c k l m n x))
       => Mapping c (Either k l) (OnEither c k l m n) where
  cst x = OnEither (cst x) (cst x)
  mmap p (OnEither f g) = OnEither (mmap p f) (mmap p g)
  mtraverse p (OnEither f g) = liftA2 OnEither (mtraverse p f) (mtraverse p g)
  act (OnEither f _) (Left x) = act f x
  act (OnEither _ g) (Right y) = act g y
  isConst (OnEither f g) = do
    x <- isConst f
    y <- isConst g
    if x == y then Just x else Nothing
  mergeA h (OnEither f1 g1) (OnEither f2 g2) =
    liftA2 OnEither (mergeA h f1 f2) (mergeA h g1 g2)
  merge h (OnEither f1 g1) (OnEither f2 g2) =
    OnEither (merge h f1 f2) (merge h g1 g2)
  mergeA3 p (OnEither f1 g1) (OnEither f2 g2) (OnEither f3 g3) =
    liftA2 OnEither (mergeA3 p f1 f2 f3) (mergeA3 p g1 g2 g3)
  merge3 p (OnEither f1 g1) (OnEither f2 g2) (OnEither f3 g3) =
    OnEither (merge3 p f1 f2 f3) (merge3 p g1 g2 g3)
  pairMappings p (OnEither f1 g1) (OnEither f2 g2) = pairMappings p f1 f2 <> pairMappings p g1 g2
  bind f (OnEither u v) = OnEither (bind (onLeft . f) u) (bind (onRight . f) v)

deriving via (AlgebraWrapper c (Either k l) (OnEither c k l (m :: Type -> Type) n) a)
  instance (Mapping c k m,
            Mapping c l n,
            c a,
            forall x. c x => Eq x,
            forall x. c x => c (OnEither c k l m n x),
            Semigroup a) => Semigroup (OnEither c k l m n a)

deriving via (AlgebraWrapper c (Either k l) (OnEither c k l (m :: Type -> Type) n) a)
  instance (Mapping c k m,
            Mapping c l n,
            c a,
            forall x. c x => Eq x,
            forall x. c x => c (OnEither c k l m n x),
            Monoid a) => Monoid (OnEither c k l m n a)

deriving via (AlgebraWrapper c (Either k l) (OnEither c k l (m :: Type -> Type) n) a)
  instance (Mapping c k m,
            Mapping c l n,
            c a,
            forall x. c x => Eq x,
            forall x. c x => c (OnEither c k l m n x),
            Num a) => Num (OnEither c k l m n a)

deriving via (AlgebraWrapper c (Either k l) (OnEither c k l (m :: Type -> Type) n) a)
  instance (Mapping c k m,
            Mapping c l n,
            c a,
            forall x. c x => Eq x,
            forall x. c x => c (OnEither c k l m n x),
            Boolean a) => Boolean (OnEither c k l m n a)


newtype Reconstrained (c :: Type -> Constraint) (d :: Type -> Constraint) (k :: Type) (m :: Type -> Type) (a :: Type) = Reconstrained {
  preconstrained :: m a
} deriving (Eq, Ord, Foldable, FoldableWithIndex k, Neighbourly)

instance (forall x. d x => c x, forall x. d x => d (Reconstrained c d k m x), Mapping c k m) => Mapping d k (Reconstrained c d k m) where
  cst = Reconstrained . cst
  act = act . preconstrained
  isConst = isConst . preconstrained
  mtraverse f = fmap Reconstrained . mtraverse f . preconstrained
  mmap f = Reconstrained . mmap f . preconstrained
  mergeA p (Reconstrained m) (Reconstrained n) = Reconstrained <$> mergeA p m n
  merge p (Reconstrained m) (Reconstrained n) = Reconstrained $ merge p m n
  mergeA3 p (Reconstrained m) (Reconstrained n) (Reconstrained o) = Reconstrained <$> mergeA3 p m n o
  merge3 p (Reconstrained m) (Reconstrained n) (Reconstrained o) = Reconstrained $ merge3 p m n o


-- | Maps on pairs
newtype OnPair c k l m n v = OnPair {
  asComposite :: m (n v)
} deriving (Eq, Ord)

instance (Foldable m, Foldable n) => Foldable (OnPair c k l m n) where
  foldMap p (OnPair f) = foldMap (foldMap p) f

instance (FoldableWithIndex k m, FoldableWithIndex l n) => FoldableWithIndex (k,l) (OnPair c k l m n) where
  ifoldMap p (OnPair f) = let
    h x = ifoldMap (p . (x,))
    in ifoldMap h f

instance (Mapping c k m,
          Mapping c l n,
          forall x. c x => c (OnPair c k l m n x))
       => Mapping c (k, l) (OnPair c k l m n) where
  cst x = OnPair . cst $ cst x
  mmap p (OnPair f) = OnPair (mmap (mmap p) f)
  mtraverse p (OnPair f) = OnPair <$> mtraverse (mtraverse p) f
  act (OnPair f) (x, y) = act (act f x) y
  isConst (OnPair f) = isConst =<< isConst f
  mergeA h (OnPair f) (OnPair g) = OnPair <$> mergeA (mergeA h) f g
  merge h (OnPair f) (OnPair g) = OnPair $ merge (merge h) f g
  merge3 p (OnPair f) (OnPair g) (OnPair h) = OnPair $ merge3 (merge3 p) f g h
  mergeA3 p (OnPair f) (OnPair g) (OnPair h) = OnPair <$> mergeA3 (mergeA3 p) f g h
  pairMappings p (OnPair f) (OnPair g) = pairMappings (pairMappings p) f g

deriving via (AlgebraWrapper (c :: Type -> Constraint) (k, l) (OnPair c k l (m :: Type -> Type) (n :: Type -> Type)) a)
  instance (Mapping c k m, Mapping c l n,
          forall x. c x => c (OnPair c k l m n x), c a, Semigroup a) => Semigroup (OnPair c k l m n a)

deriving via (AlgebraWrapper (c :: Type -> Constraint) (k, l) (OnPair c k l (m :: Type -> Type) (n :: Type -> Type)) a)
  instance (Mapping c k m, Mapping c l n,
          forall x. c x => c (OnPair c k l m n x), c a, Monoid a) => Monoid (OnPair c k l m n a)

deriving via (AlgebraWrapper (c :: Type -> Constraint) (k, l) (OnPair c k l (m :: Type -> Type) (n :: Type -> Type)) a)
  instance (Mapping c k m, Mapping c l n,
          forall x. c x => c (OnPair c k l m n x), c a, Num a) => Num (OnPair c k l m n a)

deriving via (AlgebraWrapper (c :: Type -> Constraint) (k, l) (OnPair c k l (m :: Type -> Type) (n :: Type -> Type)) b)
  instance (Mapping c k m, Mapping c l n,
          forall x. c x => c (OnPair c k l m n x), c b, Boolean b) => Boolean (OnPair c k l m n b)


-- | Is the first a subset of the second?
isSubset :: (Boolean b, c Void, Mapping c k m) => m b -> m b -> b
isSubset m n = let
  p x y = AllB (x --> y)
  in getAllB $ pairMappings p m n

-- | Are the two true on distinct values?
isDisjoint :: (Boolean b, c Void, Mapping c k m) => m b -> m b -> b
isDisjoint m n = let
  p x y = AllB (not (x && y))
  in getAllB $ pairMappings p m n


-- | A wrapper to allow defining `PartialOrd` instances on mappings whose keys
-- have an `Ord` instance.
newtype OrdWrapper c k m v = OrdWrapper {
  getOrdMapping :: m v
}

instance (Mapping c k m, c Void, Ord v) => PartialOrd (OrdWrapper c k m v) where
  compare' (OrdWrapper u) (OrdWrapper v) = pairMappings fromCompare u v


  -- | A wrapper to allow defining `PartialOrd` instances on mappings whose keys
  -- have a `PartialOrd` instance.
newtype PartialOrdWrapper c k m v = PartialOrdWrapper {
  getPartialOrdMapping :: m v
}

instance (Mapping c k m, c Void, PartialOrd v) => PartialOrd (PartialOrdWrapper c k m v) where
  compare' (PartialOrdWrapper u) (PartialOrdWrapper v) = pairMappings compare' u v
