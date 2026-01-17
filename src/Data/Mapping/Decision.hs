{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Decision diagrams, parametric in the mapping type for the decisions.
--
-- This is inspired by binary decision diagrams (as described in detail in
-- Knuth's The Art of Computer Programming, volume 4A); these are the specific
-- case where m is `BoolMapping` and v is `Bool`. Our algorithms are mostly
-- straightforward generalisations of those considered there.
--
-- Four layers of functions:
--
-- 1. Pure memoisation functions
-- 2. Specialisations to Nodes
-- 3. Cache-manipulating versions of standard functions
-- 4. The functionality of Decision

-- TODO
--  * Could optimise bind a bit, sharing base
--  * Format types of functions better
--  * Lint and check for long lines
--  * Increase test coverage
--  * Examples:
--     - finding optima
--     - finding random elements
--    (as examples of the more general functions, already coded, I hope)
--  * Documentation!!!
--
-- MAYBE TO DO
--  * Optimisation by reordering
module Data.Mapping.Decision where

import Control.Monad ((<=<))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (State, StateT, evalState, evalStateT, execState, get, modify, state)
import Data.Algebra.Boolean (Boolean(..))
import Data.Foldable (traverse_)
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import qualified Data.IntMap.Strict as IM
import Data.Monoid (All(..), Ap(..), Sum(..))
import qualified Data.Set as S
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M

import Data.Mapping


data Serial a = Serial {
  serial :: Int,
  content :: a
}

instance Eq (Serial a) where
  Serial i _ == Serial j _ = i == j


-- | A general-purpose monadic memoising function, which caches
-- partial results in an IntMap
memoComputeM :: Monad m
             => (a -> Int)
             -> (forall s. (a -> StateT s m b) -> a -> StateT s m b)
             -> a
             -> m b
memoComputeM s r = let

  go x = let
    i = s x
    inner m = case IM.lookup i m of
      Just y -> pure y
      Nothing -> do
        y <- r go x
        modify (IM.insert i y)
        pure y
    in inner =<< get

  in flip evalStateT IM.empty . go

-- | A slightly-less general-purpose memoising function, caching
-- partial results in an IntMap.
memoCompute :: (a -> Int)
            -> (forall s. (a -> State s b) -> a -> State s b)
            -> a
            -> b
memoCompute s r = runIdentity . memoComputeM s r


-- | Rapid comparison, but it's meaningless: the order depends on the
-- order of discovery
instance Ord (Serial a) where
  compare (Serial i _) (Serial j _) = compare i j

data Node k m a v = Leaf v | Branch a (m (Serial (Node k m a v)))

deriving instance (Eq (m (Serial (Node k m a v))), Eq a, Eq v) => Eq (Node k m a v)

deriving instance (Ord (m (Serial (Node k m a v))), Ord a, Ord v) => Ord (Node k m a v)

newtype Cache a = Cache (Map a (Serial a))

stash :: Ord a => a -> State (Cache a) (Serial a)
stash x = let
  f (Cache m) = let
    g Nothing = let
      s = Serial (M.size m) x
      in (s, Just s)
    g (Just s) = (s, Just s)
    in Cache <$> M.alterF g x m
  in state f

makeLeaf :: (forall x. Ord x => Ord (m x), Ord a, Ord v) => v -> State (Cache (Node k m a v)) (Serial (Node k m a v))
makeLeaf = stash . Leaf

makeBranch :: (Mapping k m, Ord a, Ord v) => a -> m (Serial (Node k m a v)) -> State (Cache (Node k m a v)) (Serial (Node k m a v))
makeBranch a n = case isConst n of
  Just s -> pure s
  Nothing -> stash (Branch a n)

-- |
--
-- Notes:
--
-- 1. The FoldableWithIndex instance can produce very large outputs
-- even with a modest-sized decision diagram.
--
-- 2. The traverse and mergeA methods are very inefficient, and can
-- visit notes an exponential number of times (see documentation for
-- `traverseS`), but the mmap, foldMap and merge methods visit each
-- node only once.
--
-- 3. If you know two Decisions have been built from the same cache,
-- then comparing the serial numbers of their start node is a better
-- equality test than the more generic one provided.
newtype Decision k m a v = Decision {
  startDecision :: Serial (Node k m a v)
}


-- | a Serial-specialised memoCompute
recurseMap :: (v -> x)
           -> (forall z s. (z -> State s x) -> a -> m z -> State s x)
           -> Serial (Node k m a v)
           -> x
recurseMap p q = let
  r f s = case content s of
    Leaf v -> pure (p v)
    Branch a m -> q f a m
  in memoCompute serial r

-- | a Serial-specialised memoComputeM
recurseMapM :: Monad n
            => (v -> n x)
            -> (forall z s. (z -> StateT s n x) -> a -> m z -> StateT s n x)
            -> Serial (Node k m a v)
            -> n x
recurseMapM p q = let
  r f s = case content s of
    Leaf v -> lift (p v)
    Branch a m -> q f a m
  in memoComputeM serial r


-- | A function Int -> Int -> Int which is injective on pairs of
-- nonnegative integers
pairIntegers :: Int -> Int -> Int
pairIntegers i j = (((i+j)*(i+j+1)) `div` 2) + j


instance (Mapping k m, Ord a, Eq v) => Eq (Decision k m a v) where
  a == b = getAll $ pairMappings (\x y -> All (x == y)) a b
-- test pointer equality first


instance (Mapping k m, Ord a, Ord v) => Ord (Decision k m a v) where
  compare = pairMappings compare


instance Foldable m => Foldable (Decision k m a) where

  foldMap f = let
    p g _ = getAp . foldMap (Ap . g)
    in recurseMap f p . startDecision

runOnEmptyCache :: State (Cache (Node k m a v)) (Serial (Node k m a v)) -> Decision k m a v
runOnEmptyCache r = Decision . evalState r $ Cache M.empty


mapS :: (Mapping k m, Ord a, Ord v)
     => (u -> v)
     -> Serial (Node k m a u)
     -> State (Cache (Node k m a v)) (Serial (Node k m a v))
mapS f = let
  q r a = lift . makeBranch a <=< mtraverse r
  in recurseMapM (makeLeaf . f) q


-- | It's far from clear whether it's possible or not to do a general
-- traverse fast in this setting. This algorithm is slow (it may visit
-- nodes an exponential number of times).
traverseS :: (Mapping k m, Ord a, Ord v, Applicative f)
          => (u -> f v)
          -> Serial (Node k m a u)
          -> f (State (Cache (Node k m a v)) (Serial (Node k m a v)))
traverseS p = let
  inner s = case content s of
    Leaf v -> makeLeaf <$> p v
    Branch a m -> fmap (makeBranch a =<<) . getCompose $ mtraverse (Compose . inner) m
  in inner


mergeS :: (Mapping k m, Ord a, Ord w)
       => (u -> v -> w)
       -> Serial (Node k m a u)
       -> Serial (Node k m a v)
       -> State (Cache (Node k m a w)) (Serial (Node k m a w))
mergeS f = let
  pairSerial (Serial i _, Serial j _) = pairIntegers i j

  calculate r (s,t) = case (content s, content t) of
    (Leaf u, Leaf v) -> lift . makeLeaf $ f u v
    (Leaf _, Branch b n) -> lift . makeBranch b =<< mtraverse (r . (s,)) n
    (Branch a m, Leaf _) -> lift . makeBranch a =<< mtraverse (r . (,t)) m
    (Branch a m, Branch b n) -> case compare a b of
      LT -> lift . makeBranch a =<< mtraverse (r . (,t)) m
      GT -> lift . makeBranch b =<< mtraverse (r . (s,)) n
      EQ -> lift . makeBranch a =<< mergeA (curry r) m n
  in curry $ memoComputeM pairSerial calculate


-- | Just as for traverseS, this setting makes it seem unlikely that
-- an efficient algorithm will be possible.
mergeAS :: (Mapping k m, Ord a, Ord w, Applicative f)
        => (u -> v -> f w)
        -> Serial (Node k m a u)
        -> Serial (Node k m a v)
        -> f (State (Cache (Node k m a w)) (Serial (Node k m a w)))
mergeAS f = let
  inner s t = case (content s, content t) of
    (Leaf u, Leaf v) -> makeLeaf <$> f u v
    (Leaf _, Branch b n) -> fmap (makeBranch b =<<) . getCompose $ mtraverse (Compose . inner s) n
    (Branch a m, Leaf _) -> fmap (makeBranch a =<<) . getCompose $ mtraverse (Compose . flip inner t) m
    (Branch a m, Branch b n) -> case compare a b of
      LT -> fmap (makeBranch a =<<) . getCompose $ mtraverse (Compose . flip inner t) m
      GT -> fmap (makeBranch b =<<) . getCompose $ mtraverse (Compose . inner s) n
      EQ -> fmap (makeBranch a =<<) . getCompose $ mergeA (\c -> Compose . inner c) m n
  in inner

instance (Mapping k m, Ord a) => Mapping (a -> k) (Decision k m a) where

  cst x = let
    n = Leaf x
    s = Serial 0 n
    in Decision s

  isConst (Decision (Serial _ (Leaf x))) = Just x
  isConst (Decision (Serial _ (Branch _ _))) = Nothing

  act = let
    inner (Leaf x) _ = x
    inner (Branch a m) f = inner (content (act m (f a))) f
    in inner . content . startDecision

  mmap p = runOnEmptyCache . mapS p . startDecision

  mtraverse p = fmap runOnEmptyCache . traverseS p . startDecision

  merge p (Decision a) (Decision b) = runOnEmptyCache $ mergeS p a b

  mergeA p (Decision a) (Decision b) = runOnEmptyCache <$> mergeAS p a b

  pairMappings f = let

    pairSerial (Serial i _, Serial j _) = pairIntegers i j

    calculate r (s,t) = case (content s, content t) of
      (Leaf u, Leaf v) -> pure $ f u v
      (Leaf _, Branch _ n) -> getAp $ foldMap (Ap . r . (s,)) n
      (Branch _ m, Leaf _) -> getAp $ foldMap (Ap . r . (,t)) m
      (Branch a m, Branch b n) -> case compare a b of
        LT -> getAp $ foldMap (Ap . r . (,t)) m
        GT -> getAp $ foldMap (Ap . r . (s,)) n
        EQ -> getAp $ pairMappings (curry (Ap . r)) m n

    go s t = memoCompute pairSerial calculate (startDecision s, startDecision t)

    in go


instance (Ord a, Mapping k m, Neighbourly m) => Neighbourly (Decision k m a) where

  neighbours = let

    serial (Left (Serial i _)) = pairIntegers i 0
    serial (Right (Serial i _, Serial j _)) = pairIntegers i (j+1)

    -- find neighbours in a node
    p r (Left s) = case content s of
      Leaf _ -> pure S.empty
      Branch _ m -> do
        now <- getAp . foldMap (Ap . r . Right) $ neighbours m
        later <- getAp $ foldMap (Ap . r . Left) m
        pure (now <> later)
    -- find common values in two nodes
    p r (Right (s,t)) = case (content s, content t) of
      (Leaf u, Leaf v) -> pure $ if u == v then S.empty else S.singleton (u,v)
      (Leaf _, Branch _ n) -> getAp $ foldMap (Ap . r . Right . (s,)) n
      (Branch _ m, Leaf _) -> getAp $ foldMap (Ap . r . Right . (,t)) m
      (Branch a m, Branch b n) -> case compare a b of
        LT -> getAp $ foldMap (Ap . r . Right . (,t)) m
        GT -> getAp $ foldMap (Ap . r . Right . (s,)) n
        EQ -> let
          q x y = Ap . r $ Right (x,y)
          in getAp $ pairMappings q m n

    in memoCompute serial p . Left . startDecision


instance (Ord a, FoldableWithIndex k m, Mapping k m) => FoldableWithIndex (Map a k) (Decision k m a) where

  ifoldMap f = let
    inner m (Leaf x) = f m x
    inner m (Branch a n) = let
      g k = inner (M.insert a k m) . content
      in ifoldMap g n
    in inner M.empty . content . startDecision


-- | Find all assignments of variables that pass the test
--
-- Even for modest-sized decision diagrams, this can produce some very
-- large outputs!
satisfyingAssignments :: (Ord a, FoldableWithIndex k m) => (v -> Bool) -> Decision k m a v -> [Map a k]
satisfyingAssignments t = let
  p x = if t x then [M.empty] else []
  q f a = let
    h k = Ap . fmap (fmap (M.insert a k)) . f
    in getAp . ifoldMap h
  in recurseMap p q . startDecision

trueAssignments :: (Ord a, FoldableWithIndex k m) => Decision k m a Bool -> [Map a k]
trueAssignments = satisfyingAssignments id


generalCount :: (Mapping k m)
             => (a -> Int)
                -- ^ The serial number of a decision
             -> Int
                -- ^ The number of decisions
             -> (v -> n)
                -- ^ The count of a value
             -> (forall f z. Applicative f => (z -> f n) -> m z -> f n)
                -- ^ How to combine counts at a node
             -> Decision k m a v
                -- ^ The input decision diagram
             -> n
                -- ^ The count
generalCount s n c d = let

  step i (j,x)
    | i+1 == j = x
    | otherwise = step i (j-1, runIdentity $ d Identity (cst x))

  p v = (n, c v)

  q f a = let
    i = s a
    in fmap (i,) . d (fmap (step i) . f)

  in step (-1) . recurseMap p q . startDecision


foldingCount :: (Mapping k m, Num n)
             => (a -> Int)
                -- ^ The serial number of a decision
             -> Int
                -- ^ The number of decisions
             -> (v -> n)
                -- ^ The count of a value
             -> Decision k m a v
                -- ^ The input decision diagram
             -> n
                -- ^ The count
foldingCount s n c = let
  q f = fmap getSum . getAp . foldMap (Ap . fmap Sum . f)
  in generalCount s n c q

foldingCountTrue :: (Mapping k m, Num n)
                 => (a -> Int)
                    -- ^ The serial number of a decision
                 -> Int
                    -- ^ The number of decisions
                 -> Decision k m a Bool
                    -- ^ The input decision diagram
                 -> n
                    -- ^ The count
foldingCountTrue s n = foldingCount s n (\x -> if x then 1 else 0)

genTestS :: (Ord a, Ord b, Boolean b) => a -> State (Cache (Node Bool OnBool a b)) (Serial (Node Bool OnBool a b))
genTestS x = do
  n0 <- makeLeaf false
  n1 <- makeLeaf true
  makeBranch x $ OnBool n0 n1

-- | A building block for BDDs - tests if a variable is true
genTest :: (Ord a, Ord b, Boolean b) => a -> Decision Bool OnBool a b
genTest = runOnEmptyCache . genTestS

-- | Test if a variable is true (specialised to `Bool`)
test :: Ord a => a -> Decision Bool OnBool a Bool
test = genTest


-- | Make a single decision
decisionS :: (Mapping k m, Ord a, Ord v) => a -> m v -> State (Cache (Node k m a v)) (Serial (Node k m a v))
decisionS a m = makeBranch a =<< mtraverse makeLeaf m

decision :: (Mapping k m, Ord a, Ord v) => a -> m v -> Decision k m a v
decision a = runOnEmptyCache . decisionS a


decideAllS :: (Mapping k m, Ord a) => Map a (m Bool) -> State (Cache (Node k m a Bool)) (Serial (Node k m a Bool))
decideAllS = let
  begin [] = makeLeaf True
  begin l = do
    f <- makeLeaf False
    t <- makeLeaf True
    continue f t l
  continue _ u [] = pure u
  continue f u ((a,m):xs) = do
    v <- makeBranch a (mmap (\i -> if i then u else f) m)
    continue f v xs
  in begin . M.toDescList

decideAll :: (Mapping k m, Ord a) => Map a (m Bool) -> Decision k m a Bool
decideAll = runOnEmptyCache . decideAllS


decideAnyS :: (Mapping k m, Ord a) => Map a (m Bool) -> State (Cache (Node k m a Bool)) (Serial (Node k m a Bool))
decideAnyS = let
  begin [] = makeLeaf False
  begin l = do
    t <- makeLeaf True
    f <- makeLeaf False
    continue t f l
  continue _ u [] = pure u
  continue t u ((a,m):xs) = do
    v <- makeBranch a (mmap (\i -> if i then t else u) m)
    continue t v xs
  in begin . M.toDescList

decideAny :: (Mapping k m, Ord a) => Map a (m Bool) -> Decision k m a Bool
decideAny = runOnEmptyCache . decideAnyS



{-

-- | What is the best assignment of keys to values resulting in a
-- value on which `p` is `True`?
bestSuchThat :: (Mapping k m, Ord k, Ord a, Ord v) => (v -> Bool) -> (forall w. a -> m w -> Maybe (k, w)) -> Decision k m a v -> Maybe ([(a,k)], v)
bestSuchThat p q = let
  f x = if p x then Just ([], x) else Nothing
  g i = uncurry (\x -> fmap (first ((i,x):))) <=< q i
  in decisionRecurse f g
-}


debugShowCache :: Mapping k m => (Show a, Show v, Show (m Int)) => Cache (Node k m a v) -> [String]
debugShowCache (Cache c) = let

  entries = IM.fromList [(serial s,content s) | s <- M.elems c]

  padding = length (show (M.size c - 1))

  makeLine (n, s) = let
    lspace = replicate (padding - length (show n)) ' '
    rest = case s of
      Leaf v -> "Leaf " <> showsPrec 9 v ""
      Branch a m -> "Branch " <> showsPrec 9 a "" <> " " <> showsPrec 9 (mmap serial m) ""
    in lspace <> show n <> ": " <> rest

  in makeLine <$> IM.assocs entries


-- | Provided for debugging purposes only: if you find yourself
-- wanting this, that's a sign you should be using the State-valued
-- functionality instead.
recoverCache :: (Mapping k m, Ord a, Ord v) => Serial (Node k m a v) -> Cache (Node k m a v)
recoverCache = let
  inner s@(Serial _ n) = do
    m <- get
    case M.lookup n m of
      Just _ -> pure ()
      Nothing -> do
        case n of
          Leaf _ -> pure ()
          Branch _ a -> traverse_ inner a
        modify (M.insert n s)
  in Cache . flip execState M.empty . inner


-- | Output the structure of a Decision
debugShow :: (Mapping k m, Ord a, Ord v) => (Show a, Show v, Show (m Int)) => Decision k m a v -> String
debugShow (Decision x@(Serial s _)) = let
  prefix i = ((if i == s then "* " else "  ") <>)
  in unlines [prefix i l | (i,l) <- zip [0..] (debugShowCache (recoverCache x))]


restrictS :: (Mapping k m, Ord a, Ord v)
          => (a -> Maybe k)
          -> Serial (Node k m a v)
          -> State (Cache (Node k m a v)) (Serial (Node k m a v))
restrictS f = let
  q r a m = case f a of
    Just b -> r $ act m b
    Nothing -> lift . makeBranch a =<< mtraverse r m
  in recurseMapM makeLeaf q

-- | Simplify a Decision by fill in some values in advance
-- > act (restrict h d) f = let
-- >   f' x = case h x of
-- >     Just y  -> y
-- >     Nothing -> f x
-- >   in act d f'
restrict :: (Mapping k m, Ord a, Ord v)
         => (a -> Maybe k)
         -> Decision k m a v
         -> Decision k m a v
restrict f = runOnEmptyCache . restrictS f . startDecision


deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, Ord a, Ord v, Semigroup v) => Semigroup (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, Ord a, Ord v, Monoid v) => Monoid (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, Ord a, Ord v, Num v) => Num (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, Ord a, Ord v, Boolean v) => Boolean (Decision k m a v)

