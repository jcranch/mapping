{-# LANGUAGE
      CPP,
      DerivingVia,
      MultiParamTypeClasses,
      OverloadedStrings,
      QuantifiedConstraints,
      RankNTypes,
      StandaloneDeriving,
      TupleSections,
      UndecidableInstances
  #-}

-- TODO
--
--  * Neighbours
--
--  * The two composition functions (mjoin/combine)
--
--  * Check for detailed comments in code
--
--  * Remove outdated, commented-out stuff
--
--  * Ensure we have a full set of builder/decision functionality
--
--  * hlint might have some things to say
--
--  * Module design:
--    - Separate into an "internal" and a public-facing module
--    - Separate out "Builder" stuff into another module?
--      (If we do that should we leave it in the State monad - lots of
--      evalState for the nonBase ones)
--
--  * Can write a more general step-based recursor which doesn't just
--    count
--
--  * Format types of functions better
--
--  * Decisions go upwards in order currently; should they go
--    downwards, to coincide with lexicographical orderings on maps
--    and hence maybe make smaller decision diagrams?
--
--    We can use Down if necessary to amend this.
--
--    I don't think there's a best order; we should just be honest.
--
--  * Increase test coverage
--
--  * Examples:
--     - finding optima
--     - finding random elements
--    (as examples of the more general functions, already coded, I hope)
--
--  * Documentation
--
--  * Monotonically renaming branches (Decision k m a v -> Decision k m b v)
--
--  * Composition algorithm
--
--  * Optimisation by reordering

-- | Decision diagrams, parametric in the mapping type for the decisions.
--
-- This is inspired by binary decision diagrams (as described in detail in
-- Knuth's The Art of Computer Programming, volume 4A); these are the specific
-- case where m is `BoolMapping` and v is `Bool`. Our algorithms are mostly
-- straightforward generalisations of those considered there.
module Data.Mapping.Decision where

import Prelude hiding ((&&))
#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
#else
import Control.Applicative (liftA2)
#endif
import Control.Monad ((<=<))
import Control.Monad.State (State, state, runState)
import Data.Algebra.Boolean (Boolean(..), AllB(..))
import Data.Bifunctor (first, bimap)
import Data.Bijection (Bij)
import qualified Data.Bijection as B
import Data.Bits (complement)
import Data.Bool (bool)
import Data.Foldable (foldrM, toList)
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Compose (Compose(..))
import Data.Functor.Identity (Identity(..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.Ord (comparing)
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Q
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map.Internal as MI
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import Data.Mapping.Util (insertIfAbsent)
import Data.Traversable (mapAccumL)
import Data.Tuple (swap)
import Formatting ((%))
import qualified Formatting as F

import Data.Mapping


-- | A helper function: monadically update a map left-to-right, with
-- access to the part of the map already created
assemble :: Monad m => (k -> u -> Map k v -> m v) -> Map k u -> m (Map k v)
assemble f = let
  go a MI.Tip = pure a
  go a (MI.Bin _ k v l r) = do
    a' <- go a l
    v' <- f k v a'
    go (MI.link k v' a' M.empty) r
  in go M.empty


-- | We assume that the serial numbers are all distinct within each
-- decision graph, and that nodes only refer to nodes with smaller
-- serial numbers). All code in this library will maintain this
-- invariant.
data Node' k m a v =
  Leaf v |
  Branch a (m (Node k m a v))

instance (Mapping k m, Eq a, Eq v, Eq (m (Node k m a v))) => Eq (Node' k m a v) where
  Leaf x     == Leaf y     = x == y
  Branch c m == Branch d n = c == d && m == n
  _          == _          = False

instance (Mapping k m, Ord a, Ord v, Ord (m (Node k m a v))) => Ord (Node' k m a v) where
  compare (Leaf _)     (Branch _ _) = LT
  compare (Branch _ _) (Leaf _)     = GT
  compare (Leaf x)     (Leaf y)     = compare x y
  compare (Branch c m) (Branch d n) = compare c d <> compare m n

data Node k m a v = Node {
  serial :: !Int,
  node :: Node' k m a v
}

instance Eq (Node k m a v) where
  Node i _ == Node j _ = i == j

instance Ord (Node k m a v) where
  compare = comparing serial

networkSerials :: Foldable m => IntMap (Node' k m a v) -> IntSet
networkSerials = let
  inner s m = case IM.maxViewWithKey m of
    Nothing -> s
    Just ((i,d),m') -> inner (IS.insert i s) $ case d of
        Leaf _ -> m'
        Branch _ n -> foldr (\(Node j e) -> IM.insert j e) m' n
  in inner IS.empty

networkSize :: Foldable m => IntMap (Node' k m a v) -> Int
networkSize = IS.size . networkSerials


-- | A `Node` is the internal point of view, and a `Decision` is the
-- external point of view: `Node`s are assumed to come from the same
-- tree (and hence can be compared by serial number); `Decision`s are
-- compared by tree traversals.
newtype Decision k m a v = Decision {
  getNode :: Node k m a v
}

size :: Foldable m => Decision k m a v -> Int
size (Decision (Node i d)) = networkSize $ IM.singleton i d

newtype Builder k m a v = Builder {
  nodeMap :: Map (Node' k m a v) Int
}

emptyBuilder :: Builder k m a v
emptyBuilder = Builder M.empty

addLeaf :: (Mapping k m, Ord a, Ord v, forall x. Ord x => Ord (m x)) => v -> Builder k m a v -> (Node k m a v, Builder k m a v)
addLeaf x b@(Builder m) = let
  (i, s) = insertIfAbsent (Leaf x) (M.size m) m
  b' = case s of
    Nothing -> b
    Just m' -> Builder m'
  in (Node i (Leaf x), b')

addBranch :: (Mapping k m, Ord a, Ord v, forall x. Ord x => Ord (m x)) => a -> m (Node k m a v) -> Builder k m a v -> (Node k m a v, Builder k m a v)
addBranch c n b@(Builder m) = case isConst n of
  Just x -> (x, b)
  Nothing -> let
    (i, s) = insertIfAbsent (Branch c n) (M.size m) m
    b' = case s of
      Nothing -> b
      Just m' -> Builder m'
    in (Node i (Branch c n), b')

instance Foldable m => Foldable (Decision k m a) where
  foldMap f = let
    inner a s m = case IM.minViewWithKey m of
      Nothing -> a
      Just ((i, d), m') -> let
        s' = IS.insert i s
        in case d of
          Leaf x -> inner (a <> f x) s' m'
          Branch _ n -> let
            h (Node j e) m1 = if IS.notMember j s' then IM.insert j e m1 else m1
            in inner a s' $ foldr h m' n
    start (Decision (Node i d)) = inner mempty IS.empty $ IM.singleton i d
    in start


-- | Unlikely to be useful for the casual user
completeDownstream :: Foldable m => IntMap (Node' k m a v) -> IntMap (Node' k m a v)
completeDownstream = let

  inner done todo = case IM.maxViewWithKey todo of
    Nothing -> done
    Just ((i, x), todo') -> let
      done' = IM.insert i x done
      in inner done' $ case x of
        Leaf _ -> todo'
        Branch _ n -> foldr (\(Node j z) -> IM.insert j z) done' n

  in inner IM.empty


-- | A general, data-sharing recursive function.
--
-- To calculate the value on a node, it first calculates all values
-- downstream of it; this can sometimes be inefficient.
genRecurse :: (Mapping k m,
               Ord c)
           => (v -> c)
              -- ^ What to do on a value
           -> (a -> m c -> c)
              -- ^ What do do on a node
           -> IntMap (Node' k m a v)
              -- ^ Nodes to work on
           -> IntMap c
genRecurse p q m0 = let

  -- TODO Check this works: it depends on strict maps behaving lazily:
  -- keys can be forced in order. If this fails could use lazy lists
  -- as well and then force it
  --
  -- TODO Could instead use assemble, in the Identity functor?
  f (Leaf x) = p x
  f (Branch c n) = q c (mmap ((m IM.!) . serial) n)
  m = fmap f $ completeDownstream m0
  in m

-- Here's an alternative
{-
genRecurse p q = let

  -- In phase 1 we gather data on what needs to be done
  phase1 prepared raw = case IM.maxViewWithKey raw of
    Nothing -> phase2 IM.empty prepared
    Just ((i, x), raw') -> let
      prepared' = IM.insert i x prepared
      in case x of
        Leaf y -> phase1 prepared' raw'
        Branch _ n -> phase1 prepared' $ foldr (\(Node i z) -> IM.insert i z) raw' n

  phase2 cooked prepared = case IM.minViewWithKey prepared of
    Nothing -> cooked
    Just ((i, Leaf x), prepared') -> phase2 (IM.insert i (p x) cooked) prepared'
    Just ((i, Branch c n), prepared') -> phase2 (IM.insert i (q c $ mmap ((cooked IM.!) . serial) n) cooked) prepared'

  in phase1 IM.empty
-}

-- | A general recursive function on a decision
--
-- It calls genRecurse, and hence calculates all values downstream of
-- any particular value.
decisionRecurse :: (Mapping k m,
                    Ord c)
                => (v -> c)
                -- ^ What to do on a value
                -> (a -> m c -> c)
                -- ^ What do do on a node
                -> Decision k m a v
                -- ^ Input decision
                -> c
decisionRecurse p q (Decision (Node i d)) = genRecurse p q (IM.singleton i d) IM.! i


-- | A general counting function
generalCounts :: (Ord a, Ord n, Mapping k m)
              => (a -> a -> Int)
                 -- ^ In the list of decisions, how far apart are these?
              -> a
                 -- ^ The first possible decision
              -> a
                 -- ^ The last possible decision
              -> (v -> n)
                 -- ^ The count of a value
              -> (m n -> n)
                 -- ^ How to combine counts at a node
              -> Decision k m a v
                 -- ^ The input decision diagram
              -> n
                 -- ^ The count
generalCounts d x0 x1 onVal combine = let
  d' Nothing Nothing = 2 + d x0 x1
  d' Nothing (Just y) = 1 + d x0 y
  d' (Just x) Nothing = 1 + d x x1
  d' (Just x) (Just y) = d x y
  p x (y, a) = let
    q 1 v = v
    q n v = q (n-1) . combine $ cst v
    in q (d' x y) a
  f x = (Nothing, onVal x)
  g a m = let
    b = Just a
    in (b, combine $ mmap (p b) m)
  in p Nothing . decisionRecurse f g

-- | How many values are true in a decision diagram with boolean
-- leaves?
numberTrueGeneral :: Mapping k m
                  => (m Integer -> Integer)
                  -- ^ How to add counts at a node
                  -> Int
                  -- ^ The first possible decision
                  -> Int
                  -- ^ The last possible decision
                  -> Decision k m Int Bool
                  -- ^ The input decision diagram
                  -> Integer
                  -- ^ The count
numberTrueGeneral g x0 x1 = let
  f a = if a then 1 else 0
  in generalCounts subtract x0 x1 f g

-- | How many values are True in a binary decision diagram with integer leaves?
numberTrue :: Int -> Int -> Decision Bool OnBool Int Bool -> Integer
numberTrue = numberTrueGeneral sum

-- | Assignments of variables that result in True
chunksTrue :: (Mapping k m, FoldableWithIndex k m, Ord k, Ord a) => Decision k m a Bool -> [Map a k]
chunksTrue = let
  f False = []
  f True = [M.empty]
  g a = ifoldMap (\x -> fmap (M.insert a x))
  in decisionRecurse f g

-- | All true values (may be a very long list even for reasonable Decisions)
listTrue :: forall k m a.
           (Mapping k m,
            FoldableWithIndex k m,
            Ord k,
            Ord a)
         => Set a
         -> Decision k m a Bool
         -> [Map a k]
listTrue s = let
  m = M.fromSet (const ()) s
  u = ifoldMap (\i _ -> [i]) $ cst @k @m ()
  fillIn = let
    onL = M.traverseMissing (\_ () -> u)
    onR = M.mapMissing (const (error "Expected a key"))
    onB = M.zipWithMatched (\_ () -> id)
    in M.mergeA onL onR onB
  in fillIn m <=< chunksTrue

-- | What is the best assignment of keys to values resulting in a
-- value on which @p@ is `True`?
bestSuchThat :: (Mapping k m, Ord k, Ord a, Ord v) => (v -> Bool) -> (forall w. a -> m w -> Maybe (k, w)) -> Decision k m a v -> Maybe ([(a,k)], v)
bestSuchThat p q = let
  f x = if p x then Just ([], x) else Nothing
  g i = uncurry (\x -> fmap (first ((i,x):))) <=< q i
  in decisionRecurse f g

-- | Build a sequence from key-value pairs; we take on trust that all
-- values are represented once.
fromKeyVals :: (Foldable f) => f (Int,a) -> Seq a
fromKeyVals = fmap snd . Q.sortBy (comparing fst) . Q.fromList . toList


-- | Add a decision tree based on a single decision
addSingleNode :: (Mapping k m,
                  Ord a,
                  Ord v,
                  forall x. Ord x => Ord (m x))
              => a
              -> m v
              -> Builder k m a v
              -> (Node k m a v, Builder k m a v)
addSingleNode r n = runState $ do
  n' <- mtraverse (state . addLeaf) n
  state (addBranch r n')

-- | A decision tree based on a single decision
singleNode :: (Mapping k m,
               Ord a,
               Ord v,
               forall x. Ord x => Ord (m x))
           => a
           -> m v
           -> Decision k m a v
singleNode r n = Decision . fst $ addSingleNode r n emptyBuilder

-- | Adds a test for a variable (valued in a general `Boolean`) to a
-- builder
addGenTest :: (Ord a,
               Ord b,
               Boolean b)
           => a
           -> Builder Bool OnBool a b
           -> (Node Bool OnBool a b, Builder Bool OnBool a b)
addGenTest r = addSingleNode r genTautOnBool

-- | Adds a test for a variable to a builder
addTest :: Ord a
        => a
        -> Builder Bool OnBool a Bool
        -> (Node Bool OnBool a Bool, Builder Bool OnBool a Bool)
addTest = addGenTest

-- | A building block for binary decision diagrams: test if a variable
-- is true (valued in any `Boolean` type)
genTest :: Boolean b => a -> Decision Bool OnBool a b
genTest r = let
  f = Node 0 (Leaf false)
  t = Node 1 (Leaf true)
  in Decision . Node 2 . Branch r $ OnBool f t

-- | A building block for binary decision diagrams: test if a variable
-- is true (specialised to `Bool`)
test :: a -> Decision Bool OnBool a Bool
test = genTest


-- | Rapidly take the conjunction of the inputs
addAll :: (Mapping k m,
           Ord a,
           forall x. Ord x => Ord (m x))
       => Map a (m Bool)
       -> Builder k m a Bool
       -> (Node k m a Bool, Builder k m a Bool)
addAll m = let
  in runState $ do
    f <- state (addLeaf False)
    t <- state (addLeaf True)
    let p r n s = do
          x <- s
          state (addBranch r $ mmap (bool f x) n)
    M.foldrWithKey p (pure t) m

addAny :: (Mapping k m,
           Ord a,
           forall x. Ord x => Ord (m x))
       => Map a (m Bool)
       -> Builder k m a Bool
       -> (Node k m a Bool, Builder k m a Bool)
addAny m = let
  in runState $ do
    f <- state (addLeaf False)
    t <- state (addLeaf True)
    let p r n s = do
          x <- s
          state (addBranch r $ mmap (bool x t) n)
    M.foldrWithKey p (pure f) m

makeAll :: (Mapping k m,
             Ord a,
             forall x. Ord x => Ord (m x))
         => Map a (m Bool)
         -> Decision k m a Bool
makeAll m = Decision . fst $ addAll m emptyBuilder

makeAny :: (Mapping k m,
             Ord a,
             forall x. Ord x => Ord (m x))
         => Map a (m Bool)
         -> Decision k m a Bool
makeAny m = Decision . fst $ addAny m emptyBuilder


-- | A very general traverse, where the shape of nodes can change (the
-- mnemonic is that __tra__nsform is like __tra__verse). The functor
-- @f@ needs to be `Traversable`, so as to reuse the same builder.
addTransform :: forall f k l m n a v w.
                (Traversable f,
                 Applicative f,
                 Mapping l n,
                 forall x. Ord x => Ord (n x),
                 Ord a,
                 Ord w)
             => (v -> f w)
             -> (forall x. a -> m x -> n x)
             -> IntMap (Node' k m a v)
             -> Builder l n a w
             -> (IntMap (f (Node l n a w)), Builder l n a w)
addTransform p q = let

  -- TODO Should this be done by some external function, which
  -- generalises `completeDownstream`?
  process :: IntMap (Either (f w) (a, n Int))
          -> IntMap (Node' k m a v)
          -> Builder l n a w
          -> (IntMap (f (Node l n a w)), Builder l n a w)
  process prepared raw = case IM.maxViewWithKey raw of
    Nothing -> cook prepared
    Just ((i,Leaf x),raw') -> let
      prepared' = IM.insert i (Left (p x)) prepared
      in process prepared' raw'
    Just ((i,Branch c n),raw') -> let
      t = q c n
      prepared' = IM.insert i (Right (c, mmap serial t)) prepared
      raw'' = foldl (\m (Node j e) -> IM.insert j e m) raw' t
      in process prepared' raw''

  cook :: IntMap (Either (f w) (a, n Int))
       -> Builder l n a w
       -> (IntMap (f (Node l n a w)), Builder l n a w)
  cook p0 b0 = let
    -- TODO use "assemble"
    f :: Builder l n a w -> Int -> Either (f w) (a, n Int) -> (Builder l n a w, f (Node l n a w))
    f b _ (Left x) = swap $ runState (traverse (state . addLeaf) x) b
    f b _ (Right (c, u)) = swap $ runState (traverse (state . addBranch c) $ mtraverse (v IM.!) u) b
    (v, b') = swap $ IM.mapAccumWithKey f b0 p0
    in (v, b')

  in process IM.empty


transform :: (Traversable f,
              Applicative f,
              Mapping l n,
              forall x. Ord x => Ord (n x),
              Ord a,
              Ord w)
          => (v -> f w)
          -> (forall x. a -> m x -> n x)
          -> Decision k m a v
          -> f (Decision l n a w)
transform p q (Decision (Node i n)) = fmap Decision . (IM.! i) . fst $ addTransform p q (IM.singleton i n) emptyBuilder


-- | __ma__ni__p__ulate is like __map__.
addManipulate :: (Mapping l n,
                  forall x. Ord x => Ord (n x),
                  Ord a,
                  Ord w)
              => (v -> w)
              -> (forall x. a -> m x -> n x)
              -> IntMap (Node' k m a v)
              -> Builder l n a w
              -> (IntMap (Node l n a w), Builder l n a w)
addManipulate p q m = first (fmap runIdentity) . addTransform (Identity . p) q m


manipulate :: (Mapping l n,
               forall x. Ord x => Ord (n x),
               Ord a,
               Ord w)
           => (v -> w)
           -> (forall x. a -> m x -> n x)
           -> Decision k m a v
           -> Decision l n a w
manipulate p q (Decision (Node i n)) = Decision . (IM.! i) . fst $ addManipulate p q (IM.singleton i n) emptyBuilder


addTraverse :: (Mapping k m,
                Traversable f,
                Applicative f,
                forall x. Ord x => Ord (m x),
                Ord a,
                Ord w)
            => (v -> f w)
            -> IntMap (Node' k m a v)
            -> Builder k m a w
            -> (IntMap (f (Node k m a w)), Builder k m a w)
addTraverse p = addTransform p (const id)


-- | Less general than mtraverse because of the requirement of
-- traversability of `f`, but more efficient (in time and space).
fastTraverse :: (Mapping k m,
                 Traversable f,
                 Applicative f,
                 forall x. Ord x => Ord (m x),
                 Ord a,
                 Ord w)
             => (v -> f w)
             -> Decision k m a v
             -> f (Decision k m a w)
fastTraverse p (Decision (Node i n)) = fmap Decision . (IM.! i) . fst $ addTraverse p (IM.singleton i n) emptyBuilder


addMap :: (Mapping k m,
           forall x. Ord x => Ord (m x),
           Ord a,
           Ord w)
       => (v -> w)
       -> IntMap (Node' k m a v)
       -> Builder k m a w
       -> (IntMap (Node k m a w), Builder k m a w)
addMap p m = first (fmap runIdentity) . addTraverse (Identity . p) m


addRestrict :: (forall x. Ord x => Ord (m x), Ord v, Ord a, Mapping k m) => (a -> Maybe k) -> IntMap (Node' k m a v) -> Builder k m a v -> (IntMap (Node k m a v), Builder k m a v)
addRestrict f m b = let
    g x n = case f x of
      Nothing -> n
      Just c -> cst (act n c)
  in addManipulate id g m b

-- | Fill in some values of a map
-- > act (restrict h d) f = let
-- >   f' x = case h x of
-- >     Just y  -> y
-- >     Nothing -> f x
-- >   in act d f'
restrict :: (forall x. Ord x => Ord (m x), Ord v, Ord a, Mapping k m) => (a -> Maybe k) -> Decision k m a v -> Decision k m a v
restrict f (Decision (Node i n)) = Decision . (IM.! i) . fst $ addRestrict f (IM.singleton i n) emptyBuilder


-- | __me__ld is like __me__rge.
addMeldA :: forall f j k l m n o a u v w.
            (Traversable f,
             Applicative f,
             Mapping j m,
             Mapping k n,
             Mapping l o,
             forall x. Ord x => Ord (o x),
             Ord a,
             Ord w)
         => (u -> v -> f w)
         -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
         -> Map (Int, Int) (Node' j m a u, Node' k n a v)
         -> Builder l o a w
         -> (Map (Int, Int) (f (Node l o a w)), Builder l o a w)
addMeldA p q = let

  enqueue u (Node i m, Node j n) = M.insert (i,j) (m,n) u
  
  process :: Map (Int, Int) (Either (f w) (a, o (Int, Int)))
          -> Map (Int, Int) (Node' j m a u, Node' k n a v)
          -> Builder l o a w
          -> (Map (Int, Int) (f (Node l o a w)), Builder l o a w)
  process done todo = case M.maxViewWithKey todo of
    Nothing -> cook done
    Just (((i,j),(Leaf x, Leaf y)), todo') -> let
      done' = M.insert (i,j) (Left (p x y)) done
      in process done' todo'
    Just (((i,j),(Leaf x, Branch d n)), todo') -> let
      o = q d (,) (cst . Node i $ Leaf x) n
      done' = M.insert (i,j) (Right (d, mmap (bimap serial serial) o)) done
      in process done' $ foldl enqueue todo' o
    Just (((i,j),(Branch c m, Leaf y)), todo') -> let
      o = q c (,) m (cst . Node j $ Leaf y)
      done' = M.insert (i,j) (Right (c, mmap (bimap serial serial) o)) done
      in process done' $ foldl enqueue todo' o
    Just (((i,j),(Branch c m, Branch d n)), todo') -> let
      (a,o) = case compare c d of
        LT -> (c, q c (,) m (cst . Node j $ Branch d n))
        GT -> (d, q c (,) (cst . Node i $ Branch c m) n)
        EQ -> (c, q c (,) m n)
      done' = M.insert (i,j) (Right (a, mmap (bimap serial serial) o)) done
      in process done' $ foldl enqueue todo' o

  cook :: Map (Int, Int) (Either (f w) (a, o (Int, Int)))
       -> Builder l o a w
       -> (Map (Int, Int) (f (Node l o a w)), Builder l o a w)
  cook p0 b0 = let
    -- TODO use assemble
    f :: Builder l o a w
      -> (Int, Int)
      -> Either (f w) (a, o (Int, Int))
      -> (Builder l o a w, f (Node l o a w))
    f b _ (Left x) = swap $ runState (traverse (state . addLeaf) x) b
    f b _ (Right (c, u)) = swap $ runState (traverse (state . addBranch c) $ mtraverse (v M.!) u) b
    (v, b') = swap $ M.mapAccumWithKey f b0 p0
    in (v, b')

  in process M.empty

meldA :: forall f j k l m n o a u v w.
         (Traversable f,
          Applicative f,
          Mapping j m,
          Mapping k n,
          Mapping l o,
          forall x. Ord x => Ord (o x),
          Ord a,
          Ord w)
      => (u -> v -> f w)
      -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
      -> Decision j m a u
      -> Decision k n a v
      -> f (Decision l o a w)
meldA p q (Decision (Node i a)) (Decision (Node j b)) = fmap Decision .
  (M.! (i,j)) .
  fst $
  addMeldA p q (M.singleton (i,j) (a,b)) emptyBuilder


addMeld :: forall j k l m n o a u v w.
           (Mapping j m,
            Mapping k n,
            Mapping l o,
            Functor n,
            forall x. Ord x => Ord (o x),
            Ord a,
            Ord w)
        => (u -> v -> w)
        -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
        -> Map (Int, Int) (Node' j m a u, Node' k n a v)
        -> Builder l o a w
        -> (Map (Int, Int) (Node l o a w), Builder l o a w)
addMeld p q m = let
  p' x y = Identity $ p x y
  in first (fmap runIdentity) . addMeldA p' q m

meld :: forall j k l m n o a u v w.
        (Mapping j m,
         Mapping k n,
         Mapping l o,
         Functor n,
         forall x. Ord x => Ord (o x),
         Ord a,
         Ord w)
     => (u -> v -> w)
     -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
     -> Decision j m a u
     -> Decision k n a v
     -> Decision l o a w
meld p q (Decision (Node i a)) (Decision (Node j b)) = Decision . (M.! (i,j)) . fst $ addMeld p q (M.singleton (i,j) (a,b)) emptyBuilder

addMergeA :: forall f k m a u v w.
             (Traversable f,
              Applicative f,
              Mapping k m,
              Functor m,
              forall x. Ord x => Ord (m x),
              Ord a,
              Ord w)
          => (u -> v -> f w)
          -> Map (Int, Int) (Node' k m a u, Node' k m a v)
          -> Builder k m a w
          -> (Map (Int, Int) (f (Node k m a w)), Builder k m a w)
addMergeA p = addMeldA p (\_ -> merge)

-- | You should use this, rather than `mergeA`, when possible (that
-- is, when valued in a `Traversable` functor); it reuses nodes more.
fastMergeA :: forall f k m a u v w.
              (Traversable f,
               Applicative f,
               Mapping k m,
               Functor m,
               forall x. Ord x => Ord (m x),
               Ord a,
               Ord w)
           => (u -> v -> f w)
           -> Decision k m a u
           -> Decision k m a v
           -> f (Decision k m a w)
fastMergeA p (Decision (Node i a)) (Decision (Node j b)) = fmap Decision . (M.! (i,j)) . fst $ addMergeA p (M.singleton (i,j) (a,b)) emptyBuilder

addMerge :: forall k m a u v w.
            (Mapping k m,
             Functor m,
             forall x. Ord x => Ord (m x),
             Ord a,
             Ord w)
         => (u -> v -> w)
         -> Map (Int, Int) (Node' k m a u, Node' k m a v)
         -> Builder k m a w
         -> (Map (Int, Int) (Node k m a w), Builder k m a w)
addMerge p = addMeld p (const merge)


{-



{-




-- | A general function for merging bases
baseGenMerge ::    (Ord a, Ord w, Ord (o Int), Mapping l o)
                => (u -> v -> w)
                -> (forall x . Ord x => a -> m x -> o x)
                -> (forall y . Ord y => a -> n y -> o y)
                -> (forall x y. (Ord x, Ord y) => a -> m x -> n y -> o (x, y))
                -> Base h m a u -> Base k n a v -> Set (Int, Int) -> Builder (Int, Int) l o a w
baseGenMerge pLL pNL pLN pNN (Base l1 m1) (Base l2 m2) = let

  close aLL aNL aLN aNN s = case S.maxView s of
    Nothing -> make aLL aNL aLN aNN
    Just ((i1, i2), s') -> case (i1 < 0, i2 < 0) of
      ( True,  True) -> let
        x = pLL (Q.index l1 $ complement i1) (Q.index l2 $ complement i2)
        in close (M.insert (i1, i2) x aLL) aNL aLN aNN s'
      ( True, False) -> let
        Node r2 n2 = Q.index m2 i2
        o = mmap (i1,) $ pLN r2 n2
        s'' = S.union s' . S.fromList $ toList o
        in close aLL aNL (M.insert (i1, i2) (r2, o) aLN) aNN s''
      (False,  True) -> let
        Node r1 n1 = Q.index m1 i1
        o = mmap (,i2) $ pNL r1 n1
        s'' = S.union s' . S.fromList $ toList o
        in close aLL (M.insert (i1, i2) (r1, o) aNL) aLN aNN s''
      (False, False) -> let
        Node r1 n1 = Q.index m1 i1
        Node r2 n2 = Q.index m2 i2
        (r, o) = case compare r1 r2 of
          LT -> (r1, mmap (,i2) $ pNL r1 n1)
          GT -> (r2, mmap (i1,) $ pLN r2 n2)
          EQ -> (r1, pNN r1 n1 n2)
        s'' = S.union s' . S.fromList $ toList o
        in close aLL aNL aLN (M.insert (i1, i2) (r, o) aNN) s''

  make aLL aNL aLN aNN = let

    b0 = emptyBuilder

    makeL b (i, j) x = addLeaf x (i, j) b
    b1 = M.foldlWithKey' makeL b0 aLL

    makeN b (i, j) (r, o) = addNode r o (i, j) b
    b2 = M.foldlWithKey' makeN b1 aNL
    b3 = M.foldlWithKey' makeN b2 aLN
    b4 = M.foldlWithKey' makeN b3 aNN
    in b4

  in close M.empty M.empty M.empty M.empty


-- | Merge two bases in an applicative functor
baseMergeA ::    (Applicative f, Ord a, Ord w, Ord (m Int), Mapping k m)
              => (u -> v -> f w)
              -> Base k m a u -> Base k m a v -> Set (Int, Int) -> f (Builder (Int, Int) k m a w)
baseMergeA p (Base l1 m1) (Base l2 m2) = let

  close aLL aNL aLN aNN s = case S.maxView s of
    Nothing -> make aLL aNL aLN aNN
    Just ((i1, i2), s') -> case (i1 < 0, i2 < 0) of
      ( True,  True) -> let
        x = p (Q.index l1 $ complement i1) (Q.index l2 $ complement i2)
        in close (M.insert (i1, i2) x aLL) aNL aLN aNN s'
      ( True, False) -> let
        Node r2 n2 = Q.index m2 i2
        o = mmap (i1,) n2
        s'' = S.union s' . S.fromList $ toList o
        in close aLL aNL (M.insert (i1, i2) (r2, o) aLN) aNN s''
      (False,  True) -> let
        Node r1 n1 = Q.index m1 i1
        o = mmap (,i2) n1
        s'' = S.union s' . S.fromList $ toList o
        in close aLL (M.insert (i1, i2) (r1, o) aNL) aLN aNN s''
      (False, False) -> let
        Node r1 n1 = Q.index m1 i1
        Node r2 n2 = Q.index m2 i2
        (r,o) = case compare r1 r2 of
          LT -> (r1, mmap (,i2) n1)
          GT -> (r2, mmap (i1,) n2)
          EQ -> (r1, merge (,) n1 n2)
        s'' = S.union s' . S.fromList $ toList o
        in close aLL aNL aLN (M.insert (i1, i2) (r, o) aNN) s''

  make aLL aNL aLN aNN = let

    b0 = pure emptyBuilder

    makeL b (i, j) = liftA2 (\b' x'-> addLeaf x' (i, j) b') b
    b1 = M.foldlWithKey' makeL b0 aLL

    makeN b (i, j) (r, o) = addNode r o (i, j) <$> b
    b2 = M.foldlWithKey' makeN b1 aNL
    b3 = M.foldlWithKey' makeN b2 aLN
    b4 = M.foldlWithKey' makeN b3 aNN
    in b4

  in close M.empty M.empty M.empty M.empty


-- | Merge two bases
baseMerge ::    (Ord a, Ord w, Ord (m Int), Mapping k m)
             => (u -> v -> w)
             -> Base k m a u -> Base k m a v -> Set (Int, Int) -> Builder (Int, Int) k m a w
baseMerge p b1 b2 = let
  p' x y = Identity $ p x y
  in runIdentity . baseMergeA p' b1 b2


-- | Folds over *all* the leaves; not something you want to do to an
-- arbitrary base
instance Foldable (Base k m a) where
  foldMap p = foldMap p . leaves

instance Foldable m => Foldable (Decision k m a) where
  foldMap p (Decision (Base l m) s) = let
    inner x old new = case IS.minView new of
      Nothing        -> x
      Just (i, new') -> if i < 0
        then inner (x <> p (Q.index l (complement i))) (IS.insert i old) new'
        else let
          old' = IS.insert i old
          extra = IS.difference (IS.fromList . toList . nodeBranch $ Q.index m i) old'
          in inner x old' (IS.union new' extra)
    in inner mempty IS.empty $ IS.singleton s

instance (Ord a, Ord (m Int), Mapping k m) => Mapping (a -> k) (Decision k m a) where

  cst x = Decision (Base (Q.singleton x) Q.empty) (-1)

  act (Decision (Base l n) s) f = let
    inner i
      | i < 0 = Q.index l $ complement i
      | otherwise = let
          Node a m = Q.index n i
          in inner . act m $ f a
    in inner s

  -- We assume the diagram is optimised, so it is constant only if it starts
  -- with a leaf.
  isConst (Decision (Base l _) s)
    | s < 0     = Just . Q.index l $ complement s
    | otherwise = Nothing

  mtraverse p (Decision (Base l m) s) = buildDecision s <$> baseTraverse p (Base l m)

  mmap p (Decision b s) = buildDecision s $ baseMap p b

  merge p (Decision b1 s1) (Decision b2 s2) = buildDecision (s1, s2) $ baseMerge p b1 b2 (S.singleton (s1, s2))

  mergeA p (Decision b1 s1) (Decision b2 s2) = buildDecision (s1, s2) <$> baseMergeA p b1 b2 (S.singleton (s1, s2))

-}



instance (Ord a, forall x. Ord x => Ord (m x), Mapping k m) => Mapping (a -> k) (Decision k m a) where

  cst = Decision . Node 0 . Leaf

  act (Decision d) p = let
    inner (Node _ (Leaf x))     = x
    inner (Node _ (Branch c n)) = inner (act n (p c))
    in inner d

  isConst (Decision (Node _ n)) = case n of
    Leaf x     -> Just x
    Branch _ _ -> Nothing

  mmap p (Decision (Node i n)) = Decision . (IM.! i) . fst $ addMap p (IM.singleton i n) emptyBuilder

  -- | Consider using `fastTraverse` where possible instead.
  mtraverse p (Decision (Node i n)) = let

    in _ . completeDownstream $ IM.singleton i n

  merge p (Decision (Node i m)) (Decision (Node j n)) = Decision . (M.! (i,j)) . fst $ addMerge p (M.singleton (i,j) (m,n)) emptyBuilder

  mergeA = _



deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Ord v, Semigroup v) => Semigroup (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Ord v, Monoid v) => Monoid (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Ord v, Num v) => Num (Decision k m a v)

deriving via (AlgebraWrapper (a -> k) (Decision k m a) v)
  instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Ord v, Boolean v) => Boolean (Decision k m a v)



instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Eq v) => Eq (Decision k m a v) where
  d1 == d2 = getAllB $ pairMappings (\x y -> AllB (x == y)) d1 d2

instance (Mapping k m, forall x. Ord x => Ord (m x), Ord a, Ord v) => Ord (Decision k m a v) where
  -- | Impressively short definition
  compare = pairMappings compare


{-
addmjoin :: (Mapping k m,
             forall x. Ord x => Ord (m x),
             Ord a,
             Ord v,
             Ord w)
         => (v -> Decision k m a w)
         -> (Decision k m a v)
         -> (Builder k m a w, Builder k m a (Either v w))
         -> (Decision k m a w, (Builder k m a w, Builder k m a (Either v w)))
addmjoin f m

-- | A (nearly) monadic join
--
-- Thinking of decisions as functions `(a -> k) -> v`, this is the
-- expected monadic structure. The corresponding unit is `cst`.
mjoin :: (Mapping k m,
          forall x. Ord x => Ord (m x),
          Ord a,
          Ord v,
          Ord w)
      => (v -> Decision k m a w)
      -> Decision k m a v
      -> Decision k m a w
mjoin f m = let
  fromLeft (Left x) = x
  fromLeft (Right _) = error "mjoin: this shouldn't happen"
  ifValue n x = let
    g (Left x) _ = Left x
    g (Right x') y
      | x == x'   = Left y
      | otherwise = Right x'
    in merge g n (f x)
  in mmap fromLeft $ foldl ifValue (mmap Right m) m


addCombine :: _

-- The function mentioned by Knuth has a type like
--     combine :: Decision Bool OnBool a Bool -> (a -> Decision Bool OnBool b Bool) -> Decision Bool OnBool b Bool)
-- If we regard @Decision k m a v@ as being @(a -> k) -> v@ then this has type
--     (b -> ((a -> k) -> l)) -> ((b -> l) -> v) -> (a -> k) -> v
-- and there's a term of this type, \h g f -> g (\x -> h x f).
combine :: (b -> Decision k m a l) -> Decision l n b v -> Decision k m a v
combine = _
-}

{-
instance (Mapping k m,
          Neighbourly m,
          Ord a,
          Ord (m Int))
       => Neighbourly (Decision k m a) where
  neighbours = _
-}

{-
-  neighbours (Decision (Base l m) s) = let
-    f v (Node _ n) = let
-      here = let
-        b = Base l m
-        e (i, j) = S.filter (uncurry (/=)) $ mutualValues (Decision b i) (Decision b j)
-        in foldMap e $ neighbours n
-      there = let
-        g i
-          | i < 0     = mempty
-          | otherwise = Q.index v i
-        in foldMap g n
-      in v |> (here <> there)
-    in Q.index (foldl f Q.empty m) s
-}

-}

-- | Output the structure of a Decision
debugShow :: forall k m a v. (Mapping k m, Show a, Show v, Show (m Int)) => Decision k m a v -> String
debugShow (Decision (Node i n)) = let
  f j a = pure $ F.formatToString (F.left 6 ' ' % ": " % F.string) j (g a)
  g (Leaf x) = "Leaf " <> showsPrec 11 x ""
  g (Branch a m) = "Branch " <> showsPrec 11 a " " <> showsPrec 11 (mmap serial m) ""
  in unlines . ifoldMap f . completeDownstream $ IM.singleton i n
