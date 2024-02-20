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
--  == Recursive functions (current plan)
--
--  * Start with transform, and write a type for it that includes
--    transformations at the nodes, and is incremental.
--
--  * Can use it to produce versions that build too, I believe.
--
--
--  == Recursive functions (old)
--
--  * Create incremental functions for transformations
--
--  * Explain recursion. Three levels:
--
--    - process-based, for complete control over the recursion (eg,
--      searching for the best element with a certain property);
--
--    - thin wrappers for the unshared traverse/merge (and meld if it's
--      written);
--
--    - quick full recursors;
--
--  * Write a unshared meld (probably can make the unshared merge a thin
--    wrapper over it)
--
--  * "Rebuild": add a decision tree to a builder (can be done quickly
--    using addMap or similar, but that may not be obvious!)
--
--
--  == Functionality
--
--  * Ensure we have a full set of builder/decision functionality
--
--  * Neighbours
--
--  * The two composition functions (mjoin/combine)
--
--  * Monotonically renaming branches (Decision k m a v -> Decision k m b v)
--
--  * Nonmonotonic branch renaming
--
--  * Optimisation by reordering
--
--
--  == General engineering
--
--  * Stash away non-public functions (either with an explicit export
--    list, or in a separate module)
--
--  * Check for detailed comments in code
--
--  * Remove outdated and commented-out stuff
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
--  * Get the documentation nice



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
import Control.Monad.State (State, state, runState, evalState)
import Data.Algebra.Boolean (Boolean(..), AllB(..))
import Data.Bifunctor (first, bimap)
import Data.Bool (bool)
import Data.Foldable (toList)
import Data.Foldable.WithIndex (FoldableWithIndex(..))
import Data.Functor.Identity (Identity(..))
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap as IM
import Data.IntSet (IntSet)
import qualified Data.IntSet as IS
import Data.Ord (comparing)
import Data.Sequence (Seq)
import qualified Data.Sequence as Q
import Data.Set (Set)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Map.Merge.Strict as M
import Data.Mapping.Util (insertIfAbsent)
import Data.Tuple (swap)
import Formatting ((%))
import qualified Formatting as F

import Data.Mapping




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


newtype Builder k m a v = Builder {
  nodeMap :: Map (Node' k m a v) Int
}

emptyBuilder :: Builder k m a v
emptyBuilder = Builder M.empty

addLeaf :: (Mapping k m,
            forall x. Ord x => Ord (m x),
            Ord a,
            Ord v)
        => v
        -> State (Builder k m a v) (Node k m a v)
addLeaf x = let
  r b@(Builder m) = let
    (i, s) = insertIfAbsent (Leaf x) (M.size m) m
    b' = case s of
      Nothing -> b
      Just m' -> Builder m'
    in (Node i (Leaf x), b')
  in state r

-- | An atomic addition: assumes all nodes linked to are already in
addBranch :: (Mapping k m,
              forall x. Ord x => Ord (m x),
              Ord a,
              Ord v)
          => a
          -> m (Node k m a v)
          -> State (Builder k m a v) (Node k m a v)
addBranch c n = let
  r b@(Builder m) = case isConst n of
    Just x -> (x, b)
    Nothing -> let
      (i, s) = insertIfAbsent (Branch c n) (M.size m) m
      b' = case s of
        Nothing -> b
        Just m' -> Builder m'
      in (Node i (Branch c n), b')
  in state r



-- | An incremental approach to transforming
incTransform :: (Mapping l n)
             => (v -> f w)
             -> (forall x. a -> m (f x) -> f (n x)) -- is this general enough to use a builder?
             -> Node k m a v
             -> State (IntMap (f (Node l n a w)))
                              (f (Node l n a w))
incTransform p q (Node i u) = let
  r m = case m IM.!? i of
    Just x  -> (x, m)
    Nothing -> case u of
      Leaf a     -> _
      Branch c n -> _
  in state r

{-

assemble :: Ord k => (k -> u -> Map k v -> v) -> Map k u -> Map k v
assemble f = let
  inner d t = case M.minViewWithKey t of
    Nothing -> d
    Just ((k,u),t') -> inner (M.insert k (f k u d) d) t'
  in inner M.empty

assembleInt :: (Int -> u -> IntMap v -> v) -> IntMap u -> IntMap v
assembleInt f = let
  inner d t = case IM.minViewWithKey t of
    Nothing -> d
    Just ((k,u),t') -> inner (IM.insert k (f k u d) d) t'
  in inner IM.empty

{-
-- | Thread an accumulating value through a map, but with access to
-- the part already created
assembleAccum :: Ord k => (k -> u -> Map k v -> a -> (a, v)) -> a -> Map k u -> (a, Map k v)
assembleAccum f = let
  inner d a t = case M.minViewWithKey t of
    Nothing -> (a, d)
    Just ((k,u),t') -> let
      (b,v) = f k u d a
      in inner (M.insert k v d) b t'
  in inner M.empty
-}


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


-- | A concept to facilitate cached computations: a process can either
-- produce an answer or make a request
data Process r a = Answer a | Request r (a -> Process r a)


-- | A very general, data-sharing recursive function
--
-- This is written with the indirection given by `Process` so as to
-- avoid computing the values for all nodes downstream of a given one.
generalRecurse :: (Node' k m a v -> Process (Node k m a v) c)
               -> IntMap (Node' k m a v)
               -> IntMap c
generalRecurse p = let

  unpause done paused = case IM.minViewWithKey paused of
    Nothing -> done
    Just ((i,(j,f)),paused') -> process done paused' i (f (done IM.! j))

  process done paused i (Answer x) = unpause (IM.insert i x done) paused
  process done paused i (Request (Node j n) f) = case done IM.!? j of
    Just x  -> process done paused i (f x)
    Nothing -> process done (IM.insert i (j,f) paused) j (p n)

  start done todo = case IM.minViewWithKey todo of
    Nothing -> done
    Just ((i,x),todo') -> start (process done IM.empty i (p x)) todo'

  in start IM.empty


-- | A general, data-sharing recursive function.
--
-- To calculate the value on a node, it first calculates all values
-- downstream of it; this can sometimes be inefficient.
specialRecurse :: (Mapping k m,
                   Ord c)
               => (v -> c)
                  -- ^ What to do on a value
               -> (a -> m c -> c)
                  -- ^ What to do on a node
               -> IntMap (Node' k m a v)
                  -- ^ Nodes to work on
              -> IntMap c
specialRecurse p q m0 = let

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

-- | A recursive function on a decision
--
-- It calls specialRecurse, and hence calculates all values downstream of
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
decisionRecurse p q (Decision (Node i d)) = specialRecurse p q (IM.singleton i d) IM.! i


{-
cache :: Ord k => (k -> v) -> k -> State (Map k v) v
cache f k = let
  r m = case m M.!? k of
    Just v -> (v, m)
    Nothing -> let
      v = f k
      in (v, M.insert k v m)
  in state r

processCache :: Ord k => (k -> Process k v) -> k -> State (Map k v) v
processCache f = let
  compute k m (Answer v) = (v, M.insert k v m)
  compute k m (Request k' c) = let
    (v', m') = check k' m
    in compute k m' (c v')
  check k m = case m M.!? k of
    Just v -> (v, m)
    Nothing -> compute k m (f k)
  in state . check

processCacheHashed :: Ord r => (k -> r) -> (k -> Process k v) -> k -> State (Map r v) v
processCacheHashed h f = let
  compute r m (Answer v) = (v, M.insert r v m)
  compute r m (Request k c) = let
    (v', m') = check k m
    in compute r m' (c v')
  check k m = let
    r = h k
    in case m M.!? r of
      Just v -> (v, m)
      Nothing -> compute r m (f k)
  in state . check
-}


-- Use a transform
getInvariant :: (Mapping k m,
                 Ord c)
             => (v -> c)
                -- ^ What to do on a value
             -> (a -> m c -> c)
                -- ^ What do do on a node
             -> Node k m a v
             -> State (IntMap c) c
getInvariant p q = let
  in _


-- Use a meld
getPairing :: (Mapping k m,
               Ord c)
           => (v -> v -> c)
              -- ^ What to do on a pair of values
           -> (a -> m c -> m c -> c)
              -- ^ What to do on a branching
           -> Node k m a v
           -> Node k m a v
           -> State (Map (Int, Int) c) c
getPairing p q = _


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


addSharedTraverse :: (Mapping k m,
                Traversable f,
                Applicative f,
                forall x. Ord x => Ord (m x),
                Ord a,
                Ord w)
            => (v -> f w)
            -> IntMap (Node' k m a v)
            -> Builder k m a w
            -> (IntMap (f (Node k m a w)), Builder k m a w)
addSharedTraverse p = addTransform p (const id)


-- | Less general than mtraverse because of the requirement of
-- traversability of `f`, but more efficient (in time and space).
sharedTraverse :: (Mapping k m,
                 Traversable f,
                 Applicative f,
                 forall x. Ord x => Ord (m x),
                 Ord a,
                 Ord w)
             => (v -> f w)
             -> Decision k m a v
             -> f (Decision k m a w)
sharedTraverse p (Decision (Node i n)) = fmap Decision
  . (IM.! i)
  . fst
  $ addSharedTraverse p (IM.singleton i n) emptyBuilder


addMap :: (Mapping k m,
           forall x. Ord x => Ord (m x),
           Ord a,
           Ord w)
       => (v -> w)
       -> IntMap (Node' k m a v)
       -> Builder k m a w
       -> (IntMap (Node k m a w), Builder k m a w)
addMap p m = first (fmap runIdentity) . addSharedTraverse (Identity . p) m


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
restrict f (Decision (Node i n)) = Decision
  . (IM.! i)
  . fst
  $ addRestrict f (IM.singleton i n) emptyBuilder


-- | Find all the structure required for a merge. This is unlikely to
-- be of interest to the casual user.
completeMergeDownstream :: forall f j k l m n o a u v w.
                           (Mapping j m,
                            Mapping k n,
                            Mapping l o,
                            Ord a)
                        => (u -> v -> f w)
                        -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
                        -> Map (Int, Int) (Node' j m a u, Node' k n a v)
                        -> Map (Int, Int) (Either (f w) (a, o (Int, Int)))
completeMergeDownstream p q = let

  enqueue u (Node i m, Node j n) = M.insert (i,j) (m,n) u

  inner :: Map (Int, Int) (Either (f w) (a, o (Int, Int)))
        -> Map (Int, Int) (Node' j m a u, Node' k n a v)
        -> Map (Int, Int) (Either (f w) (a, o (Int, Int)))
  inner done todo = case M.maxViewWithKey todo of
    Nothing ->  done
    Just (((i,j),(Leaf x, Leaf y)), todo') -> let
      done' = M.insert (i,j) (Left (p x y)) done
      in inner done' todo'
    Just (((i,j),(Leaf x, Branch d n)), todo') -> let
      o = q d (,) (cst . Node i $ Leaf x) n
      done' = M.insert (i,j) (Right (d, mmap (bimap serial serial) o)) done
      in inner done' $ foldl enqueue todo' o
    Just (((i,j),(Branch c m, Leaf y)), todo') -> let
      o = q c (,) m (cst . Node j $ Leaf y)
      done' = M.insert (i,j) (Right (c, mmap (bimap serial serial) o)) done
      in inner done' $ foldl enqueue todo' o
    Just (((i,j),(Branch c m, Branch d n)), todo') -> let
      (a,o) = case compare c d of
        LT -> (c, q c (,) m (cst . Node j $ Branch d n))
        GT -> (d, q c (,) (cst . Node i $ Branch c m) n)
        EQ -> (c, q c (,) m n)
      done' = M.insert (i,j) (Right (a, mmap (bimap serial serial) o)) done
      in inner done' $ foldl enqueue todo' o

  in inner M.empty


-- | The mnemonic is that __me__ld is like __me__rge.
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

  in cook . completeMergeDownstream p q

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
         forall x. Ord x => Ord (o x),
         Ord a,
         Ord w)
     => (u -> v -> w)
     -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
     -> Decision j m a u
     -> Decision k n a v
     -> Decision l o a w
meld p q (Decision (Node i a)) (Decision (Node j b)) = Decision . (M.! (i,j)) . fst $ addMeld p q (M.singleton (i,j) (a,b)) emptyBuilder

addSharedMergeA :: forall f k m a u v w.
             (Traversable f,
              Applicative f,
              Mapping k m,
              forall x. Ord x => Ord (m x),
              Ord a,
              Ord w)
          => (u -> v -> f w)
          -> Map (Int, Int) (Node' k m a u, Node' k m a v)
          -> Builder k m a w
          -> (Map (Int, Int) (f (Node k m a w)), Builder k m a w)
addSharedMergeA p = addMeldA p (\_ -> merge)

-- | You should use this, rather than `mergeA`, when possible (that
-- is, when valued in a `Traversable` functor); it reuses nodes more.
sharedMergeA :: forall f k m a u v w.
              (Traversable f,
               Applicative f,
               Mapping k m,
               forall x. Ord x => Ord (m x),
               Ord a,
               Ord w)
           => (u -> v -> f w)
           -> Decision k m a u
           -> Decision k m a v
           -> f (Decision k m a w)
sharedMergeA p (Decision (Node i a)) (Decision (Node j b)) = fmap Decision . (M.! (i,j)) . fst $ addSharedMergeA p (M.singleton (i,j) (a,b)) emptyBuilder

addMerge :: forall k m a u v w.
            (Mapping k m,
             forall x. Ord x => Ord (m x),
             Ord a,
             Ord w)
         => (u -> v -> w)
         -> Map (Int, Int) (Node' k m a u, Node' k m a v)
         -> Builder k m a w
         -> (Map (Int, Int) (Node k m a w), Builder k m a w)
addMerge p = addMeld p (const merge)





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


addUnsharedTraverse :: forall f k m a v w.
                   (Mapping k m,
                    Applicative f,
                    forall x. Ord x => Ord (m x),
                    Ord a,
                    Ord w)
                => (v -> f w)
                -> IntMap (Node' k m a v)
                -> IntMap (f (State (Builder k m a w) (Node k m a w)))
addUnsharedTraverse p = let
  f :: Node' k m a v
    -> IntMap (f (State (Builder k m a w) (Node k m a w)))
    -> f (State (Builder k m a w) (Node k m a w))
  f (Leaf x) _ = state . addLeaf <$> p x
  f (Branch c n) m = fmap (state . addBranch c <=< mtraverse id) $ mtraverseInj ((m IM.!) . serial) n
  in assembleInt (const f) . completeDownstream


addUnsharedTransform :: forall f k l m n a v w.
                        (Applicative f,
                         Mapping l n,
                         forall x. Ord x => Ord (n x),
                         Ord a,
                         Ord w)
                     => (v -> f w)
                     -> (forall x. a -> m x -> n x)
                     -> IntMap (Node' k m a v)
                     -> IntMap (f (State (Builder l n a w) (Node l n a w)))
addUnsharedTransform p q = let
  f :: Node' k m a v
    -> IntMap (f (State (Builder l n a w) (Node l n a w)))
    -> f (State (Builder l n a w) (Node l n a w))
  f (Leaf x) _ = state . addLeaf <$> p x
  f (Branch c n) m =
  in assembleInt (const f) . completeDownstream


-- TODO Write in terms of addUnsharedMeldA?
addUnsharedMergeA :: forall f k m a u v w.
                 (Mapping k m,
                  Applicative f,
                  forall x. Ord x => Ord (m x),
                  Ord a,
                  Ord w)
              => (u -> v -> f w)
              -> Map (Int, Int) (Node' k m a u, Node' k m a v)
              -> Map (Int, Int) (f (State (Builder k m a w) (Node k m a w)))
addUnsharedMergeA p = let
  f :: Either (f w) (a, m (Int, Int))
    -> Map (Int, Int) (f (State (Builder k m a w) (Node k m a w)))
    -> f (State (Builder k m a w) (Node k m a w))
  f (Left u) _ = fmap (state . addLeaf) u
  f (Right (c, n)) m = fmap (state . addBranch c <=< mtraverse id) $ mtraverseInj (m M.!) n
  in assemble (const f) . completeMergeDownstream p (const merge)



addUnsharedMeld :: forall j k l m n o a u v w.
                   (Mapping k m,
                    forall x. Ord x => Ord (m x),
                    Ord a,
                    Ord w)
                => (u -> v -> w)
                -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
                -> Map (Int, Int) (Node' j m a u, Node' k n a v)
                -> Map (Int, Int) (State (Builder l o a w) (Node l o a w))
addUnsharedMeld p q = let
  in _



addUnsharedMeldA :: forall f j k l m n o a u v w.
                    (Mapping k m,
                     Applicative f,
                     forall x. Ord x => Ord (m x),
                     Ord a,
                     Ord w)
                 => (u -> v -> f w)
                 -> (forall x y z. Ord z => a -> (x -> y -> z) -> m x -> n y -> o z)
                 -> Map (Int, Int) (Node' j m a u, Node' k n a v)
                 -> Map (Int, Int) (f (State (Builder l o a w) (Node l o a w)))
addUnsharedMeldA p q = let

  in _



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

  mmapInj p = let
    f (Leaf x) _ = Leaf $ p x
    f (Branch c n) m = let
      h (Node i _) = Node i (m IM.! i)
      in Branch c $ mmapInj h n
    go (Decision (Node i n)) = Decision . Node i . (IM.! i) . assembleInt (const f) . completeDownstream $ IM.singleton i n
    in go

  -- | Use `sharedTraverse` where possible instead
  mtraverse p (Decision (Node i n)) = fmap (Decision . flip evalState emptyBuilder)
    . (IM.! i)
    $ addUnsharedTraverse p (IM.singleton i n)

  mtraverseInj p = let
    f (Leaf x) _ = Leaf <$> p x
    f (Branch c n) m = let
      h (Node i _) = Node i <$> (m IM.! i)
      in Branch c <$> mtraverseInj h n
    go (Decision (Node i n)) = fmap (Decision . Node i)
      . (IM.! i)
      . assembleInt (const f)
      . completeDownstream
      $ IM.singleton i n
    in go

  merge p (Decision (Node i m)) (Decision (Node j n)) = Decision
    . (M.! (i,j))
    . fst
    $ addMerge p (M.singleton (i,j) (m,n)) emptyBuilder

  -- | Use `sharedMergeA` where possible instead
  mergeA :: forall f u v w.
            (Applicative f,
             Ord w)
         => (u -> v -> f w)
         -> Decision k m a u
         -> Decision k m a v
         -> f (Decision k m a w)
  mergeA p (Decision (Node i m)) (Decision (Node j n)) =
    fmap (Decision . flip evalState emptyBuilder)
    . (M.! (i,j))
    $ addUnsharedMergeA p (M.singleton (i,j) (m,n))


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


-- | Output the structure of a Decision
debugShow :: forall k m a v. (Mapping k m, Show a, Show v, Show (m Int)) => Decision k m a v -> String
debugShow (Decision (Node i n)) = let
  f j a = pure $ F.formatToString (F.left 6 ' ' % ": " % F.string) j (g a)
  g (Leaf x) = "Leaf " <> showsPrec 11 x ""
  g (Branch a m) = "Branch " <> showsPrec 11 a " " <> showsPrec 11 (mmap serial m) ""
  in unlines . ifoldMap f . completeDownstream $ IM.singleton i n



{-
computeNeighbours :: forall k m a v c.
                     _
                  -> IntMap c
computeNeighbours = let

  addCommonValues :: (Node k m a v, Node k m a v)
                  -> State (Map (Int, Int) [(v, v)]) [(v, v)]
  addCommonValues = let
    h (Node i _, Node j _) = (i,j)
    f (Node i u, Node j v) = case (u,v) of
      (Leaf x, Leaf y) -> Answer [(x,y)]
      (Branch c m, Leaf y) -> _
      (Branch c m, Branch d n) -> case compare c d of
    in processCacheHashed h f

  in _
-}

  {-

  addCommonValues :: (Node k m a v, Node k m a v)
                  -> State (Map (Int, Int) [(v, v)]) [(v, v)]
  addCommonValues (Node i m, Node j n) e = case e M.!? (i,j) of
    Nothing ->

  inner :: Map (Int, Int) [(v, v)]
           -- ^ Common values taken by the two nodes listed
        -> IntMap c
           -- ^ Neighbours already calculated
        -> _
        -> IntMap c

  in _


instance (Mapping k m,
          Neighbourly m d)
       => Neighbourly (Decision k m a) (a, d) where
  foldmapNeighbours = _
-}

-}
