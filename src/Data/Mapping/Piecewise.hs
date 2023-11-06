{-# LANGUAGE CPP #-}

module Data.Mapping.Piecewise where

#if MIN_VERSION_GLASGOW_HASKELL(9,6,0,0)
#else
import Control.Applicative (liftA2)
#endif
import Control.Applicative (liftA3)
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
  leftEnd :: v,
  starts :: Map k v
} deriving (Eq, Ord)

piecewiseFromAsc :: Eq k => v -> [(k,v)] -> Piecewise k v
piecewiseFromAsc k = Piecewise k . M.fromAscList

instance (Show k, Show v) => Show (Piecewise k v) where
  showsPrec d (Piecewise k m) =
    ("piecewiseFromAsc " <>) .
    showsPrec d k .
    (" " <>) .
    showList (M.toList m)

changeAt :: v -> k -> v -> Piecewise k v
changeAt a x b = Piecewise a $ M.singleton x b

atLeast :: k -> Piecewise k Bool
atLeast k = changeAt False k True

lessThan :: k -> Piecewise k Bool
lessThan k = changeAt True k False

fromAscList :: (Ord k, Eq v) => v -> [(k,v)] -> Piecewise k v
fromAscList = let
  inner _ [] = []
  inner a ((y,b):r)
    | a == b    = inner a r
    | otherwise = (y,b):inner b r
  run x = Piecewise x . M.fromAscList . inner x
  in run

values :: Piecewise k v -> [v]
values (Piecewise x m) = x : M.elems m

instance Foldable (Piecewise k) where
  foldMap f (Piecewise a m) = f a <> foldMap f m

instance Ord k => Mapping k (Piecewise k) where

  cst x = Piecewise x M.empty

  act (Piecewise a f) x = case M.lookupLE x f of
    Nothing -> a
    Just (_,b) -> b

  isConst (Piecewise a f) = if M.null f then Just a else Nothing

  mmap p (Piecewise a f) = fromAscList (p a) (fmap p <$> M.toList f)

  mtraverse p (Piecewise a f) = liftA2 fromAscList (p a) (traverse (traverse p) $ M.toList f)

  merge p = let

    inner a b c r@((x,a'):r') s@((y,b'):s') = case compare x y of
      LT -> let
        c' = p a' b
        in if c' == c then inner a' b c r' s else (x,c'):inner a' b c' r' s
      GT -> let
        c' = p a b'
        in if c' == c then inner a b' c r s' else (y,c'):inner a b' c' r s'
      EQ -> let
        c' = p a' b'
        in if c' == c then inner a' b' c r' s' else (x,c'):inner a' b' c' r' s'
    inner a _ c [] ((y,b'):s') = let
      c' = p a b'
      in if c' == c then inner a b' c [] s' else (y,c'):inner a b' c' [] s'
    inner _ b c ((x,a'):r') [] = let
      c' = p a' b
      in if c' == c then inner a' b c r' [] else (x,c'):inner a' b c' r' []
    inner _ _ _ [] [] = []

    run (Piecewise a f) (Piecewise b g) = let
      c = p a b
      l = inner a b c (M.toList f) (M.toList g)
      in Piecewise c $ M.fromList l

    in run

  mergeA p = let

    maybePrepend x u v l
      | u == v    = l
      | otherwise = (x,v):l

    inner a b c r@((x,a'):r') s@((y,b'):s') = case compare x y of
      LT -> let
        c' = p a' b
        in liftA3 (maybePrepend x) c c' $ inner a' b c' r' s
      GT -> let
        c' = p a b'
        in liftA3 (maybePrepend y) c c' $ inner a b' c' r s'
      EQ -> let
        c' = p a' b'
        in liftA3 (maybePrepend x) c c' $ inner a' b' c' r' s'
    inner a _ c [] ((y,b'):s') = let
      c' = p a b'
      in liftA3 (maybePrepend y) c c' $ inner a b' c' [] s'
    inner _ b c ((x,a'):r') [] = let
      c' = p a' b
      in liftA3 (maybePrepend x) c c' $ inner a' b c' r' []
    inner _ _ _ [] [] = pure []

    run (Piecewise a f) (Piecewise b g) = let
      c = p a b
      l = inner a b c (M.toList f) (M.toList g)
      in liftA2 Piecewise c (M.fromList <$> l)

    in run

instance Neighbourly (Piecewise k) where
  neighbours m = let
    v = values m
    in S.fromList $ zip v (tail v)


{-
-- May work with a future version of cond
deriving via (AlgebraWrapper k (Piecewise k) b)
  instance (Ord k, Ord b, Boolean b) => Boolean (Piecewise k b)
-}
