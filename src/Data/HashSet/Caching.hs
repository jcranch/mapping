{-# LANGUAGE UnboxedTuples #-}

-- | Functions using the HashMap/HashSet data structures for an
-- apparently unintended purpose: structure sharing.
module Data.HashSet.Caching where

import Control.Monad.ST (runST)
import Data.Bifunctor (bimap)
import Data.Bits ((.|.), (.&.))
import Data.Hashable (Hashable)
import Data.HashMap.Internal (Hash, hash, mask, index, update32, ptrEq, bitsPerSubkey, sparseIndex, two, collision, bitmapIndexedOrFull, HashMap(..), Leaf(..))
import qualified Data.HashMap.Internal.Array as A
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HM
import Data.HashSet (HashSet)
import qualified Data.HashSet as HS
import qualified Data.HashSet.Internal as HSI
import Control.Monad.State.Strict (State, state)


retrieveOrSnocWith :: (a0 -> p0 -> (# a0 #)) -> t1 -> t2 -> A.Array (Leaf t1 t2) -> ((t1, t2), A.Array (Leaf t1 t2))
retrieveOrSnocWith = _


-- | Take a key and a value; if the key already exists in the map
-- return it and its corresponding value; if not insert them. This is
-- intended to be useful for structure-sharing algorithms: it is
-- intended to be used to ensure there is only one version of each `k`
-- persisting in memory.
cacheInsert :: Hashable k => k -> v -> HashMap k v -> ((k, v), HashMap k v)
cacheInsert k = cacheInsert' (hash k) k

cacheInsert' :: Hashable k => Hash -> k -> v -> HashMap k v -> ((k, v), HashMap k v)
cacheInsert' h0 k0 v0 m0 = go h0 k0 v0 0 m0
  where
    go !h !k x !_ Empty = ((k, x), Leaf h (L k x))
    go h k x s t@(Leaf hy l@(L ky y))
        | hy == h = if ky == k
                    then ((ky, y), t)
                    else ((k, x), collision h l (L k x))
        | otherwise = runST (two s h k x hy t)
    go h k x s t@(BitmapIndexed b ary)
        | b .&. m == 0 =
            let !ary' = A.insert ary i $! Leaf h (L k x)
            in ((k, x), bitmapIndexedOrFull (b .|. m) ary')
        | otherwise =
            let !st  = A.index ary i
            in case go h k x (s+bitsPerSubkey) st of
              ((k', x'), st') -> ((k', x'), if st' `ptrEq` st
                                   then t
                                   else BitmapIndexed b (A.update ary i st'))
      where m = mask h s
            i = sparseIndex b m
    go h k x s t@(Full ary) =
        let !st  = A.index ary i
        in case go h k x (s+bitsPerSubkey) st of
          ((k',x'),st') -> ((k',x'), if st' `ptrEq` st
                             then t
                             else Full (update32 ary i st'))
      where i = index h s

    go h k x s t@(Collision hy v)
        | h == hy   = Collision h <$> _ (\a _ -> (# a #)) k x v
        | otherwise = go h k x s $ BitmapIndexed (mask hy s) (A.singleton t)
{-# INLINABLE cacheInsert' #-}

-- | @cache x s@ tests if @x@ is in @s@: if it is, it returns the
-- version in @s@; if it isn't, it inserts it
cache :: Hashable a => a -> HashSet a -> (a, HashSet a)
cache x = bimap fst HSI.HashSet . cacheInsert x () . HSI.asMap

-- | As above, but in the State monad
cacheS :: Hashable a => a -> State (HashSet a) a
cacheS = state . cache
