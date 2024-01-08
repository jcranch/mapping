module Data.Mapping.MapWithDefaultSpec where

import Data.Mapping
import Data.Mapping.MapWithDefault

import Test.Hspec


spec :: Spec
spec = do

  describe "MapWithDefault" $ do
    let m = fromList (1 :: Int) [('a',1), ('b',2), ('c',3)]
    let n = fromList (2 :: Int) [('b',1), ('c',1), ('d',3)]

    it "merges correctly" $ do
      merge (+) m n `shouldBe` fromList 3 [('c',4), ('d',4)]

    it "calculates neighbours correctly" $ do
      let m = fromlist "" [(1 :: Int,"a"),(2,"a"),(4,"b"),(5,"c")]
      let l = [(1,"","a"), (3,"a",""), (4,"","b"), (5,"b","c"), (6,"c","")]
      foldmapNeighbours (\d x y -> [(d,x,y)]) m `shouldBe` l
