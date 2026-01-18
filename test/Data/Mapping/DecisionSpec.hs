module Data.Mapping.DecisionSpec where

import Prelude hiding ((&&), (||), not, all)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Test.Hspec
import Data.Algebra.Boolean ((&&), (||), not, all)
import Data.Mapping
import Data.Mapping.Decision
import Data.Mapping.Piecewise (Piecewise, greaterThanOrEqual, fromAscList)


boolAct ::    Ord a
           => Decision Bool OnBool a Bool
           -> [a]
           -> Bool
boolAct a s = act a (`S.member` S.fromList s)


completeAssignments :: Ord a => [a] -> Map a Bool -> [Map a Bool]
completeAssignments [] m = pure m
completeAssignments (v:vs) m = let
  l = case M.lookup v m of
    Just _  -> pure m
    Nothing -> [M.insert v False m, M.insert v True m]
  in completeAssignments vs =<< l


spec :: Spec
spec = do

  let x = test "x"
  let y = test "y"

  describe "Basic tests of act" $ do

    it "x false on {}" $ do
      boolAct x []    `shouldBe` False
    it "x true on {x}" $ do
      boolAct x ["x"] `shouldBe` True

  describe "Basic tests of mmap" $ do

    it "not x true on {}" $ do
      boolAct (not x) []    `shouldBe` True
    it "not x false on {x}" $ do
      boolAct (not x) ["x"] `shouldBe` False

  describe "Basic tests of merge" $ do

    it "x && y true on {}" $ do
      boolAct (x && y) []         `shouldBe` False
    it "x && y true on {x}" $ do
      boolAct (x && y) ["x"]      `shouldBe` False
    it "x && y true on {y}" $ do
      boolAct (x && y) ["y"]      `shouldBe` False
    it "x && y true on {x,y}" $ do
      boolAct (x && y) ["x", "y"] `shouldBe` True

    it "x || y true on {}" $ do
      boolAct (x || y) []         `shouldBe` False
    it "x || y true on {x}" $ do
      boolAct (x || y) ["x"]      `shouldBe` True
    it "x || y true on {y}" $ do
      boolAct (x || y) ["y"]      `shouldBe` True
    it "x || y true on {x,y}" $ do
      boolAct (x || y) ["x", "y"] `shouldBe` True

    it "y && x true on {}" $ do
      boolAct (y && x) []         `shouldBe` False
    it "y && x true on {x}" $ do
      boolAct (y && x) ["x"]      `shouldBe` False
    it "y && x true on {y}" $ do
      boolAct (y && x) ["y"]      `shouldBe` False
    it "y && x true on {x,y}" $ do
      boolAct (y && x) ["x", "y"] `shouldBe` True

    it "y || x true on {}" $ do
      boolAct (y || x) []         `shouldBe` False
    it "y || x true on {x}" $ do
      boolAct (y || x) ["x"]      `shouldBe` True
    it "y || x true on {y}" $ do
      boolAct (y || x) ["y"]      `shouldBe` True
    it "y || x true on {x,y}" $ do
      boolAct (y || x) ["x", "y"] `shouldBe` True

  describe "Check of trueAssignments" $ do

    let x0y0 = M.fromList [("x", False), ("y", False)]
    let x0y1 = M.fromList [("x", False), ("y", True)]
    let x1y0 = M.fromList [("x", True), ("y", False)]
    let x1y1 = M.fromList [("x", True), ("y", True)]

    it "Should work on &&" $ do
      S.fromList (completeAssignments ["x","y"] =<< trueAssignments (x && y))
        `shouldBe` S.fromList [x1y1]
    it "Should work on ||" $ do
      S.fromList (completeAssignments ["x","y"] =<< trueAssignments (x || y))
        `shouldBe` S.fromList [x0y1, x1y0, x1y1]
    it "Should work on not (1)" $ do
      S.fromList (completeAssignments ["x","y"] =<< trueAssignments (not x))
        `shouldBe` S.fromList [x0y0, x0y1]
    it "Should work on not (2)" $ do
      S.fromList (completeAssignments ["x","y"] =<< trueAssignments (not y))
        `shouldBe` S.fromList [x0y0, x1y0]

  describe "Independent maximal sets in C_100" $ do

    -- We build a decision tree representing all maximal subsets of
    -- {0,...,99} (regarded cyclically) with no consecutive elements.
    let l2 = (99,0):[(n,n+1) | n <- [0..98]]
    let l3 = (98,99,0):(99,0,1):[(n,n+1,n+2) | n <- [0..97]]
    let independent = all (\(i,j) -> not (test i && test j)) l2
    let maximal = all (\(i,j,k) -> test i || test j || test k) l3
    let t = independent && maximal

    -- Mentioned in Knuth
    it "should have the right count" $ do
      foldingCountTrue id 100 t `shouldBe` (1630580875002 :: Int)

  describe "Test of neighbours" $ do

    let m1 = decision "x" $ fromAscList 1 [(37,2),(74,3)]
    let m2 = decision "y" $ fromAscList 10 [(24,20),(83,30)]
    let m = m1 + m2 :: Decision Int (Piecewise Int) String Int
    it "should calculate neighbours correctly" $ do
      neighbours m `shouldBe` S.fromList [
        (11,12),(12,13),(21,22),(22,23),(31,32),(32,33),
        (11,21),(21,31),(12,22),(22,32),(13,23),(23,33)]

  describe "Decision trees for monomial divisibility" $ do

    -- We build a decision tree which associates, to each monomial,
    -- the largest-numbered monomial that divides it (or 0 if no such
    -- exists).
    let xy2 = M.fromList [("X", 1::Int), ("Y", 2)]      -- monomial 1
    let x2y = M.fromList [("X", 2), ("Y", 1)]           -- monomial 2
    let xyz = M.fromList [("X", 1), ("Y", 1), ("Z", 1)] -- monomial 3
    let monomials = M.fromList [(xy2, 1::Int), (x2y, 2), (xyz, 3)]
    let f i b = if b then i else 0
    let d = M.foldlWithKey' (\t m i -> merge max t (mmap (f i) . decideAll $ fmap greaterThanOrEqual m)) (cst 0) monomials
    let mapAct m = act d (\a -> M.findWithDefault 0 a $ M.fromList m)

    it "should get the right monomial for w^2y^4" $ do
      mapAct [("W", 2), ("Y", 4)] `shouldBe` 0

    it "should get the right monomial for w^3xy^2" $ do
      mapAct [("W", 3), ("X", 1), ("Y", 2)] `shouldBe` 1

    it "should get the right monomial for w^2x^2y^2" $ do
      mapAct [("W", 2), ("X", 2), ("Y", 2)] `shouldBe` 2

    it "should get the right monomial for w^2x^2y^2z^2" $ do
      mapAct [("W", 2), ("X", 2), ("Y", 2), ("Z", 2)] `shouldBe` 3

    it "should calculate neighbours correctly" $ do
      neighbours d `shouldBe` S.fromList [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
