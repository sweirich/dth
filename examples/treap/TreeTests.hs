module TreeTests where

--import Treap
import Treap2
import Control.Monad (liftM2)
import qualified Data.List as List (intersect, nub, sort, union)
import qualified Data.IntSet as Set (fromList, difference) 
import Test.QuickCheck hiding (elements)

-- ---------------------------------------------------------------------
-- Instance Classes
-- ---------------------------------------------------------------------

instance (Arbitrary a, Ord a, Show a) => Arbitrary (Tree a) where
  arbitrary = liftM2 fromList2 arbitrary arbitrary 
  -- shrink t = shrinkTree t

-- ---------------------------------------------------------------------
-- Auxiliary functions
-- ---------------------------------------------------------------------

isSorted :: Ord a => [a] -> Bool
isSorted l = List.sort (List.nub l) == l

-- ---------------------------------------------------------------------
-- QuickCheck Properties
-- ---------------------------------------------------------------------

prop_BST :: Tree Int -> Bool
prop_BST = isSorted . elements

prop_heap :: Tree Int -> Bool
prop_heap t
  | isEmpty t = True
  | otherwise = p >= priority lt && p >= priority rt && prop_heap lt &&
                prop_heap rt
  where
    p  = priority t
    lt = getLeft t
    rt = getRight t

prop_treap :: Tree Int -> Bool
prop_treap t = prop_BST t && prop_heap t

prop_insert1 :: Positive Int -> Int -> Tree Int -> Bool
prop_insert1 p x t = member x t' && prop_treap t'
  where t' = insert p x t 

prop_insert2 :: Positive Int -> Int -> Tree Int -> Bool
prop_insert2 p x t = all (`member` t') $ elements t
  where t' = insert p x t

prop_delete1 :: Tree Int -> Bool
prop_delete1 t = all (\x -> let t' = delete x t in
                            not (member x t') && prop_treap t')
                     (elements t)

prop_delete2 :: Tree Int -> Bool
prop_delete2 t = all (\(x,y) -> x == y || member y (delete x t)) allPairs
  where
    allPairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete3 :: Int -> Tree Int -> Property
prop_delete3 x t = notElem x (elements t) ==> (delete x t == t)

prop_split :: Int -> Tree Int -> Bool
prop_split x t = prop_treap lt && prop_treap rt && all (<x) (elements lt) 
  && all (>x) (elements rt)
  where
    (lt, rt) = split x t

prop_join :: Int -> Tree Int -> Bool
prop_join x t = prop_treap t' && elements t' == elements (delete x t)
  where
    (lt, rt) = split x t
    t'       = join lt rt

prop_union :: Tree Int -> Tree Int -> Bool
prop_union t1 t2 = prop_treap t
  && elements t == List.sort (elements t1 `List.union` elements t2)
  where
    t = t1 `union` t2

prop_intersect :: Tree Int -> Tree Int -> Bool
prop_intersect t1 t2 = prop_treap t
  && elements t == List.sort (elements t1 `List.intersect` elements t2)
  where
    t = t1 `intersect` t2

prop_difference :: Tree Int -> Tree Int -> Bool
prop_difference t1 t2 = prop_treap t
  && Set.fromList (elements t) == Set.difference s1 s2
  where
    t  = difference t1 t2
    s1 = Set.fromList (elements t1)
    s2 = Set.fromList (elements t2)
 
main :: IO ()
main = do quickCheck prop_treap
          quickCheck prop_insert1
          quickCheck prop_insert2
          quickCheck prop_delete1
          quickCheck prop_delete2
          quickCheck prop_delete3
          quickCheck prop_split
          quickCheck prop_join
          quickCheck prop_union
          quickCheck prop_intersect
          quickCheck prop_difference