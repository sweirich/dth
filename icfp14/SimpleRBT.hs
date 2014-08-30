{-# LANGUAGE InstanceSigs,GADTs, DataKinds, KindSignatures, MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}

-- A version of Red-black trees that uses GADTs to ensure red-black tree
-- invariants. For ICFP 2014.
-- Stephanie Weirich

module SimpleGADT where

import Prelude hiding (max)
import Test.QuickCheck hiding (elements)
import Data.List(nub,sort)
import Control.Monad(liftM)
import Data.Type.Equality
import Data.Maybe(isJust)

-- 
data Color = R | B

-- Singleton type, connects the type level color to data
-- not necessary in a full-spectrum dependently-typed language
data Sing (c :: Color) where
   SR  :: Sing R -- red
   SB  :: Sing B -- black
  
-- natural numbers for tracking the black height
data Nat = Zero | Suc Nat

-- Well-formed Red/Black trees
-- n statically tracks the black height of the tree
-- c statically tracks the color of the root node
data Tree (n :: Nat) (c :: Color) (a :: *) where
   E  :: Tree Zero B a
   T  :: Valid c c1 c2 => 
         Sing c -> (Tree n c1 a) -> a -> (Tree n c2 a) -> Tree (Incr c n) c a

-- this type class forces the children of red nodes to be black
-- and also excludes double-black and negative-black nodes from
-- a valid red-black tree.
class Valid (c :: Color) (c1 :: Color) (c2 :: Color) where
instance Valid R B B 
instance Valid B c1 c2

-- incrementing the black height, based on the color 
type family Incr (c :: Color) (n :: Nat) :: Nat
type instance Incr B n             = Suc n
type instance Incr R   n           = n

-- the top level type of red-black trees
-- the data constructor forces the root to be black and 
-- hides the black height.
data RBSet a where
  Root :: (Tree n B a) -> RBSet a

-- We can't automatically derive show and equality
-- methods for GADTs.  
instance Show (Sing c) where  
  show SR = "R"
  show SB = "B"
  
instance Show a => Show (Tree n c a) where
  show E = "E"
  show (T c l x r) = 
    "(T " ++ show c ++ " " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"
instance Show a => Show (RBSet a) where
  show (Root x) = show x


showT :: Tree n c a -> String
showT E = "E"
showT (T c l x r) = 
    "(T " ++ show c ++ " " ++ showT l ++ " " 
          ++ "..." ++ " " ++ showT r ++ ")"


-- the test equality class gives us a proof that type level 
-- colors are equal. 
-- testEquality :: Sing c1 -> Sing c2 -> Maybe (c1 ~ c2)
instance TestEquality Sing where
  testEquality SR SR   = Just Refl
  testEquality SB SB   = Just Refl
  testEquality _ _   = Nothing

-- comparing two Red/Black trees for equality. 
-- unfortunately, because we have two instances, we can't
-- use the testEquality class.
(%==%) :: Eq a => Tree n1 c1 a -> Tree n2 c2 a -> Bool
E %==% E = True
T c1 a1 x1 b1 %==% T c2 a2 x2 b2 = 
  isJust (testEquality c1 c2) && a1 %==% a2 && x1 == x2 && b1 %==% b2
_ %==% _ = False
  
instance Eq a => Eq (RBSet a) where
  (Root t1) == (Root t2) = t1 %==% t2


 -- Public operations --

empty :: RBSet a
empty = Root E

member :: (Ord a) => a -> RBSet a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> Tree n c a -> Bool
  aux x E = False
  aux x (T _ l y r) | x < y     = aux x l
                    | x > y     = aux x r
                    | otherwise = True

elements :: Ord a => RBSet a -> [a]
elements (Root t) = aux t [] where
      aux :: Ord a => Tree n c a -> [a] -> [a]
      aux E acc = acc
      aux (T _ a x b) acc = aux a (x : aux b acc)

 -- INSERTION --

insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x (Root s) = blacken (ins x s) 
 where ins :: Ord a => a -> Tree n c a -> AlmostTree n a
       ins x E = AT SR E x E
       ins x s@(T color a y b) | x < y     = balanceL color (ins x a) y b
                               | x > y     = balanceR color a y (ins x b)
                               | otherwise = (AT color a y b)


       blacken :: AlmostTree n a -> RBSet a
       blacken (AT _ a x b) = Root (T SB a x b)

-- an intermediate data structure that temporarily violates the 
-- red-black tree invariants during insertion. 
-- This tree must be non-empty, but is allowed to have two red nodes in 
-- a row.
data AlmostTree n a where
   AT :: Sing c -> Tree n c1 a -> a -> Tree n c2 a -> AlmostTree (Incr c n) a

-- `balance` rotates away coloring conflicts
-- we separate it into two cases based on whether the infraction could
-- be on the left or the right
   
balanceL :: Sing c -> AlmostTree n a -> a -> Tree n c1 a -> AlmostTree (Incr c n) a
balanceL SB (AT SR (T SR a x b) y c) z d = AT SR (T SB a x b) y (T SB c z d)
balanceL SB (AT SR a x (T SR b y c)) z d = AT SR (T SB a x b) y (T SB c z d)
balanceL c (AT SB a x b) z d           = AT c (T SB a x b) z d
balanceL c (AT SR a@(T SB _ _ _) x b@(T SB _ _ _)) z d = AT c (T SR a x b) z d
balanceL c (AT SR a@E x b@E) z d       = AT c (T SR a x b) z d
   
   
balanceR :: Sing c -> Tree n c1 a -> a -> AlmostTree n a -> AlmostTree (Incr c n) a
balanceR SB a x (AT SR (T SR b y c) z d) = AT SR (T SB a x b) y (T SB c z d)
balanceR SB a x (AT SR b y (T SR c z d)) = AT SR (T SB a x b) y (T SB c z d)
balanceR c a x (AT SB b z d)           = AT c a x (T SB b z d)
balanceR c a x (AT SR b@(T SB _ _ _) z d@(T SB _ _ _)) = AT c a x (T SR b z d)
balanceR c a x (AT SR b@E z d@E)       = AT c a x (T SR b z d)
                                                        

-- testing code to ensure that we didn't miss any cases
instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = liftM (foldr insert empty) arbitrary
       
isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x              

prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

check_insert = do
    putStrLn "BST property"
    quickCheck prop_BST

main :: IO ()
main = 
 do
 return $! ()
