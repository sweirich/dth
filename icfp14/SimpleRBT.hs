{-# LANGUAGE InstanceSigs,GADTs, DataKinds, KindSignatures, MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}

-- A version of Red-black trees that uses GADTs to ensure red-black tree
-- invariants. For ICFP 2014.

-- This version has separate data constructors for red and black internal 
-- nodes (i.e. TR and TB)  It is also possible to combine them together
-- in the definition of Tree (much like AlmostTree does), but this code 
-- does not do so for easier comparison to Agda. (Agda pattern matching 
-- does not allow such combination in Tree.)

-- Stephanie Weirich

module SimpleRBT where

import Prelude hiding (max)
import Test.QuickCheck hiding (elements)
import Data.List(nub,sort)
import Control.Monad(liftM)
import Data.Type.Equality
import Data.Maybe(isJust)

-- 32 loc for insertion

data Color = R | B

  
-- natural numbers for tracking the black height
data Nat = Zero | Suc Nat

-- Well-formed Red/Black trees
-- n statically tracks the black height of the tree
-- c statically tracks the color of the root node
data Tree (n :: Nat) (c :: Color) (a :: *) where
   E  :: Tree Zero B a
   TR :: Tree n B a -> a -> Tree n B a -> Tree n R a
   TB :: Tree n c1 a -> a -> Tree n c2 a -> Tree (Suc n) B a

-- the top level type of red-black trees
-- the data constructor forces the root to be black and 
-- hides the black height.
data RBT a where
  Root :: (Tree n B a) -> RBT a


-- Singleton type, connects the type level color to data
-- not necessary in a full-spectrum dependently-typed language
data Sing (c :: Color) where
   SR  :: Sing R -- red
   SB  :: Sing B -- black

-- incrementing the black height, based on the color 
type family Incr (c :: Color) (n :: Nat) :: Nat
type instance Incr B n             = Suc n
type instance Incr R   n           = n

 -- Public operations --

empty :: RBT a
empty = Root E

member :: (Ord a) => a -> RBT a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> Tree n c a -> Bool
  aux x E = False
  aux x (TR l y r) | x < y     = aux x l
                   | x > y     = aux x r
                   | otherwise = True
  aux x (TB l y r) | x < y     = aux x l
                   | x > y     = aux x r
                   | otherwise = True

elements :: Ord a => RBT a -> [a]
elements (Root t) = aux t [] where
      aux :: Ord a => Tree n c a -> [a] -> [a]
      aux E acc = acc
      aux (TR a x b) acc = aux a (x : aux b acc)
      aux (TB a x b) acc = aux a (x : aux b acc)

 -- INSERTION --

-- 12 loc
insert :: (Ord a) => a -> RBT a -> RBT a                    
insert x (Root s) = blacken (ins x s) 
 where ins :: Ord a => a -> Tree n c a -> AlmostTree n a
       ins x E = AT SR E x E
       ins x s@(TR a y b) | x < y     = balanceL SR (ins x a) y b
                          | x > y     = balanceR SR a y (ins x b)
                          | otherwise = (AT SR a y b)
       ins x s@(TB a y b) | x < y     = balanceL SB (ins x a) y b
                          | x > y     = balanceR SB a y (ins x b)
                          | otherwise = (AT SB a y b)


       blacken :: AlmostTree n a -> RBT a
       blacken (AT _ a x b) = Root (TB a x b)


-- 14 loc  (AlmostTree + balance)
       
-- an intermediate data structure that temporarily violates the 
-- red-black tree invariants during insertion. 
-- This tree must be non-empty, but is allowed to have two red nodes in 
-- a row.
data AlmostTree n a where
   AT :: Sing c -> Tree n c1 a -> a -> Tree n c2 a -> AlmostTree (Incr c n) a

-- `balance` rotates away coloring conflicts
-- we separate it into two cases based on whether the infraction could
-- be on the left or the right
-- However, we do not need to have separate versions for red and black   
-- nodes.
balanceL :: Sing c -> AlmostTree n a -> a -> Tree n c1 a -> AlmostTree (Incr c n) a
balanceL SB (AT SR (TR a x b) y c) z d = AT SR (TB a x b) y (TB c z d)
balanceL SB (AT SR a x (TR b y c)) z d = AT SR (TB a x b) y (TB c z d)
-- fallthrough cases
balanceL c (AT SB a x b) z d             = AT c (TB a x b) z d
-- Note that the following two cases are exhaustive.  We know that there 
-- will be at most 2 reds in a row. So if c is R then the two subtrees must
-- both be black. (The AlmostTree type isn't precise enough to guarantee 
-- this.)
balanceL c (AT SR a@(TB _ _ _) x b@(TB _ _ _)) z d = AT c (TR a x b) z d
balanceL c (AT SR a@E x b@E) z d       = AT c (TR a x b) z d
   
   
balanceR :: Sing c -> Tree n c1 a -> a -> AlmostTree n a -> AlmostTree (Incr c n) a
balanceR SB a x (AT SR (TR b y c) z d) = AT SR (TB a x b) y (TB c z d)
balanceR SB a x (AT SR b y (TR c z d)) = AT SR (TB a x b) y (TB c z d)
balanceR c a x (AT SB b z d)           = AT c a x (TB b z d)
balanceR c a x (AT SR b@(TB _ _ _) z d@(TB _ _ _)) = AT c a x (TR b z d)
balanceR c a x (AT SR b@E z d@E)       = AT c a x (TR b z d)
                                                        

-- testing code to ensure that we didn't miss any cases


-- We can't automatically derive show and equality
-- methods for GADTs.  
instance Show (Sing c) where  
  show SR = "R"
  show SB = "B"
  
instance Show a => Show (Tree n c a) where
  show E = "E"
  show (TR l x r) = 
    "(TR " ++ " " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"
  show (TB l x r) = 
    "(TB " ++ " " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"

instance Show a => Show (RBT a) where
  show (Root x) = show x


-- comparing two Red/Black trees for equality. 
(%==%) :: Eq a => Tree n1 c1 a -> Tree n2 c2 a -> Bool
E %==% E = True
TR a1 x1 b1 %==% TR  a2 x2 b2 = 
  a1 %==% a2 && x1 == x2 && b1 %==% b2
TB a1 x1 b1 %==% TB a2 x2 b2 = 
  a1 %==% a2 && x1 == x2 && b1 %==% b2

_ %==% _ = False
  
instance Eq a => Eq (RBT a) where
  (Root t1) == (Root t2) = t1 %==% t2


instance (Ord a, Arbitrary a) => Arbitrary (RBT a)  where
  arbitrary = liftM (foldr insert empty) arbitrary
       
isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x              

prop_BST :: RBT Int -> Bool
prop_BST t = isSortedNoDups (elements t)

check_insert = do
    putStrLn "BST property"
    quickCheck prop_BST

main :: IO ()
main = 
 do
 return $! ()
