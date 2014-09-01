{-# LANGUAGE KindSignatures, GADTs #-}

module Okasaki where

data A = A1 | A2 | A3 deriving (Eq, Ord)

data Color :: * where
   R :: Color
   B :: Color

data Tree :: * where
  E :: Tree
  T :: Color -> Tree -> A -> Tree -> Tree 


insert :: A -> Tree -> Tree                    
insert x s = blacken (ins s) 
   where ins E = T R E x E
         ins s@(T color a y b) 
             | x < y     = balance color (ins a) y b
             | x > y     = balance color a y (ins b)
             | otherwise = s
         blacken (T _ a x b) = T B a x b


balance :: Color -> Tree -> A -> Tree -> Tree
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)
balance color a x b = T color a x b
