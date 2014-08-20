{-# LANGUAGE GADTs, DataKinds, ExistentialQuantification,
    TypeOperators, KindSignatures #-}        

-- Perfect trees with GADTs indexing the *height* of the tree

import Data.Type.Equality
import Data.Monoid 

data Nat = Z | S Nat

data Sing (n :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

data Perfect h a where
  Leaf :: Perfect Z a
  Node :: Perfect h a -> a -> Perfect h a -> Perfect (S h) a
  
data Tree a = forall h. Tree (Perfect h a)

zero' = Leaf
zero = Tree zero'

one' = Node zero' 1 zero'
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

three' = Node two' 3 two' 
three = Tree three'


decr :: Tree a -> Tree a 
decr (Tree (Node (Node ll xl lr) xc (Node rl xr rr))) = 
  Tree (Node ll xc rr)x

next :: Tree Int -> Tree Int
next (Tree t) = Tree (Node t 0 t)

merge :: Monoid a => Tree a -> Tree a -> Maybe (Tree a)
merge (Tree t1) (Tree t2) = case sameHeight t1 t2 of 
  Just Refl -> Just (Tree (merge' t1 t2))
  Nothing -> Nothing
  
merge' :: Monoid a => Perfect h a -> Perfect h a -> Perfect h a
merge' Leaf Leaf = Leaf
merge' (Node l1 x r1) (Node l2 y r2) = Node (merge' l1 l2) (mappend x y) (merge' r1 r2)

sameHeight :: Perfect n1 a -> Perfect n2 a -> Maybe (n1 :~: n2)
sameHeight Leaf Leaf = Just Refl
sameHeight (Node l1 _ _) (Node l2 _ _) = case sameHeight l1 l2 of
  Just Refl -> Just Refl
sameHeight _ _ = Nothing