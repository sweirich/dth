-- Various versions of a constrained datatype: complete trees.

-- Only uncomment one version at a time! (These should be in 
-- separate files.)

-- In the versions below the type 'Tree a' should contain only  
-- complete trees (where the height from the root to every leaf 
-- is constant). All other shapes of tree should be ruled out 
-- by the type system.

{-
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- Complete trees with nested datatypes

data Z a = Leaf
data S t a = Node (t a) a (t a)

data Nested t a = Z (t a) | S (Nested (S t) a)

type Tree a = Nested Z a

zero' = Leaf
zero = Z Leaf

one' = Node zero' 1 zero'
one  = S (Z one')

two' = Node one' 2 one'
two  = S (S (Z two'))

three' = Node two' 3 two'
three = S (S (S (Z three')))


instance Show a => Show (Tree a) where
  show x = show1 x (const ".") where
    show1 :: Show a => Nested t a -> (t a -> String) -> String
    show1 (Z t) f = f t 
    show1 (S t) f = show1 t (\ (Node l x r) -> "(" ++ f l ++ " " ++ show x ++ " " ++ f r ++ ")") 

-- calculate the height of the tree. Can be read off the tree prefix
height :: Tree a -> Int
height t = ht t where
   ht :: Nested t a -> Int
   ht (Z _) = 0
   ht (S n) = 1 + ht n

-- make a tree one stage shorter (if not a leaf, id otherwise)
decr :: Tree a -> Tree a 
decr (Z t) = Z t
decr (S t) = S (decr1 t)

decr1 :: Nested (S t) a -> Nested (S t) a
decr1 (S (Z (Node (Node ll xl lr) xc (Node rl xr rr)))) = 
  Z (Node ll xc rr)
decr1 (S t1) = S (decr1 t1)

-- make the tree one level larger
next :: Num a => Tree a -> Tree a
next t = next1 t

next1 :: Num a => Nested t a -> Nested t a
next1 (Z t) = S (Z (Node t 0 t))
next1 (S t) = S (next1 t)

-- merge two trees, if they have the same height
merge :: Tree a -> Tree a -> Maybe a 
merge = undefined

merge1 :: Nested s a -> Nested s a -> Nested s a
merge1 = undefined

-}


{-# LANGUAGE RankNTypes, ExistentialQuantification, EmptyDataDecls, NoMonomorphismRestriction, MultiParamTypeClasses, FlexibleInstances #-}        
data Z
data S n

-- Complete trees with Higher-order polymporphism
class Church repr a where
  leaf :: repr Z a 
  node :: repr h a -> a -> repr h a -> repr (S h) a 
  
data Tree a = forall h. Tree (forall repr. Church repr a => repr h a)

zero' = leaf  
zero  = Tree zero'

one' = node zero' 1 zero'
one  = Tree one'

two' = node one' 2 one' 
two = Tree two'

newtype Sh h a = Sh { unSh :: String }
instance Show a => Church Sh a where
  leaf = Sh "."
  node l x r = Sh ("(" ++ unSh l ++ show x ++ unSh r ++ ")")

instance Show a => Show (Tree a) where
  show (Tree t) = unSh t

newtype Ht h a = Ht { unHt :: Int }
instance Church Ht a where
  leaf = Ht 0
  node (Ht n1) _ (Ht n2) = (Ht (1 + n1))
  
height :: Tree a -> Int 
height (Tree t) = unHt t


{-
{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}        
-- Singleton version, w/type classes to unify type

data Leaf a = Leaf
data Node t1 t2 a = Node (t1 a) a (t2 a)

class CompleteTree t where
  fold :: b -> (b -> a -> b -> b) -> t a -> b
  
instance CompleteTree Leaf where  
  fold l n Leaf = l
instance (CompleteTree t) => CompleteTree (Node t t) where
  fold l n (Node t1 a t2) = n (fold l n t1) a (fold l n t2)
    
data Tree a = forall t. CompleteTree t => Tree (t a)

zero' = Leaf
zero = Tree zero'

one' = Node Leaf 1 Leaf
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

height :: Tree a -> Int 
height (Tree t) = fold 0 (\x _ y -> x + 1) t

-- Oleg's challenge

decr :: Tree a -> Tree a 
decr (Tree (Node (Node ll xl lr) xc (Node rl xr rr))) = undefined
  -- Tree (Node ll xc rr)

next :: Tree Int -> Tree Int
next (Tree t) = Tree (Node t 0 t)

merge :: Tree a -> Tree a -> Maybe a 
merge = undefined
-}
                    
{-
{-# LANGUAGE GADTs, DataKinds, ExistentialQuantification,
    TypeOperators, KindSignatures #-}        
-- Complete trees with GADTs

import Data.Type.Equality
import Data.Monoid 

data Nat = Z | S Nat

data Sing (n :: Nat) where
  SZ :: Sing Z
  SS :: Sing n -> Sing (S n)

data Complete h a where
  Leaf :: Complete Z a
  Node :: Complete h a -> a -> Complete h a -> Complete (S h) a
  
data Tree a = forall h. Tree (Complete h a)

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
  Tree (Node ll xc rr)

next :: Tree Int -> Tree Int
next (Tree t) = Tree (Node t 0 t)

merge :: Monoid a => Tree a -> Tree a -> Maybe (Tree a)
merge (Tree t1) (Tree t2) = case sameHeight t1 t2 of 
  Just Refl -> Just (Tree (merge' t1 t2))
  Nothing -> Nothing
  
merge' :: Monoid a => Complete h a -> Complete h a -> Complete h a
merge' Leaf Leaf = Leaf
merge' (Node l1 x r1) (Node l2 y r2) = Node (merge' l1 l2) (mappend x y) (merge' r1 r2)

sameHeight :: Complete n1 a -> Complete n2 a -> Maybe (n1 :~: n2)
sameHeight Leaf Leaf = Just Refl
sameHeight (Node l1 _ _) (Node l2 _ _) = case sameHeight l1 l2 of
  Just Refl -> Just Refl
sameHeight _ _ = Nothing

-}

