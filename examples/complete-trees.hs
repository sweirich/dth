-- Various versions of a constrained datatype: complete trees.

-- Only uncomment one version at a time! (These should be in 
-- separate files.)

-- In the versions below the type 'tree a' should contain only  
-- complete trees (where the height from the root to every leaf 
-- is constant). All other shapes of tree should be ruled out 
-- by the type system.

{-
-- Balanced trees with nested datatypes

data Z a = Leaf
data S t a = Node (t a, a, t a)

data Nested t a = Z (t a) | S (Nested (S t) a)

type Tree a = Nested Z a

zero' = Leaf
zero = Z Leaf

one' = Node (zero', 1, zero')
one  = S (Z one')

two' = Node (one', 2, one')
two  = S (S (Z two'))

three' = Node (two', 3, two')
three = S (S (S (Z three')))

height :: Tree a -> Int
height t = ht t where
   ht :: Nested t a -> Int
   ht (Z _) = 0
   ht (S n) = 1 + ht n
-}


{-
{-# LANGUAGE RankNTypes, ExistentialQuantification, EmptyDataDecls, NoMonomorphismRestriction #-}        
data Z
data S n

-- Balanced trees with Higher-order polymporphism
class Church repr where
  leaf :: repr Z a 
  node :: repr h a -> a -> repr h a -> repr (S h) a 
  
data Tree a = forall h. Tree (forall repr. Church repr => repr h a)

zero' = leaf  
zero  = Tree zero'

one' = node zero' 1 zero'
one  = Tree one'

two' = node one' 2 one' 
two = Tree two'

newtype Ht h a = Ht { unHt :: Int }
instance Church Ht where
  leaf = Ht 0
  node (Ht n1) _ (Ht n2) = (Ht (1 + n1))
  
height :: Tree a -> Int 
height (Tree t) = unHt t
-}

{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}        
-- Singleton version, w/type classes to unify type

data Leaf a = Leaf
data Node t1 t2 a = Node (t1 a) a (t2 a)

class BalancedTree t where
  fold :: b -> (b -> a -> b -> b) -> t a -> b
  
instance BalancedTree Leaf where  
  fold l n Leaf = l
instance (BalancedTree t) => BalancedTree (Node t t) where
  fold l n (Node t1 a t2) = n (fold l n t1) a (fold l n t2)
    
data Tree a = forall t. BalancedTree t => Tree (t a)

zero' = Leaf
zero = Tree zero'

one' = Node Leaf 1 Leaf
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

height :: Tree a -> Int 
height (Tree t) = fold 0 (\x _ y -> x + 1) t

                    
{-
{-# LANGUAGE GADTs, DataKinds, ExistentialQuantification #-}        
-- Balanced trees with GADTs

data Nat = Z | S Nat

data Balanced h a where
  Leaf :: Balanced Z a
  Node :: Balanced h a -> a -> Balanced h a -> Balanced (S h) a
  
data Tree a = forall h. Tree (Balanced h a)

zero' = Leaf
zero = Tree zero'

one' = Node zero' 1 zero'
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

three' = Node two' 3 two' 
three = Tree three'
-}


