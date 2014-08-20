{-# LANGUAGE ExistentialQuantification, GADTs, TypeFamilies, DataKinds #-}        

-- GADT-based singleton version, w/ a closed type family used as a predicate
-- on the type-level reflection of the runtime shape of the tree

-- data Leaf a = Leaf
-- data Node t1 t2 a = Node (t1 a) a (t2 a)


data TreeShape = LeafShape | NodeShape TreeShape TreeShape

data Tree (t :: TreeShape) (a :: *) :: * where
  Leaf :: Tree LeafShape a
  Node :: Tree l a -> a -> Tree r a -> Tree (NodeShape l r) a

type family Perfect (t :: TreeShape) :: Bool where
    Perfect LeafShape       = True     
    Perfect (NodeShape l l) = True    -- require left and right to have same shape
    Perfect (NodeShape l r) = False

    
data PerfectTree (a :: *) = forall (t :: TreeShape). (Perfect t ~ True) => Tree (Tree t a)

zero' = Leaf
zero = Tree zero'

one' = Node Leaf 1 Leaf
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

height :: PerfectTree a -> Int 
height (Tree t) = ht t where
  ht :: Tree t a -> Int
  ht Leaf = 0
  ht (Node l x r) = ht l

-- Oleg's challenge

decr :: PerfectTree a -> PerfectTree a 
decr (Tree (Node (Node ll xl lr) xc (Node rl xr rr))) = undefined
 -- can't propagate info backwards
 ---Tree (Node ll xc rr)

next :: PerfectTree Int -> PerfectTree Int
next (Tree t) = Tree (Node t 0 t)

merge :: PerfectTree a -> PerfectTree a -> Maybe a 
merge = undefined
