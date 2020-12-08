{-# LANGUAGE ExistentialQuantification, GADTs, TypeFamilies, DataKinds #-}        

module ConstraintTF where
  
-- GADT-based version, w/ a closed type family used as a predicate
-- on the type-level reflection of the runtime shape of the tree

-- with code from Danial Winograd-Cort

import Data.Kind (Constraint)


data TreeShape = LeafShape | NodeShape TreeShape TreeShape

data Tree (t :: TreeShape) (a :: *) :: * where
  Leaf :: Tree LeafShape a
  Node :: Tree l a -> a -> Tree r a -> Tree (NodeShape l r) a

type family Perfect (t :: TreeShape) :: Constraint where
    Perfect LeafShape       = ()
    Perfect (NodeShape l r) = (l ~ r, Perfect l)
    -- require left and right to have same shape
        
data PerfectTree (a :: *) = forall (t :: TreeShape). (Perfect t) => Tree (Tree t a)

zero' = Leaf
zero = Tree zero'

one' = Node Leaf 1 Leaf
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

bad' = Node one' 2 zero'
-- Doesn't typecheck
-- bad = Tree $ Node bad' 3 bad'

height :: PerfectTree a -> Int 
height (Tree t) = ht t where
  ht :: Tree t a -> Int
  ht Leaf = 0
  ht (Node l x r) = 1 + ht l

decr :: PerfectTree a -> PerfectTree a
decr (Tree (Node (Node ll xl lr) xc (Node rl xr rr))) = Tree $ Node ll xc lr
decr (Tree Leaf) = Tree Leaf

merge :: forall a. Semigroup a => PerfectTree a -> PerfectTree a -> Maybe (PerfectTree a)
merge (Tree t1) (Tree t2) = Tree <$> go t1 t2
  where
    go :: (Perfect t1, Perfect t2, Semigroup a) =>
         Tree t1 a -> Tree t2 a -> Maybe (Tree t1 a)
    go Leaf Leaf = Just Leaf
    go (Node ll xl lr) (Node rl xr rr) = do
      l <- go ll rl
      r <- go lr rr
      pure $ Node l (xl <> xr) r
    go _ _ = Nothing


