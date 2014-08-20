{-# LANGUAGE ExistentialQuantification, MultiParamTypeClasses, FlexibleInstances #-}        

-- Singleton version, w/type classes to make a unified type

-- However, there seem to be limitations on what we can do with this version of the type.

data Leaf a = Leaf
data Node t1 t2 a = Node (t1 a) a (t2 a)

class PerfectTree t where
  fold :: b -> (b -> a -> b -> b) -> t a -> b
  
instance PerfectTree Leaf where  
  fold l n Leaf = l
  
instance (PerfectTree t) => PerfectTree (Node t t) where
  fold l n (Node t1 a t2) = n (fold l n t1) a (fold l n t2)
  
data Tree a = forall t. PerfectTree t => Tree (t a)

zero' = Leaf
zero = Tree zero'

one' = Node Leaf 1 Leaf
one = Tree one'

two' = Node one' 2 one'
two = Tree two'

height :: Tree a -> Int 
height (Tree t) = fold 0 (\x _ _ -> x + 1) t

instance Show a => Show (Tree a) where
  show (Tree t) = fold "." 
    (\ t1 x t2 -> "("++ t1 ++ " " ++ show x ++ " " ++ t2 ++ ")") t

-- Oleg's challenge

next :: Tree Int -> Tree Int
next (Tree t) = Tree (Node t 0 t)

decr :: Tree a -> Tree a 
decr (Tree t) = undefined

  -- decr (Node (Node ll xl lr) xc (Node rl xr rr))) = Tree (Node ll xc rr)

merge :: Tree a -> Tree a -> Maybe a 
merge = undefined
