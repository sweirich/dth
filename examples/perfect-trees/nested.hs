{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

-- Perfect trees with nested datatypes
import Data.Monoid

-- definition of the datatype
data Z a = Leaf
data S t a = Node (t a) a (t a)
data Nested t a = Z (t a) | S (Nested (S t) a)

type Tree a = Nested Z a

-- some example trees

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
-- CPS programming is getting old.
merge :: Monoid a => Tree a -> Tree a -> Maybe (Tree a) 
merge t1 t2 = merge1 t1 t2 (\Leaf Leaf -> Leaf)

merge1 :: Monoid a =>  Nested s a -> Nested s a -> 
          (s a -> s a -> s a) -> Maybe (Nested s a)
merge1 (Z t1) (Z t2) f = Just (Z (f t1 t2))
merge1 (S t1) (S t2) f = do 
   t <- merge1 t1 t2 
         (\ (Node ll lx lr) (Node rl rx rr) -> 
              Node (f ll rl) (mappend lx rx) (f lr rr))
   return (S t)
merge1 (Z _) _ f = Nothing
merge1 (S _) _ f = Nothing

