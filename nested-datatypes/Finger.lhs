This code is directly taken from:

Claessen, Finger Trees Explained Anew, and Slightly Simplified (Functional Pearl)
Haskell Symposium 2020

> {-# LANGUAGE DeriveTraversable #-}
> module Finger where
>
> import Prelude hiding (tail,head)

> data Seq a = Nil | Unit a | More (Some a) (Seq (Tuple a)) (Some a)
> data Tuple a = Pair a a | Triple a a a 

> data Some a = One a | Two a a | Three a a a
>    deriving (Eq,Show, Foldable, Traversable, Functor)
>
> 
> toList :: Some a -> [a]
> toList (One x) = [x]
> toList (Two x y) = [x, y]
> toList (Three x y z) = [x,y,z]


> head :: Seq a -> a
> head Nil = error "no head"
> head (Unit a) = a
> head (More (One x) _ _ ) = x
> head (More (Two x _) _ _) = x
> head (More (Three x _ _) _ _) = x

> cons :: a -> Seq a -> Seq a
> cons x Nil = Unit x
> cons x (Unit y) = More (One x) Nil (One y)
> cons x (More (One y) q u) = More (Two x y) q u
> cons x (More (Two y z) q u) = More (Three x y z) q u
> cons x (More (Three y z w) q u) =
>   More (Two x y) (cons (Pair z w) q) u
> 
> snoc :: Seq a -> a -> Seq a
> snoc Nil x = Unit x
> snoc (Unit y) x = More (One y) Nil (One x)
> snoc (More u q (One y)) x = More u q (Two y x) 
> snoc (More u q (Two y z)) x = More u q (Three y z x)
> snoc (More u q (Three y z w)) x =
>   More u (snoc q (Pair z w)) (Two y x)
> 
> 
> tail :: Seq a -> Seq a
> tail Nil = error "no tail"
> tail (Unit _) = Nil
> tail (More (Three _ x y) q u) = More (Two x y) q u
> tail (More (Two _ x) q u) = More (One x) q u
> tail (More (One _ ) q u) = more0 q u
> 
> more0 :: Seq (Tuple a) -> Some a -> Seq a
> more0 Nil (One y) = Unit y
> more0 Nil (Two y z) = More (One y) Nil (One z)
> more0 Nil (Three y z w) = More (One y) Nil (Two z w)
> more0 q u =
>   case head q of
>     Pair x y -> More (Two x y) (tail q) u
>     Triple x _ _ -> More (One x) (map1 chop q) u
>        where chop (Triple _ y z) = Pair y z
>  
> toTuples :: [a] -> [Tuple a]
> toTuples [ ] = [ ]
> toTuples [x, y ] = [Pair x y ]
> toTuples [x, y, z, w] = [Pair x y, Pair z w]
> toTuples (x : y : z : xs) = Triple x y z : toTuples xs
> 
> glue :: Seq a -> [a] -> Seq a -> Seq a
> glue Nil as q2 = foldr cons q2 as
> glue q1 as Nil = foldl snoc q1 as
> glue (Unit x) as q2 = foldr cons q2 (x : as)
> glue q1 as (Unit y) = foldl snoc q1 (as ++ [y ])
> glue (More u1 q1 v1) as (More u2 q2 v2) =
>   More u1
>   (glue q1
>    (toTuples (toList v1 ++ as ++ toList u2)) q2) v2
>
> map1 :: (a -> a) -> Seq a -> Seq a
> map1 f (Unit x) = Unit (f x)
> map1 f (More (One x) q u) = More (One (f x)) q u
> map1 f (More (Two x y) q u) = More (Two (f x) y) q u
>
> 
> instance Semigroup (Seq a) where
>   q1 <> q2 = glue q1 [] q2

