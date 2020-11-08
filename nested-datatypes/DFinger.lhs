Finger Trees Explained Anew, and Slightly Simplified (Functional Pearl)

This time, using GADTs instead of nested datatypes

> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeInType #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unticked-promoted-constructors #-}


> module Finger where
>
> import Prelude hiding (tail,head)
> import Nat


Two-Three Trees
---------------

We start by implementing 2-3 trees that statically track their height.  This
index ensures that the tree is balanced. All subtrees must have the exactly the
same height.

> -- A two-three tree of depth n
> -- NOTE: height 0 is just a single value
> data TwoThree n a where
>    Leaf :: a -> TwoThree Z a
>    Node :: Tuple (TwoThree n a) -> TwoThree (S n) a

> deriving instance Show a => Show (TwoThree n a)
> deriving instance Eq a => Eq (TwoThree n a)
> deriving instance Functor (TwoThree n)
> deriving instance Foldable (TwoThree n)
> deriving instance Traversable (TwoThree n)

> -- two or three values
> data Tuple a = Pair a a | Triple a a a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

Sequences / FingerTrees
-----------------------

We will use these 2-3 trees as the building block of FingerTrees. Here
the n parameter works in reverse: in each recursive call it tracks the
height of the 2-3 trees that are allowed at that level.

> -- still like a nested type --- number grows with each recursive use
> data Seq n a where
>    Nil  :: Seq n a
>    Unit :: TwoThree n a -> Seq n a
>    More :: Some (TwoThree n a) -> Seq (S n) a -> Some (TwoThree n a) -> Seq n a

> data Some a = One a | Two a a | Three a a a
>    deriving (Eq,Show,Functor,Foldable,Traversable)

> toList :: Some a -> [a]
> toList (One x) = [x]
> toList (Two x y) = [x, y]
> toList (Three x y z) = [x,y,z]


> head :: Seq Z a -> a 
> head Nil = error "no head"
> head (Unit (Leaf x)) = x
> head (More (One (Leaf x)) _ _ ) = x
> head (More (Two (Leaf x) _) _ _) = x
> head (More (Three (Leaf x) _ _) _ _) = x

> head23 :: Seq n a -> TwoThree n a
> head23 Nil = error "no head"
> head23 (Unit x) = x
> head23 (More (One x) _ _ ) = x
> head23 (More (Two x _) _ _) = x
> head23 (More (Three x _ _) _ _) = x

> cons :: TwoThree n a -> Seq n a -> Seq n a
> cons x Nil = Unit x
> cons x (Unit y) = More (One x) Nil (One y)
> cons x (More (One y) q u) = More (Two x y) q u
> cons x (More (Two y z) q u) = More (Three x y z) q u
> cons x (More (Three y z w) q u) = More (Two x y) (cons (Node (Pair z w)) q) u

>
> snoc :: Seq n a -> TwoThree n a -> Seq n a
> snoc Nil x = Unit x
> snoc (Unit y) x = More (One y) Nil (One x)
> snoc (More u q (One y)) x = More u q (Two y x) 
> snoc (More u q (Two y z)) x = More u q (Three y z x)
> snoc (More u q (Three y z w)) x = More u (snoc q (Node (Pair z w))) (Two y x)
> 
> 
> tail :: Seq n a -> Seq n a
> tail Nil = error "no tail"
> tail (Unit _) = Nil
> tail (More (Three _ x y) q u) = More (Two x y) q u
> tail (More (Two _ x) q u) = More (One x) q u
> tail (More (One _ ) q u) = more0 q u
>
> uncons :: Seq n a -> Maybe (TwoThree n a, Seq n a)
> uncons Nil = Nothing
> uncons (Unit y) = Just (y,Nil)
> uncons (More (Three w x y) q u) = Just (w, More (Two x y) q u)
> uncons (More (Two w x) q u) = Just (w,More (One x) q u)
> uncons (More (One w) q u) = Just (w, more0 q u)

> more0 :: Seq (S n) a -> Some (TwoThree n a) -> Seq n a
> more0 Nil (One y) = Unit y
> more0 Nil (Two y z) = More (One y) Nil (One z)
> more0 Nil (Three y z w) = More (One y) Nil (Two z w)
> more0 q u =
>   case uncons q of
>     Just (Node (Pair x y), tq) -> More (Two x y) tq u
>     Just (Node (Triple x _ _), _tq) -> More (One x) (map1 chop q) u
>        where
>          chop :: TwoThree n a -> TwoThree n a
>          chop (Node (Triple _ y z)) = Node (Pair y z)
>     Nothing -> error "impossible -- nil cases above" 
> {-
>   case head23 q of
>     Node (Pair x y) -> More (Two x y) (tail q) u
>     Node (Triple x _ _) -> More (One x) (map1 chop q) u -}
> 
> 
> toTuples :: [a] -> [Tuple a]
> toTuples [ ] = [ ]
> toTuples [x, y ] = [Pair x y ]
> toTuples [x, y, z, w] = [Pair x y, Pair z w]
> toTuples (x : y : z : xs) = Triple x y z : toTuples xs
>
> 
> glue :: Seq n a -> [ TwoThree n a ] -> Seq n a -> Seq n a
> glue Nil as q2 = foldr cons q2 as
> glue q1 as Nil = foldl snoc q1 as
> glue (Unit x) as q2 = foldr cons q2 (x : as)
> glue q1 as (Unit y) = foldl snoc q1 (as ++ [y ])
> glue (More u1 q1 v1) as (More u2 q2 v2) =
>   More u1
>   (glue q1
>    (map Node (toTuples (toList v1 ++ as ++ toList u2))) q2) v2
> 

> map1 :: (TwoThree n a -> TwoThree n a) -> Seq n a  -> Seq n a
> map1 _f Nil = Nil
> map1 f (Unit x) = Unit (f x)
> map1 f (More (One x) q u) = More (One (f x)) q u
> map1 f (More (Two x y) q u) = More (Two (f x) y) q u
> map1 f (More (Three x y z) q u) = More (Three (f x) y z) q u
> 
> instance Semigroup (Seq n a) where
>   q1 <> q2 = glue q1 [] q2

