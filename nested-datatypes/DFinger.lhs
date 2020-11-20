This module is inspired by 

   Claessen, Finger Trees Explained Anew, and Slightly Simplified (Functional Pearl)
   Haskell Symposium 2020

It is a reinterpretation of the FingerTree data structure using GADTs in place of nested datatypes.

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


> module DFinger where
>
> import Prelude hiding (tail,head)
> import Data.Kind (Type)
> import Nat hiding (Some)

Two-Three Trees
---------------

We start by implementing 2-3 trees that statically track their height.  This
index ensures that the tree is balanced. All subtrees must have the exactly the
same height.

> -- two or three values
> data Tuple a = Pair a a | Triple a a a
>   deriving (Eq, Show, Functor, Foldable, Traversable)

> -- A two-three tree of height n, with values of type a at the leaves
> data TwoThree n a where
>    Leaf :: a -> TwoThree Z a
>    Node :: Tuple (TwoThree n a) -> TwoThree (S n) a

> deriving instance Show a => Show (TwoThree n a)
> deriving instance Eq a => Eq (TwoThree n a)
> deriving instance Functor (TwoThree n)
> deriving instance Foldable (TwoThree n)
> deriving instance Traversable (TwoThree n)

NOTE: height 0 is just a single value.

Sequences / FingerTrees
-----------------------

We will use these 2-3 trees as the building block of FingerTrees. Here the `n`
parameter works in reverse of the 2-3 trees above: in each recursive call it
increases, allowing each subsequent level to use larger 2-3 trees.

> data Seq (n :: Nat) (a :: Type) where
>    Nil  :: Seq n a
>    Unit :: TwoThree n a -> Seq n a
>    More :: Some n a -> Seq (S n) a -> Some n a -> Seq n a

> deriving instance Show a => Show (Seq n a)
> deriving instance Eq a => Eq (Seq n a)
> deriving instance Functor (Seq n)
> deriving instance Foldable (Seq n)
> deriving instance Traversable (Seq n)


I've modified the `Some` datatype to a use Tuple instead of having a separate
Two/Three constructors.  It doesn't add any clarity to this file.

> data Some n a =
>     One (TwoThree n a)
>   | Bump (Tuple (TwoThree n a))
>       deriving (Eq,Show,Functor,Foldable,Traversable)



> head :: Seq n a -> TwoThree n a
> head Nil = error "no head"
> head (Unit x) = x
> head (More (One x) _ _ ) = x
> head (More (Bump (Pair x _)) _ _) = x
> head (More (Bump (Triple x _ _)) _ _) = x

> tail :: Seq n a -> Seq n a
> tail Nil = error "no tail"
> tail (Unit _) = Nil
> tail (More (Bump (Triple _ x y)) q u) = More (Bump (Pair x y)) q u
> tail (More (Bump (Pair _ x)) q u) = More (One x) q u
> tail (More (One _ ) q u) = more0 q u
>
> more0 :: Seq (S n) a -> Some n a -> Seq n a
> more0 Nil (One y) = Unit y
> more0 Nil (Bump (Pair y z)) = More (One y) Nil (One z)
> more0 Nil (Bump (Triple y z w)) = More (One y) Nil (Bump (Pair z w))
> more0 q u =
>   case uncons q of
>     Just (Node (Pair x y), tq) -> More (Bump (Pair x y)) tq u
>     Just (Node (Triple x _ _), _tq) -> More (One x) (map1 chop q) u
>        where
>          chop :: TwoThree n a -> TwoThree n a
>          chop (Node (Triple _ y z)) = Node (Pair y z)
>     Nothing -> error "impossible -- nil cases above" 

> map1 :: (TwoThree n a -> TwoThree n a) -> Seq n a  -> Seq n a
> map1 _f Nil = Nil
> map1 f (Unit x) = Unit (f x)
> map1 f (More (One x) q u) = More (One (f x)) q u
> map1 f (More (Bump (Pair x y)) q u) = More (Bump (Pair (f x) y)) q u
> map1 f (More (Bump (Triple x y z)) q u) = More (Bump (Triple (f x) y z)) q u

> -- | Safer combination of head/tail
> -- is there a better way to extract elements that doesn't rely on 'map1' and 'chop'?
> -- the code above seems a bit clunky
> uncons :: Seq n a -> Maybe (TwoThree n a, Seq n a)
> uncons Nil = Nothing
> uncons (Unit y) = Just (y,Nil)
> uncons (More (Bump (Triple w x y)) q u) = Just (w, More (Bump (Pair x y)) q u)
> uncons (More (Bump (Pair w x)) q u) = Just (w, More (One x) q u)
> uncons (More (One w) q u) = Just (w, more0 q u)


> -- add to the front
> cons :: TwoThree n a -> Seq n a -> Seq n a
> cons x Nil = Unit x
> cons x (Unit y) = More (One x) Nil (One y)
> cons x (More (One y) q u) = More (Bump (Pair x y)) q u
> cons x (More (Bump (Pair y z)) q u) = More (Bump (Triple x y z)) q u
> cons x (More (Bump (Triple y z w)) q u) = More (Bump (Pair x y)) (cons (Node (Pair z w)) q) u

> -- add to the back
> snoc :: Seq n a -> TwoThree n a -> Seq n a
> snoc Nil x = Unit x
> snoc (Unit y) x = More (One y) Nil (One x)
> snoc (More u q (One y)) x = More u q (Bump (Pair y x))
> snoc (More u q (Bump (Pair y z))) x = More u q (Bump (Triple y z x))
> snoc (More u q (Bump (Triple y z w))) x = More u (snoc q (Node (Pair z w))) (Bump (Pair y x))


> -- | This part isn't so much fun. Why do we need a list? what is the invariant about
> -- the number of elements in the list that is passed to 'glue'? Could it grow arbitrarily large?
> 
> toTuples :: [a] -> [Tuple a]
> toTuples [ ] = [ ]
> toTuples [x, y] = [Pair x y ]
> toTuples [x, y, z, w] = [Pair x y, Pair z w]
> toTuples (x : y : z : xs) = Triple x y z : toTuples xs
>
> toList :: Some n a -> [TwoThree n a]
> toList (One x) = [x]
> toList (Bump (Pair x y)) = [x, y]
> toList (Bump (Triple x y z)) = [x,y,z]

> glue :: Seq n a -> [ TwoThree n a ] -> Seq n a -> Seq n a
> glue Nil as q2 = foldr cons q2 as
> glue q1 as Nil = foldl snoc q1 as
> glue (Unit x) as q2 = foldr cons q2 (x : as)
> glue q1 as (Unit y) = foldl snoc q1 (as ++ [y])
> glue (More u1 q1 v1) as (More u2 q2 v2) =
>   More u1 (glue q1 (map Node (toTuples (toList v1 ++ as ++ toList u2))) q2) v2

> 
> instance Semigroup (Seq n a) where
>   q1 <> q2 = glue q1 [] q2

