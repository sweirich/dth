
Do we need nested datatypes?
============================

I always find nested datatypes a bit mysterious (and their types a bit
misleading). This module is my attempt to understand them a bit more
clearly, by comparing them against indexed types.

More specifically, this module compares two implementations of *perfect*
trees, where the type system forces each instance of a tree-like data
structure to have exactly `2^n` nodes.

Warning: this module uses some *fancy* types.

> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unticked-promoted-constructors #-}

> module Nested where
> 
> import Prelude hiding (head, tail, Double)
> import Data.Kind (Type)
> import Control.Monad (ap)
> import Data.Type.Equality
> import Data.Some

The code in this file relies on the 'Two' data structure. This data structure
contains *exactly* two elements of the same type.

> data Two a = Two a a
>    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

A lot of examples of nested datatypes use the type `(a,a)` instead of
  `Two`. However, it is convenient in modern Haskell to have the appropriate
definition of `fmap` etc. available. 

Regular datatypes
-----------------

Nested datatypes allow polymorphic datatypes to use non-regular recursion. In
a *regular* datatype, all recursive uses of the type parameter must be the
same. For example, this definition of a binary tree has a recursive use of
the `Tree` type, where the type parameter is `a`.

> data Tree (a :: Type)
>   = Leaf a
>   | Node (Two (Tree a))
>      deriving (Eq,Ord,Show, Functor, Foldable, Traversable)

Here are some example trees

> t1 :: Tree Int
> t1 = Leaf 1

> t2 :: Tree Int
> t2 = Node (Two (Leaf 1) (Leaf 2))

> t3 :: Tree Int
> t3 = Node (Two (Node (Two (Leaf 1) (Leaf 2))) (Leaf 3))

This sort of tree can store any number of elements, in lots of different
shapes. We can also automatically derive instances for a number of common
Haskell type classes for this type.
 


Nested datatypes
----------------

In contrast, a *nested* datatype uses a different argument to `Tree` in the
recursive calls. For example, what happens if we say that the `Node`
constructor carries a tree of two values instead of two trees.

> data NTree (a :: Type) =
>     NLeaf a
>   | NNode (NTree (Two a))
>       deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

Here are some example trees:

> n1 :: NTree Int
> n1 = NLeaf 1
>
> n2 :: NTree Int
> n2 = NNode (NLeaf (Two 1 2))
>
> n3 :: NTree Int
> n3 = NNode (NNode (NLeaf (Two (Two 1 2) (Two 3 4))))

Notice that these "Trees" are all perfect trees. Each tree stores 2^n
elements, where n is the number of uses of the `NNode` constructor.  Even
though the datatype itself doesn't look much like a tree (there is only one
recursive call), we still get a tree structure due to the use of the
pairing. And, that tree structure is highly constrained.

Note especially that the "prefix" of these values i.e. the sequence of `NNode`
and `NLeaf` constructors codes the height of the perfect tree in unary
notation. i.e. `NLeaf` is 0, `NNode . NLeaf` is `, `NNode . NNode . NLeaf` is
2, etc.


The same type classes are derivable as before and if you were to implement
 them by hand, the code you write would be identical. 

However, there is one important difference in these definitions: nested data
 types require *polymorphic recursion*.

In a regular datatype, recursive calls to polymorphic functions are at exactly the
same type parameter. Here is the mapping function for regular trees, where I've
used scoped type variables and type applications to annotate the instantiation of
the recursive call. 

> tmap :: forall a b. (a -> b) -> (Tree a -> Tree b)
> tmap f (Leaf x) = Leaf (f x)
> tmap f (Node z) = Node (fmap (tmap @a @b f) z)

Even without the type signature (and type applications), this code would still
type check. Recursive functions over regular datatypes is well-within the
purview of HM type inference.

However, here is the implementation of the mapping function for the nested
 datatype version. Note that in this case, the recursive call to `ntmap` is
not `a` and `b`, but at `Two a` and `Two b`. 

> ntmap :: forall a b. (a -> b) -> (NTree a -> NTree b)
> ntmap f (NLeaf x) = NLeaf (f x)
> ntmap f (NNode z) = NNode (ntmap @(Two a) @(Two b) (fmap f) z)

In the absence of type annotations, like the definition of `ntmap` above, HM +
polymorphic recursion is undecidable [1][2]. If we remove the type
annotation, then we get an error message from GHC:

     nested.lhs:(118,3)-(119,44): error: …
         • Occurs check: cannot construct the infinite type: t ~ f t
           Expected type: (f t -> f b) -> NTree (Two t) -> NTree (Two b)
             Actual type: (t -> b) -> NTree t -> NTree b
         • Relevant bindings include
             tmap :: (f t -> f b) -> NTree (Two t) -> NTree (Two b)
               (bound at /Users/sweirich/github/dth/nested-datatypes/nested.lhs:118:3)
         |
     Compilation failed.

In the presence of the type annotation, though, polymporphic recursion is not
problemmatic and the Haskell 98 report specifically states that type
signatures can be used to support polymorphic recursion [3].

Indexed datatypes
-----------------

One thing that always puzzles me is that the parameter to `NTree` does
double-duty. It constrains the shape of the type *and* paramterizes the type
of data stored in the tree. If I were to write down a type of perfect trees
from scratch, using much more recent features of GHC, this is what I would
write.

First, let's define some natural numbers so that we can count.

> data Nat = S Nat | Z 

Now, let's index the tree by its height and require that both subtrees in a
node have the same height. 

> data DTree (n :: Nat) (a :: Type) where
>   DLeaf :: a -> DTree 'Z a
>   DNode :: Two (DTree n a) -> DTree ('S n) a

In this case, our tree datatype is now a GADT --- the result types of the leaf
and node data constructors differ in the height index. I tend to follow the
terminology of Coq and call `n` a type *index* (because it varies in the
result type) and `a` a type *parameter* (because it does not).

Because `DTree` is a GADT, we have to use standalone deriving for the
instances above. 

> deriving instance Show a => Show (DTree n a)
> deriving instance Eq a => Eq (DTree n a)
> deriving instance Ord a => Ord (DTree n a)
> deriving instance Functor (DTree n)
> deriving instance Foldable (DTree n)
> deriving instance Traversable (DTree n)

The height "leaks" into the tree type. Therefore, to define the equivalent
type, we need to also use an existential type to hide the index. For
convenience we also include a singleton type to have a runtime witness for
that height. (This singleton corresponds to the height prefix on the nested
tree.)

> data SNat a where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

> deriving instance Show (SNat n)

> data Perfect a = forall n. Perfect (SNat n) (DTree n a) 

> deriving instance Show a => Show (Perfect a)
> deriving instance Functor Perfect
> deriving instance Foldable Perfect
> deriving instance Traversable Perfect


Note: we can already see one cost to our GADT-based approach. The derived
 implementations of `Eq` and `Ord` don't type check for `Perfect` trees.

> -- deriving instance Eq a => Eq (Perfect a)
> -- deriving instance Ord a => Ord (Perfect a)

We can see the problem by looking at the error message for this attempt:

> -- treeEq :: Eq a => Perfect a -> Perfect a -> Bool
> -- treeEq (Perfect _ t1) (Perfect _ t2) = t1 == t2

The two `DTree`s have potentially different height parameters, so we cannot
 use our derived equality function for `DTree`s.

There are two ways we could implement equality for Perfect trees. The
first is to first make sure that the two trees are the same size before
comparison. We can do this by checking if their height parameters are
the same.

> instance TestEquality SNat where
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

> instance Eq a => Eq (Perfect a) where
>    Perfect n1 t1 == Perfect n2 t2 =
>      case testEquality n1 n2 of
>        Just Refl -> t1 == t2   -- now we know t1 and t2 have the same height
>        Nothing   -> False


Alternatively, we could define a heterogenous equality for `DTree`s and ignore
  the height parameter altogether.

> class Heq a b where
>    heq :: a -> b -> Bool
> instance Heq a b => Heq (Two a) (Two b) where
>    heq (Two x y) (Two z w) = heq x z && heq y w
> instance Eq a => Heq (DTree n a) (DTree m a) where
>    heq (DLeaf x) (DLeaf y)   = x == y
>    heq (DNode p1) (DNode p2) = heq p1 p2
>    heq _ _ = False

> peq :: Eq a => Perfect a -> Perfect a -> Bool
> peq (Perfect _ t) (Perfect _ u) = heq t u

Now, here are the examples. They look a lot more like the first tree type
than the second.

> d1 :: DTree 'Z Int
> d1 = DLeaf 1

> d2 :: DTree ('S 'Z) Int
> d2 = DNode (Two (DLeaf 1) (DLeaf 2))

> -- not perfect, doesn't type check
> -- d3 = DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2))) (DLeaf 3))
>
> d4 :: DTree ('S ('S 'Z)) Int
> d4 = DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2)))
>                 (DNode (Two (DLeaf 3) (DLeaf 4))))

We can use the same definitions, once again, for our common instances.  This
time, we are using polymorphic recursion in the natural number, not in the
two type parameters.

> dtmap :: forall n a b. (a -> b) -> (DTree n a -> DTree n b)
> dtmap f (DLeaf x) = DLeaf (f x)
> dtmap f (DNode (z :: Two (DTree m a)))
>    = DNode (fmap (dtmap @m @a @b f) z)


Comparison
==========

How do `NTree` and `DTree`/`Perfect` compare? 

Can we do the same thing with both trees?

But can you invert that tree?
-----------------------------

Ok, let's mirror our trees. I don't know why you would want to do this. But it seems important.

Here's our basic building block. Swap the components of the Pair.

> swap :: Two a -> Two a
> swap (Two x y) = Two y x

For perfect trees, we rely on a helper function that tells us that inverting the tree preserves
its height. That's essential, because we reuse the same height when we package up the result.

> invertPerfect :: Perfect a -> Perfect a
> invertPerfect (Perfect n t) = Perfect n (invert t) where
>    invert :: DTree n a -> DTree n a
>    invert (DLeaf x) = DLeaf x
>    invert (DNode p) = DNode (swap (fmap invert p))

This code is roughly the same as the code for inverting regular trees.

Inverting nested trees is slightly trickier. 

> invertNTree :: NTree a -> NTree a
> invertNTree = go id where
>   go :: (a -> a) -> NTree a -> NTree a
>   go f (NLeaf x) = NLeaf (f x)
>   go f (NNode x) = NNode (go (swap . fmap f) (invertNTree x))

With every recursive  call, we need to construct a  new "inversion function" f
 that we use to invert the entire tree in one go in the leaf case.

Tree replication
----------------

Given some height n, and some value x, generate a perfect tree containing 2^n copies of x.

> replicateTree :: a -> Int -> Tree a
> replicateTree x = go where
>   go 0 = Leaf x
>   go m = Node (Two (go (m-1)) (go (m-1)))

For Nested trees

> replicateNTree :: a -> Int -> NTree a
> replicateNTree = go where
>   go :: forall a. a -> Int -> NTree a
>   go a 0 = NLeaf a
>   go a m = NNode (go (Two a a) (m - 1))


> fromInt :: Int -> Some SNat
> fromInt 0 = Some $ SZ
> fromInt n = case (fromInt (n-1)) of
>   Some sn -> Some $ SS sn

> replicatePerfect :: a -> Int -> Perfect a
> replicatePerfect x i = case fromInt i of
>     Some n -> Perfect n (go x n)
>       where
>         go :: a -> SNat n -> DTree n a
>         go x SZ     = DLeaf x
>         go x (SS m) = DNode (Two (go x m) (go x m))

Applicative and Monad
---------------------

The standard instance the Monad type class for trees is in terms of "grafting"
 best expressed by the `join` operation.

> join :: Tree (Tree a) -> Tree a
> join (Leaf t) = t
> join (Node (Two t1 t2)) = Node (Two (join t1) (join t2))

With this definition, we can give straightforward instances for Applicative
 and Monad classes.

> instance Monad Tree where
>   return = Leaf
>   xs >>= f = join (fmap f xs)
> instance Applicative Tree where
>   pure = return
>   (<*>) = ap

However, we can't do the same thing for the `NTree` or `Perfect` types. Think about what
grafting means in this case:

< njoin :: NTree (NTree a) -> NTree a

This is only successful if all of the embedded trees are the same height ---
 if they are different from eachother, then we get non-perfect trees.

Our `DTree` type can talk about joining together trees that are all the same shape.
But in this case, while we get a new perfect tree, it doesn't have the same height as the
original.

> djoin :: DTree n (DTree m a) -> DTree (Add n m) a
> djoin (DLeaf t) = t
> djoin (DNode (Two t1 t2)) = DNode (Two (djoin t1) (djoin t2))

> type family Add n m where
>   Add Z m  = m
>   Add (S n) m = S (Add n m)

Maybe there is a different interpretation of the `Applicative` and `Monad`
 type classes for `DTree`s?

For Applicatives, we can use the `ZipList` interpretation.

> class INat n where inat :: SNat n
> instance INat Z where inat = SZ
> instance INat n => INat (S n) where inat = SS inat
 
> instance INat n => Applicative (DTree n) where
>   pure x = go x inat where
>     go :: forall a n. a -> SNat n -> DTree n a
>     go x SZ = DLeaf x
>     go x (SS m) = DNode (Two (go x m) (go x m))
>   f <*> t = go f t where
>     go :: forall n a b. DTree n (a -> b) -> DTree n a -> DTree n b
>     go (DLeaf f) (DLeaf x) = DLeaf (f x)
>     go (DNode (Two t1 t2)) (DNode (Two u1 u2)) =
>       DNode (Two (go t1 u1) (go t2 u2))


But the type doesn't give us enough flexibility for a `Monad` instance.


Converting between representations
----------------------------------

We can, with effort, convert a `NTree` to a `Perfect` tree. And we can, with
 effort, convert a `Perfect` tree to a `NTree`.

Both of these conversions require the use of an auxiliary data structure that
captures a "decomposed" nested tree. i.e. one where we have eliminated unary
encoded prefix into a runtime natural number (i.e. `SNat`) and only have the
nesting of the `Two` data structure.

> data HT a where
>   HT :: SNat n -> NTwo n a -> HT a

> type family NTwo n a where
>   NTwo Z     a = a
>   NTwo (S n) a = NTwo n (Two a)

> n2p :: NTree a -> Perfect a
> n2p nt = case n2ht nt of
>           HT n s -> Perfect n (ht2d n s)

> -- | decompose the prefix find out the height of the perfect tree
> n2ht :: NTree a -> HT a 
> n2ht (NLeaf a) = HT SZ a
> n2ht (NNode t) = case n2ht t of
>   HT m p -> HT (SS m) p
>
> -- | take the tree structure itself and convert it to the indexed version
> ht2d :: SNat n -> NTwo n a -> DTree n a
> ht2d SZ a = DLeaf a
> ht2d (SS m) p = DNode (dsplit (ht2d m p))
>   where
>     dsplit :: DTree n (Two a) -> Two (DTree n a)
>     dsplit (DLeaf (Two x y))   = Two (DLeaf x) (DLeaf y)
>     dsplit (DNode (Two t1 t2)) = Two (DNode (Two t1a t2a)) (DNode (Two t1b t2b))
>        where
>          (Two t1a t1b) = dsplit t1
>          (Two t2a t2b) = dsplit t2
>

> p2n :: Perfect a -> NTree a
> p2n (Perfect n dt) = ht2n (HT n (d2ht dt))
>
> ht2n :: forall a. HT a -> NTree a
> ht2n (HT SZ x) = NLeaf x
> ht2n (HT (SS m) x) = NNode (ht2n (HT m x))

> d2ht :: forall n a. DTree n a -> NTwo n a
> d2ht (DLeaf a) = a
> d2ht (DNode (Two p1 p2)) = d2ht (dmerge p1 p2)
>   where
>     dmerge :: forall n a. DTree n a -> DTree n a -> DTree n (Two a)
>     dmerge (DLeaf x) (DLeaf y) = DLeaf (Two x y)
>     dmerge (DNode (Two t1a t1b)) (DNode (Two t2a t2b)) =
>          DNode (Two (dmerge t1a t2a) (dmerge t1b t2b))

Due to the need for `dsplit` and `dmerge`, both of these operations take
longer than we might like. The ideal would be `O (n + log n)`, which is just `O(n)`.
But instead we get `O (n log n)`.

Parse, don't validate
---------------------

Can we write functions that validate a perfect `Tree` as an `NTree` or as
a `DTree`?

> -- Validation function, check that the input is a
> -- valid tree using the smart constructors of the class
> toNTree :: Tree a -> Maybe (NTree a)
> toNTree (Leaf x) = return (NLeaf x)
> toNTree (Node p) = traverse toNTree p >>= node where
>   node (Two n1 n2) = NNode <$> merge n1 n2 where
>     merge :: NTree a -> NTree a -> Maybe (NTree (Two a))
>     merge (NLeaf x) (NLeaf y) = pure (NLeaf (Two x y))
>     merge (NNode x) (NNode y) = NNode <$> merge x y
>     merge _ _ = Nothing

> fromNTree :: NTree a -> Tree a
> fromNTree (NLeaf x) = Leaf x
> fromNTree (NNode p) = Node (fromNTree <$> split p) where
>     split :: NTree (Two a) -> Two (NTree a)
>     split (NLeaf p) = NLeaf <$> p
>     split (NNode p) = NNode <$> split p

Again, for nested type we have operations that are 


For our GADT-based approach, the instance is much more straightforward.


> toPerfect :: Tree a -> Maybe (Perfect a)
> toPerfect (Leaf x) = return (Perfect SZ (DLeaf x))
> toPerfect (Node p) = traverse toPerfect p >>= node where
>    node :: Two (Perfect a) -> Maybe (Perfect a)
>    node (Two (Perfect n1 u1) (Perfect n2 u2)) = do
>      Refl <- testEquality n1 n2
>      return $ Perfect (SS n1) (DNode (Two u1 u2))
>
> fromPerfect :: Perfect a -> Tree a
> fromPerfect (Perfect _ t) = fromDTree t where
>      fromDTree :: DTree n a -> Tree a
>      fromDTree (DLeaf x) = Leaf x
>      fromDTree (DNode p) = Node (fromDTree <$> p)

Conclusion
----------

This is about as far as we can go with a comparison between perfect
trees. They're fairly constrained datatypes, so there isn't all that much
you can do with them. From my point of view, I find the indexed version of
the datastructure a bit easier to understand because we don't need to use
polymorphic recursion. However, maybe that is because I am already familiar
with the patterns of DependentHaskell. If you are the opposite, perhaps this
explanation will serve as a Rosetta stone.


[1]: Fritz Henglein, Type Inference with Polymorphic Recursion.
ACM Transactions on Programming Languages and Systems. Vol 15, Issue 2. April 1993.
[2]: Assaf J Kfoury, Jerzy  Tiuryn, Paweł Urzyczyn. Type reconstruction in the presence of polymorphic recursion. ACM Transactions on Programming Languages and Systems. Vol 15, Issue 2. April 1993.
[3]: https://www.haskell.org/onlinereport/decls.html#type-signatures
