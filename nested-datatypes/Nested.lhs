title: Do we need nested datatypes?

Constraining the Shape of Data via Types
========================================

I always find nested datatypes a bit mysterious and their types a bit
misleading. This module is my attempt to understand them a bit more clearly,
by comparing them against similar structures implemented by indexed types.

More specifically, this module compares several implementations of *perfect*
trees, where the type system forces each instance of a tree-like data
structure to have exactly `2^n` nodes.

Warning: this module uses some *fancy* types.

> {-# LANGUAGE AllowAmbiguousTypes #-}
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
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE UndecidableInstances #-}

> {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unticked-promoted-constructors #-}

> module Nested where
> 
> import Prelude hiding (head, tail, Double)
> import Data.Kind (Type)
> import Control.Monad (ap)
> import Data.Type.Equality
> import Data.Some

Auxiliary type: Two
-------------------

A brief digression before we get started. The examples here rely on
the 'Two' data structure. This data structure contains *exactly* two elements
of the same type. There is not anything special about it -- we'll just use it
to make the comparison between various versions easier to see.

> data Two a = Two a a
>    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

Many examples of nested datatypes, especially for perfect trees, use the type
`(a,a)` instead of `Two`. However, it is convenient in modern Haskell to
 have the appropriate definitions of `fmap` etc. available for this
auxiliary type.

Regular datatypes
-----------------

Nested datatypes allow polymorphic datatypes to use non-regular recursion. So,
before we talk about what they are, let's talk about what they are not. In a
*regular* datatype, all recursive uses of the type parameter must be the
same.

For example, this definition of a binary tree has a recursive use of the
 `Tree` type where the type parameter is `a`.

> data Tree (a :: Type) 
>   = Leaf a
>   | Node (Two (Tree a))
>      deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

Here are some example trees

> t1 :: Tree Int
> t1 = Leaf 1

> t2 :: Tree Int
> t2 = Node (Two (Leaf 1) (Leaf 2))

> t3 :: Tree Int
> t3 = Node (Two (Node (Two (Leaf 1) (Leaf 2))) (Leaf 3))

This sort of tree can store any number of elements, in lots of different
shapes. 
 
Nested datatypes
----------------

In contrast, a *nested* datatype uses a different argument to `Tree` in the
 recursive calls. For example, what happens if we say that the `Node`
 constructor carries a tree of two values instead of two values that are
 trees?

> data NTree (a :: Type) =
>     NLeaf a
>   | NNode (NTree (Two a))
>       deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

Here are some example nested trees:

> n1 :: NTree Int
> n1 = NLeaf 1
>
> n2 :: NTree Int
> n2 = NNode (NLeaf (Two 1 2))
>
> n3 :: NTree Int
> n3 = NNode (NNode (NLeaf (Two (Two 1 2) (Two 3 4))))

These "Trees" are all perfect trees. Each tree stores exactly `2^n` elements,
  where `n` is the number of uses of the `NNode` constructor.  Even though the
  datatype itself doesn't look much like a tree (there is only one recursive
  call), we still get a tree structure due to the use of the pairing in the
  `Two` datatype. And, that tree structure is highly constrained.

Note especially that the "prefix" of these values i.e. the sequence of `NNode`
 and `NLeaf` constructors codes the height of the perfect tree in unary
 notation. i.e. `NLeaf` is 0, `NNode . NLeaf` is 1, and `NNode . NNode
 . NLeaf` is 2, etc.


The same type classes (e.g. `Eq`, `Functor`, etc) are derivable as before and
if you were to implement them by hand, the code you write would be
identical.

However, there is one important difference in these derived definitions: nested data
 types require *polymorphic recursion*.

In a regular datatype, recursive calls to polymorphic functions are use
 exactly the same type parameter. For example, here is the definition of
 `fmap` for regular trees, where I've used scoped type variables and type
 applications to annotate the instantiation of the recursive call.

> tmap :: forall a b. (a -> b) -> (Tree a -> Tree b)
> tmap f (Leaf x) = Leaf (f x)
> tmap f (Node z) = Node (fmap (tmap @a @b f) z)

Even without the type signature (and type applications), this code would still
type check. Recursive functions over regular datatypes are well-within the
purview of HM type inference.

However, here is the implementation of the mapping function for the nested
 datatype version. Note that in this case, the recursive call to `ntmap` uses
not `a` and `b`, but `Two a` and `Two b`. 

> ntmap :: forall a b. (a -> b) -> (NTree a -> NTree b)
> ntmap f (NLeaf x) = NLeaf (f x)
> ntmap f (NNode z) = NNode (ntmap @(Two a) @(Two b) (fmap f) z)

In the absence of type annotations, like the definition of `ntmap` above, HM +
polymorphic recursion is undecidable [1][2]. Accordingly, if we remove the type
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
problemmatic and has been a part of Haskell for years. The Haskell 98 report
specifically states that type signatures can be used to support polymorphic
recursion [3].

Indexed datatypes
-----------------

One thing that always puzzles me is that the parameter to `NTree` does
double-duty. It both constrains the shape of the type *and* paramterizes the type
of data stored in the tree. If I were to write down a type of perfect trees
from scratch, using much more recent features of GHC, this is what I would
write.

First, let's define some natural numbers so that we can count.

> data Nat = S Nat | Z 

Now, let's index the tree by its height and require that both subtrees in a
node have the same height. We'll use datatype promotion with our GADT so that
we can refer to natural numbers in types.

> data ITree (n :: Nat) (a :: Type) where
>   DLeaf :: a -> ITree 'Z a
>   DNode :: Two (ITree n a) -> ITree ('S n) a

In this case, our tree datatype is now a GADT --- the result types of the leaf
and node data constructors differ in the height index [4].

Furthermore, we haven't really implemented a type equivalent to `NTree a` because 
the height index n "leaks" into the `ITree` type. Therefore, to define the equivalent
type, we need to also use an existential type to hide this index. 

> data DTree a = forall n. DTree (ITree n a) 

Here are some example trees. They look a lot more like the regular tree type
than the nested tree.

> d1 :: DTree Int
> d1 = DTree $ DLeaf 1

> d2 :: DTree Int
> d2 = DTree $ DNode (Two (DLeaf 1) (DLeaf 2))

> -- not a perfect tree, doesn't type check
> -- d3 = DTree $ DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2))) (DLeaf 3))
>
> d4 :: DTree Int
> d4 = DTree $ DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2)))
>                         (DNode (Two (DLeaf 3) (DLeaf 4))))

Because `ITree` is a GADT, we have to use standalone deriving for the usual
instances above. 

> deriving instance Show a => Show (ITree n a)
> deriving instance Eq a => Eq (ITree n a)
> deriving instance Ord a => Ord (ITree n a)
> deriving instance Functor (ITree n)
> deriving instance Foldable (ITree n)
> deriving instance Traversable (ITree n)

We can still derive many of the usual instances.  This time, we are using
  polymorphic recursion only in the natural number, not in the two type parameters.

> dtmap :: forall n a b. (a -> b) -> (ITree n a -> ITree n b)
> dtmap f (DLeaf x) = DLeaf (f x)
> dtmap f (DNode (z :: Two (ITree m a)))
>    = DNode (fmap (dtmap @m @a @b f) z)


But, here is one cost to our GADT-based approach. The derived
implementations of `Eq` and `Ord` don't type check for `DTree`!

> deriving instance Show a => Show (DTree a)
> -- no deriving instance Eq a => Eq (DTree a)
> -- no deriving instance Ord a => Ord (DTree a) 
> deriving instance Functor DTree
> deriving instance Foldable DTree
> deriving instance Traversable DTree

We can see why by looking at the error message for this attempt:

> -- treeEq :: Eq a => DTree a -> DTree a -> Bool
> -- treeEq (DTree (t1 :: ITree n1 a)) (DTree (t2 :: ITree n2 a)) = t1 == t2

If we try to define an equality function this way, the two `ITree`s have
potentially different height indices, so we cannot use the derived
equality function for `ITree`s.

Therefore, to solve this issue, we need to define a type class for
 *heterogeneous* equality. This type class allows us to compare arguments
 with different types.

> instance Eq a => Eq (DTree a) where
>    DTree t1 == DTree t2 = t1 `heq` t2

> class Heq a b where
>    heq :: a -> b -> Bool
> instance Heq a b => Heq (Two a) (Two b) where
>    heq (Two x y) (Two z w) = heq x z && heq y w
> instance Eq a => Heq (ITree n a) (ITree m a) where
>    heq (DLeaf x) (DLeaf y)   = x == y
>    heq (DNode p1) (DNode p2) = heq p1 p2
>    heq _ _ = False


Type Family-based approach
--------------------------

There is still one more way to define a perfect binary tree. We can use a type
family.  This type-level function computes the appropriate nesting of `Two`
copies of its argument.

> type family FTwo (n :: Nat) (a :: Type) :: Type where
>   FTwo Z     a = a
>   FTwo (S n) a = Two (FTwo n a)

The type `FTwo n a` is difficult to use. As a type family, it doesn't play
well with GHC's unification because it is not injective. That is not a problem as long as
all of the arguments are concrete:

> ft1 :: FTwo Z Int
> ft1 = 1
>
> ft2 :: FTwo (S Z) Int
> ft2 = Two 1 2
>
> ft3 :: FTwo (S (S Z)) Int
> ft3 = Two (Two 1 2) (Two 3 4)

As above, we can hide the type parameter to `FTwo` behind another existential
type. However, we will only be able to use the `FTwo` type if we also have
access to a runtime version of the height. We cannot determine it from `FTwo
n a` alone.  Therefore we also include a singleton type for the natural
number [5]. 

> data FTree a where
>   FTree :: SNat n -> FTwo n a -> FTree a 

> -- | Singleton type for natural numbers
> data SNat :: Nat -> Type where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

> deriving instance Show (SNat n)
> -- no instance for Eq (SNat n)
> -- no instance for Ord (SNat n)

Here are some examples of the `FTree` type. Compare them to the nested datatype
version above --- the singleton nat corresponds to the height prefix on the nested
tree.

> f1 :: FTree Int
> f1 = FTree SZ 1
>
> f2 :: FTree Int
> f2 = FTree (SS SZ) (Two 1 2)
>
> f3 :: FTree Int
> f3 = FTree (SS (SS SZ)) $ Two (Two 1 2) (Two 3 4)

However, with the type family-based type definition, we lose all possibility
of deriving our standard instances. We must implement all of them by
hand. The implementations are fairly straightforward, but do require type
annotations for the local `go` functions to resolve ambiguity.

> instance Show a => Show (FTree a) where
>   showsPrec d (FTree n x) = go d n x where
>      go :: Int -> SNat n -> FTwo n a -> ShowS
>      go d SZ x = showsPrec d x
>      go d (SS n) (Two p1 p2) = showParen (d > 10) $
>                     showString "Two " 
>                   . go 11 n p1
>                   . showString " "
>                   . go 11 n p2
>

To implement equality for `FTree`, we need a way to 
first make sure that the two trees are the same size before
comparison. We can do this by using the following type class 
instance, which produces a proof that the two type-level nats
are the same when the terms are the same.

> instance TestEquality SNat where
>   testEquality :: SNat n1 -> SNat n2 -> Maybe (n1 :~: n2)
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

> instance Eq a => Eq (FTree a) where
>   (FTree n1 x1) == (FTree n2 x2) 
>     | Just Refl <- testEquality n1 n2
>     = eqFTwo n1 x1 x2 where
>          eqFTwo :: SNat n -> FTwo n a -> FTwo n a -> Bool
>          eqFTwo SZ = (==) 
>          eqFTwo (SS n) = \(Two x1 x2)(Two y1 y2) -> eqFTwo n x1 y1 && eqFTwo n x2 y2
>   _ == _ = False

Below, the scoped type variables & type application in the definition of the
`Functor` instance demonstrate that, like `dtmap` above, we are using
polymorphic recursion only on the height argument `n`, and not on the type
arguments `a` and `b`.

> instance Functor FTree where
>    fmap f (FTree n x) = FTree n (go n f x) where
>      go :: forall n a b. SNat n -> (a -> b) -> FTwo n a -> FTwo n b
>      go SZ f a = (f a)
>      go (SS (m :: SNat m)) f p = fmap (go @m @a @b m f) p

> instance Foldable FTree where
>    foldMap :: Monoid m => (a -> m) -> FTree a -> m
>    foldMap f (FTree n x) = go n f x where
>      go :: Monoid m => SNat n -> (a -> m) -> FTwo n a -> m
>      go SZ f a = f a
>      go (SS n) f p = foldMap (go n f) p

> instance Traversable FTree where
>    traverse :: Applicative f => (a -> f b) -> FTree a -> f (FTree b)
>    traverse f (FTree n x) = FTree n <$> go n f x where
>      go :: Applicative f => SNat n -> (a -> f b) -> FTwo n a -> f (FTwo n b)
>      go SZ f a = f a
>      go (SS n) f p = traverse (go n f) p



Comparison
==========

How do `NTree` and `DTree` and `FTree` compare? 

Can we do the same thing with all of the trees?

But can you invert that tree?
-----------------------------

Ok, let's mirror our trees. I don't know why you would want to do this. But it
seems important in technical coding interviews.

Here's the basic building block of tree mirroring: swap the components of the Pair.

> swap :: Two a -> Two a
> swap (Two x y) = Two y x

For regular trees, we recur over the tree and apply the `swap` function above.

> invertTree :: Tree a -> Tree a
> invertTree (Leaf x) = Leaf x
> invertTree (Node p) = Node (swap (fmap invertTree p))

For GADT-based trees, we rely on a helper function that tells us that inverting the tree preserves
its height. 

> invertDTree :: DTree a -> DTree a
> invertDTree (DTree t) = DTree (invert t) where
>    invert :: ITree n a -> ITree n a
>    invert (DLeaf x) = DLeaf x
>    invert (DNode p) = DNode (swap (fmap invert p))

This code is roughly the same as the code for inverting regular trees.

Inverting nested trees is slightly trickier. With every recursive call, we
need to construct a new "inversion function" `f` that we use to invert the
entire tree in one go in the leaf case.

> invertNTree :: NTree a -> NTree a
> invertNTree = go id where
>   go :: (a -> a) -> NTree a -> NTree a
>   go f (NLeaf x) = NLeaf (f x)
>   go f (NNode x) = NNode (go (swap . fmap f) (invertNTree x))

The code for the type family version is similar to the GADT version, but needs
more care.  In this case, the helper function must show that inverting the
tree does not change its height.  That's essential, because we reuse the same
height when we package up the result.  Furthermore, we must use the type
applications `@a` in this definition in order to avoid ambiguity from the use
of `FTwo n a`. (We don't need to explicitly supply `n` because type inference
can determine this type argument via `SNat`.)

> invertFTree :: forall a. FTree a -> FTree a
> invertFTree (FTree n t) = FTree n (invert @a n t) where
>    invert :: forall a n. SNat n -> FTwo n a -> FTwo n a
>    invert SZ a = a
>    invert (SS n) p = swap (fmap (invert @a n) p)

Tree replication
----------------

Given some height `n`, and some value `x`, generate a perfect tree containing
 `2^n` copies of `x`.

Straightforward with the usual tree datatype, though you really want to be careful
to maintain sharing in the recursive calls (i.e. the local definition of `y`)

> replicateTree :: a -> Int -> Tree a
> replicateTree x = go where
>   go 0 = Leaf x
>   go m = Node (Two y y) where
>             y = go (m - 1)

For Nested trees, we naturally
create a tree with a lot of sharing.

> replicateNTree :: a -> Int -> NTree a
> replicateNTree = go where
>   go :: forall a. a -> Int -> NTree a
>   go a 0 = NLeaf a
>   go a m = NNode (go (Two a a) (m - 1))

For GADT-based and type-family based trees, we need to first interpret the height
argument as `SNat` and then use that runtime natural number to control the size of tree
that we generate. Without this, we don't have the static guarantee that we are generating
a perfect tree.

> fromInt :: Int -> Some SNat
> fromInt 0 = Some $ SZ
> fromInt n = case (fromInt (n-1)) of
>   Some sn -> Some $ SS sn

> replicateDTree :: a -> Int -> DTree a
> replicateDTree x i = case fromInt i of
>     Some n -> DTree (go x n)
>       where
>         go :: a -> SNat n -> ITree n a
>         go x SZ     = DLeaf x
>         go x (SS m) = DNode (Two y y) where
>            y = go x m
>
> replicateFTree :: a -> Int -> FTree a
> replicateFTree x i = case fromInt i of
>     Some n -> FTree n (go x n)
>       where
>         go :: a -> SNat n -> FTwo n a
>         go x SZ = x
>         go x (SS m) = Two y y where
>            y = go x m

Microbenchmark
--------------

Ok, this is not a scientific study, but I did run the code. The nested
datatype version seems faster. There's a performance hit for the GADT
version, perhaps from using unary nats. And the type family version allocates
twice as much for reasons that I do not understand.

λ> :set +s
λ> sum $ replicateTree (3::Int) 20
3145728
(0.33 secs, 134,791,032 bytes)
λ> sum $ replicateNTree (3::Int) 20
3145728
(0.27 secs, 118,011,328 bytes)
λ> sum $ replicateDTree (3::Int) 20
3145728
(0.42 secs, 134,791,688 bytes)
λ> sum $ replicateFTree (3::Int) 20
3145728
(0.36 secs, 294,174,088 bytes)


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

However, we can't do the same thing for the `NTree` or `DTree` types. Think about what
grafting means in this case:

< njoin :: NTree (NTree a) -> NTree a

This is only successful if all of the embedded trees are the same height ---
 if they are different from eachother, then we get non-perfect trees.

Our `ITree` and `FTwo` types can talk about joining together structures that
 are all the same shape.  But in these cases, while we get a new perfect tree,
 it doesn't have the same height as the original.

> type family Add n m where
>   Add Z m  = m
>   Add (S n) m = S (Add n m)

> djoin :: ITree n (ITree m a) -> ITree (Add n m) a
> djoin (DLeaf t) = t
> djoin (DNode p) = DNode (djoin <$> p)

> fjoin :: forall a m n. SNat n -> FTwo n (FTwo m a) -> FTwo (Add n m) a
> fjoin SZ t = t
> fjoin (SS k) p = fjoin @a @m k <$> p

Maybe there is a different interpretation of the `Applicative` and `Monad`
 type classes for `ITree`s?

For Applicatives, we can use the `ZipList` interpretation.

> class INat (n :: Nat) where inat :: SNat n
> instance INat Z where inat = SZ
> instance INat n => INat (S n) where inat = SS inat


> instance INat n => Applicative (ITree n) where
>   pure x = go x inat where
>     go :: forall a n. a -> SNat n -> ITree n a
>     go x SZ = DLeaf x
>     go x (SS m) = DNode (Two (go x m) (go x m))
>   f <*> t = go f t where
>     go :: forall n a b. ITree n (a -> b) -> ITree n a -> ITree n b
>     go (DLeaf f) (DLeaf x) = DLeaf (f x)
>     go (DNode (Two t1 t2)) (DNode (Two u1 u2)) =
>       DNode (Two (go t1 u1) (go t2 u2))


But the type doesn't give us enough flexibility for a `Monad` instance.

Parse, don't validate
---------------------

Can we write functions that validate a perfect `Tree` as an `NTree`, `DTree`
  or `FTree`?

> -- Validation function for nested trees, check that the input is a
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

Due to the need for `dsplit` and `dmerge`, both of these operations take
longer than we might like. The ideal would be `O (n + log n)`, which is just `O(n)`.
But instead we get `O (n log n)`.

For the GADT and type family-based approaches, validation and conversion is
much more straightforward. But, still O (n log n) from the equality
comparison on unary nats. If we were to use an optimized representation of
this data, we could get a linear time conversion.

> data SomeITree a where
>   SomeITree :: SNat n -> ITree n a -> SomeITree a 
> forget :: SomeITree a -> DTree a
> forget (SomeITree _ dt) = DTree dt

> toDTree :: Tree a -> Maybe (DTree a)
> toDTree t = forget <$> go t 
>   where
>     go :: Tree a -> Maybe (SomeITree a)
>     go (Leaf x) = return (SomeITree SZ (DLeaf x))
>     go (Node p) = traverse go p >>= node where
>      node :: Two (SomeITree a) -> Maybe (SomeITree a)
>      node (Two (SomeITree n1 u1) (SomeITree n2 u2)) = do
>        Refl <- testEquality n1 n2
>        return $ SomeITree (SS n1) (DNode (Two u1 u2))
>
> fromDTree :: DTree a -> Tree a
> fromDTree (DTree t) = go t where
>      go :: ITree n a -> Tree a
>      go (DLeaf x) = Leaf x
>      go (DNode p) = Node (go <$> p)


> toFTree :: Tree a -> Maybe (FTree a)
> toFTree (Leaf x) = return (FTree SZ x)
> toFTree (Node p) = traverse toFTree p >>= node where
>    node :: Two (FTree a) -> Maybe (FTree a)
>    node (Two (FTree n1 u1) (FTree n2 u2)) = do
>      Refl <- testEquality n1 n2
>      return $ FTree (SS n1) (Two u1 u2)
>
> fromFTree :: FTree a -> Tree a
> fromFTree (FTree n t) = go n t where
>      go :: SNat n -> FTwo n a -> Tree a
>      go SZ  x    = Leaf x
>      go (SS n) p = Node (go n <$> p)



Other examples
--------------

Perfect trees are a fairly constrained, symmetric and artificial data
 structure. Was it just a fluke that we could define the GADT and type-family
analogues to the nested datatype definition?

I don't think so. 

* Other Okasaki data structures
* Well-scoped expressions
* Finger trees

Furthermore, how robust are nested datatypes, in general. For example, I don't
see how to augment the `NTree` data structrue to include values at the nodes
in addition to the leaves. But for GADT-based an type family based
definitions, this modification is straightforward.

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
[4]: I follow the terminology of Coq and call `n` a type *index* (because it varies in the
result type) and `a` a type *parameter* (because it does not).
[5]: We could use https://hackage.haskell.org/package/singletons for these types but it is simpler to just write them here.
