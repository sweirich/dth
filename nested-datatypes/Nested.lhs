title: Do we need nested datatypes?

> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE DeriveGeneric #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE RankNTypes #-}
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

Sometimes we want non-regular datatypes
=======================================

Although typed functional programming languages excel at representing tree
structured data, not all trees are regular.  Sometimes we would like to work
with trees of a more particular form than algebraic datatypes express. 

For example, we can represent a regular binary tree, with values only stored
 at the leaves, using the following definition. 

> data Tree (a :: Type) 
>   = Leaf a
>   | Node (Two (Tree a))
>      deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

This definition is for a binary tree, where each node has exactly two
children.  To simplify later comparison, we record that this is a binary tree
using the following simple datatype [0]. This datatype is a pair of two
values of the same type.

> data Two a = Two a a
>    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

But the tree type above can be used to express all sorts of trees, of many
different shapes. What if we *only* want our type to include *perfect* trees
--- i.e. those where every path from the root to a leaf is the same length.

Can we rule out imperfect trees using the type system?

Of course we can! Perfect trees are a classic example of a constraint that can
 be captured using *nested* datatypes.

To express this constraint using a nested datatype, we modify the tree
definition above to say that the `Node` constructor carries a tree of two
values instead of carrying two values that are trees.

> data NTree (a :: Type) =
>     NLeaf a
>   | NNode (NTree (Two a))
>       deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

With this change, this tree definition can *only* represent perfect trees.

For example, we can represent the following regular trees which may or may not
be perfect with the `Tree` type.

> -- a perfect tree
> t1 :: Tree Int
> t1 = Leaf 1

> -- a perfect tree
> t2 :: Tree Int
> t2 = Node (Two (Leaf 1) (Leaf 2))

> -- not a perfect tree
> t3 :: Tree Int
> t3 = Node (Two (Node (Two (Leaf 1) (Leaf 2))) (Leaf 3))

However, with the `NTree` type we can only represent perfect trees.

> -- a perfect tree
> n1 :: NTree Int
> n1 = NLeaf 1
>
> -- a perfect tree
> n2 :: NTree Int
> n2 = NNode (NLeaf (Two 1 2))
>
> -- not a perfect tree, doesn't type check
> -- n3 :: NTree Int
> -- n3 = NNode (NNode (NLeaf (Two (Two 1 2) 3)))

> -- a perfect tree, but not the same as t3
> n4 :: NTree Int
> n4 = NNode (NNode (NLeaf (Two (Two 1 2) (Two 3 4))))

What is the general form of values of type `NTree Int`? It is some number of
`NNode` data constructors, followed by a `NLeaf` data
constructor containing a value of type

<      (Two (Two ... (Two Int)))

That means that this structure is constrained to store exactly `2^n` `Int`
 values, in a perfectly symmetric tree shape.

In fact, we can decode "prefix" of these values i.e. the sequence of `NNode`
and `NLeaf` constructors as `n`, the height of the perfect tree, in unary
notation. In other words, we can decode `NLeaf` as 0, `NNode . NLeaf` as 1,
and `NNode . NNode . NLeaf` as 2, etc.

The key feature that defines a nested datatype is the use of *non-regular*
recursion. If you go back and look at the `NTree` definition, the `NNode`
constructor has an argument of type `NTree (Two a)`. This is a recursive use
of the `NTree` type in its definition, but the argument to this recursive
call is *not* just the parameter to the recursive type itself. Regular
recursion requires this argument to always be the parameter `a` and
non-regular recursion happens when some recursive call uses something else
(like `Two a`).

I sometimes find nested datatypes a bit confusing. How can a simple
modification to the type make such a big difference in the structure? How
should I express similar constraints? Once I have a nested data type
definition, what can I do with it? And how does this approach compare to
other mechanisms for constraining datatypes, such as GADTs?

The rest of this post is a comparison between approaches using the example
of perfect trees. I've chosen perfect trees for this treatment due to their
relative simplicity. It isn't *that* difficult to say all there is to say
about this sort of data structure.

More generally, nested datatypes can be used for many purposes beyond perfect
trees. For example, they feature prominently in practical Haskell libraries
such as `Data.Sequence` (based on the FingerTree data structure) and the
`bound` library (based on well-scoped lambda terms). I conjecture that these
and other applications can also be expressed using GADTs instead of nested
datatypes. I'll return to that point at the end of the post.
 
Working with nested datatypes: polymorphic recursion
----------------------------------------------------

At first, nested datatypes don't seem all that different from regular datatypes. 
For example, even though the `NTree` type uses nested recursion, the usual type classes
(e.g. `Eq`, `Functor`, etc) are derivable, as we saw above. In fact, if you
were to implement these instances by hand, the code you write would be
identical to the non-nested version. In other words, the derived instances for
the `Functor` class look something like this for the two types.

< instance Functor Tree where
<   fmap :: forall a b. (a -> b) -> (Tree a -> Tree b)
<   fmap f (Leaf x) = Leaf (f x)
<   fmap f (Node z) = Node (fmap (fmap f) z)

< instance Functor NTree where
<   fmap :: forall a b. (a -> b) -> (NTree a -> NTree b)
<   fmap f (NLeaf x) = NLeaf (f x)
<   fmap f (NNode z) = NNode (fmap (fmap f) z)

But don't be fooled! These two definitions are *not* the same. There is one
important difference in these derived definitions: functions over nested data
types require *polymorphic recursion*.

In a regular datatype, recursive calls to polymorphic functions use exactly
the same type parameter. To make this clear, I've redefined `fmap` for
regular trees to mark the location of the recursive call and used scoped type
variables and type applications to annotate its instantiation.

> tmap :: forall a b. (a -> b) -> (Tree a -> Tree b)
> tmap f (Leaf x) = Leaf (f x)
> tmap f (Node z) = Node (fmap (tmap @a @b f) z)

Even without the type signature (and type applications), this code would still
type check. Recursive functions over regular datatypes are well within the
expressive power of HM type inference.

However, compare the above to the implementation of the mapping function for
the nested datatype. Note that in this case, the recursive call to `ntmap`
uses not `a` and `b`, but `Two a` and `Two b`. This is polymorphic recursion
in action, directly corresponding to the fact that the datatype definition
uses `Two a` instead of `a` in its definition.

> ntmap :: forall a b. (a -> b) -> (NTree a -> NTree b)
> ntmap f (NLeaf x) = NLeaf (f x)
> ntmap f (NNode z) = NNode (ntmap @(Two a) @(Two b) (fmap f) z)

In the absence of type annotations, like the definition of `ntmap` above,
Hindley-Milner type inference with polymorphic recursion is undecidable
[1][2]. As a consequence, if we remove the type annotation, then we get an
error message from GHC:

     nested.lhs:(118,3)-(119,44): error: …
         • Occurs check: cannot construct the infinite type: t ~ f t
           Expected type: (f t -> f b) -> NTree (Two t) -> NTree (Two b)
             Actual type: (t -> b) -> NTree t -> NTree b
         • Relevant bindings include
             tmap :: (f t -> f b) -> NTree (Two t) -> NTree (Two b)
               (bound at /Users/sweirich/github/dth/nested-datatypes/nested.lhs:118:3)
         |
     Compilation failed.

So, when working with nested datatypes, we must always remember to annotate
the type of the function---GHC cannot figure it out for us.  In the presence
of this type annotation, polymorphic recursion is not difficult and has
been a part of Haskell for years. (The Haskell 98 report specifically states
that type signatures can be used to support polymorphic recursion [3].)

Representing perfect trees with GADTs
=====================================

One thing that puzzles me about nested datatypes, like `NTree` is that the
type parameter does double-duty. It both constrains the shape of the tree
*and* parameterizes the type of data stored in the tree.

A definition of perfect trees using GADTs separates these aspects of the
 definition. Let's compare.

First, we'll define some natural numbers so that we can count.

> data Nat = S Nat | Z 

Now, let's index a tree by its height and require that both subtrees in a node
have the *same* height. Here, we're using datatype promotion with in a GADT
so that we can refer to natural numbers in types.

> data HTree (h :: Nat) (a :: Type) where
>   DLeaf :: a -> HTree Z a
>   DNode :: Two (HTree h a) -> HTree (S h) a

This data type definition is a GADT because the result types of the leaf and
node data constructors differ in the height index [4]. So that we can express
this difference in the result type, we use GADT syntax for the definition.

But, we haven't yet implemented a type equivalent to `NTree a` because the
height index `h` "leaks" into the `HTree` type. Therefore, to define the
equivalent type, we need to also use an existential type to hide this index.

> data DTree a = forall h. DTree (HTree h a) 

Here are some example trees. In construction, they look a lot more like the regular tree type
than the nested tree, but the type system still rules out non-perfect trees.

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

However, because `HTree` is a GADT, we must use standalone deriving for the
usual instances above.

> deriving instance Show a => Show (HTree h a)
> deriving instance Eq a => Eq (HTree h a)
> deriving instance Ord a => Ord (HTree h a)
> deriving instance Functor (HTree h)
> deriving instance Foldable (HTree h)
> deriving instance Traversable (HTree h)

These derived instances look the same as the derived instances for
`Tree`. And, like the nested datatype, they require polymorphic recursion.
For example, if we add scoped type variables to the definition of `fmap` for
this type, we can see that the recursive call uses the height `k` instead of
`h`. (The type variable `k` must be bound in the patter for `DNode`. When it
is introduced we also know that it is equal to `S h`.)  What this means is
that we need to add annotations on recursive functions that use the type
`HTree` in order to get them to type check. (Again, we don't need to bind the
scoped type variables and provide the explicit type applications, the
top-level type annotation provides enough information for GHC to figure it
out.)

> dtmap :: forall h a b. (a -> b) -> (HTree h a -> HTree h b)
> dtmap f (DLeaf x) = DLeaf (f x)
> dtmap f (DNode (z :: Two (HTree k a)))
>    = DNode (fmap (dtmap @k @a @b f) z)

But, there *is* a cost to the GADT-based approach. The derived implementations
 of `Eq` and `Ord` don't type check for `DTree`!

> deriving instance Show a => Show (DTree a)
> -- deriving instance Eq a => Eq (DTree a)   -- doesn't type check
> -- deriving instance Ord a => Ord (DTree a) -- doesn't type check
> deriving instance Functor DTree
> deriving instance Foldable DTree
> deriving instance Traversable DTree

We can see why by looking at the error message for this attempt:

> -- treeEq :: Eq a => DTree a -> DTree a -> Bool
> -- treeEq (DTree (t1 :: HTree h1 a)) (DTree (t2 :: HTree h2 a)) = t1 == t2

If we try to define an equality function this way, the two `HTree`s have
potentially different height indices, so we cannot use the derived
equality function for `HTree`s. The expression `t1 == t2` doesn't type check
because `t1` and `t2` have different heights.

There are two different ways that we can implement the equality operation for
`DTree`.  The first is to define a type class for *heterogeneous*
equality. This type class allows us to compare arguments with different
types. GHC doesn't know how to automatically derive instances of this class,
so we must provide them directly. However, the code that we write is the same
as for the `Eq` class.

> -- Heterogeneous equality type class
> class Heq a b where
>    heq :: a -> b -> Bool
> instance Heq a b => Heq (Two a) (Two b) where
>    heq (Two x y) (Two z w) = heq x z && heq y w
> instance Eq a => Heq (HTree n a) (HTree m a) where
>    heq (DLeaf x) (DLeaf y)   = x == y
>    heq (DNode p1) (DNode p2) = heq p1 p2
>    heq _ _ = False

> instance Eq a => Eq (DTree a) where
>    DTree t1 == DTree t2 = t1 `heq` t2

The second solution is to compare the heights of `t1` and `t2` and then only call the
equality function if the two trees have the same height. To implement this version we need
three components:

1. A run time version of the (so far) compile-time only height. This GADT,
  called a *singleton* type, exactly reflects the structure of the
 `Nat` type above.

> data SNat n where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

The important property of this data structure is that if a value `x` has type
`SNat h` then it is isomorphic to `h` (i.e.  it is the unary representation
of the same number.) It is common, when programming with indexed types in
Haskell, to need such a singleton type. Compared to full-spectrum
dependently-typed languages, like Agda or Idris, Haskell does not allow the
same parameter to be computationally relevant (i.e. around at run time) and an
index to a data structure. Thus, we need to set up this somewhat awkward
mirroring. (The `singletons` library can help automate this.)

2. A way to calculate the run time representation of the height of a height-indexed tree.

The type of this function asserts its correctness --- the value that it
returns must be the height of the tree.

> heightHTree :: HTree h a -> SNat h
> heightHTree (DLeaf _) = SZ
> heightHTree (DNode (Two t1 _)) = SS (heightHTree t1)

3. A way to compare two singleton values for equality.

For this step, we'll create an instance of the class `TestEquality` from the module `Data.Type.Equality`. This class captures the idea that sometimes, when comparing
indexed data structures, we can produce a proof that indices are equal. 

< class TestEquality f where
<    testEquality :: f a -> f b -> Maybe (a :~: b)

Singleton types make ideal instances of this class. For the `SNat` type,
if we have two copies of `SZ` then we can prove that the two (compile-time) nats
are equal, using the trivial proof `Refl`. Otherwise, if they both start with
`SS`, we can compare their predecessors. If those two happen to be equal, we can
still use `Refl` as our proof.

> instance TestEquality SNat where
>   testEquality :: SNat n1 -> SNat n2 -> Maybe (n1 :~: n2)
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

With these three components, we can define an equality function for `DTree`s
that is based on our derived, homogeneously typed equality function for
`HTree`s.

> dtreeEq :: Eq a => DTree a -> DTree a -> Bool
> dtreeEq (DTree t1) (DTree t2) = case
>    testEquality (heightHTree t1) (heightHTree t2) of
>      Just Refl -> t1 == t2  -- here we know the types are the same because the
>                             -- two trees must have the same height
>      Nothing   -> False

Programming with perfect trees
==============================

We've looked at the difference in terms of derivable type classes.  But, how
do the types `NTree` and `DTree` compare with operations that we write by
hand?  How difficult is it to actually program with these data structures?

Here are several examples of functions that work with perfect trees. All of
these functions are straightforward to define for regular trees. Sometimes
they are a bit easier to express with the GADT version and sometimes they are
a bit easier to express with the nested datatype version.

Tree inversion
--------------

OK, let's mirror our trees. I don't know why you would want to do this, but it
seems important in technical coding interviews and is straightforward
enough.

Here's the basic building block of tree mirroring: swap the order of the two
components.

> swap :: Two a -> Two a
> swap (Two x y) = Two y x

For regular trees, tree mirroring is straightforward. We recur over the tree
and apply the `swap` function above.

> invertTree :: Tree a -> Tree a
> invertTree (Leaf x) = Leaf x
> invertTree (Node p) = Node (swap (fmap invertTree p))

For GADT-based trees, we rely on a local helper function that tells us that
 inverting the tree preserves its height. But the code for the local function
is the same as the definition above.

> invertDTree :: DTree a -> DTree a
> invertDTree (DTree t) = DTree (invert t) where
>    invert :: HTree n a -> HTree n a
>    invert (DLeaf x) = DLeaf x
>    invert (DNode p) = DNode (swap (fmap invert p))

However, inverting nested trees is slightly trickier and not similar to the
regular tree version. The local function needs to create the appropriate
inversion function `f` With every recursive call. Then at the base case this
function inverts the entire tree in one go.

> invertNTree :: NTree a -> NTree a
> invertNTree = go id where
>   go :: (a -> a) -> NTree a -> NTree a
>   go f (NLeaf x) = NLeaf (f x)
>   go f (NNode p) = NNode (go (swap . fmap f) (invertNTree p))


Tree replication
----------------

Given some height `n`, and some value `x`, let's generate a perfect tree containing
 `2^n` copies of `x`.

This function is straightforward enough to write with the regular tree datatype,
though you really want to be careful to maintain sharing in the recursive
calls (i.e. make sure that you use a local definition of `y`.)

> replicateTree :: a -> Int -> Tree a
> replicateTree x = go
>   where
>     go 0 = Leaf x
>     go m | m < 0 = error "invalid argument to replicateTree"
>     go m = Node (Two y y) where
>               y = go (m - 1)

For Nested trees, as above, we need to add an "accumulator" to the local helper function and update this accumulator on
on each recursive call. However, with this version we can't help but create a tree with a lot of sharing.

> replicateNTree :: a -> Int -> NTree a
> replicateNTree = go
>   where
>     go :: forall a. a -> Int -> NTree a
>     go a 0 = NLeaf a
>     go a m | m < 0 = error "invalid argument to replicateNTree"
>     go a m = NNode (go (Two a a) (m - 1))

For GADT-based trees, we need to first interpret the height argument as an
`SNat`, using the `toSomeNat` function, and then use that run time natural
number to control the size of tree that we generate.

> replicateDTree :: forall a. a -> Int -> DTree a
> replicateDTree x i = case toSomeNat i of
>     Just (Some n) -> DTree (go n)
>       where
>         go :: SNat n -> HTree n a 
>         go SZ     = DLeaf x
>         go (SS m) = DNode (Two y y) where
>            y = go m
>     Nothing -> error "invalid argument to replicate DTree"

This translation function would be part of a library for working with `SNat`
values. Because we don't know statically what number it will produce, we must
hide that height parameter in the `Some` datatype from `Data.Some`.

> toSomeNat :: Integral n => n -> Maybe (Some SNat)
> toSomeNat 0 =
>   return (Some SZ)
> toSomeNat n = do
>   Some sn <- toSomeNat (n-1)
>   return (Some (SS sn))


Validating perfect trees
------------------------

Can we write functions that convert a `Tree` to be an `NTree` or `DTree` if it
happens to be perfect? Or inject a `NTree` or `DTree` into a regular tree?

Both validation functions can be expressed with the same general structure:
recur over the tree datatype, and use a "smart constructor", called `node`,
to construct a binary node out of two subtrees if the the two subtrees have
the same height.

For nested trees, this "smart constructor" recursively merges the two trees
if they have the same prefix (which ensures they have the same height).

> toNTree :: Tree a -> Maybe (NTree a)
> toNTree (Leaf x) = return (NLeaf x)
> toNTree (Node p) = traverse toNTree p >>= node where
>   node :: Two (NTree a) -> Maybe (NTree a)
>   node (Two n1 n2) = NNode <$> merge n1 n2 where
>     merge :: NTree a -> NTree a -> Maybe (NTree (Two a))
>     merge (NLeaf x) (NLeaf y) = pure (NLeaf (Two x y))
>     merge (NNode x) (NNode y) = NNode <$> merge x y
>     merge _ _ = Nothing

For GADT-based trees, the "smart constructor" more directly calculates the
heights to the two trees, tests them for equality, and constructs a new tree
if the test succeeds. A more efficient version might return the height as
part of the recursion (instead of recalculating it at every step).

> toDTree :: Tree a -> Maybe (DTree a)
> toDTree (Leaf x) = return (DTree (DLeaf x))
> toDTree (Node p) = traverse toDTree p >>= node where
>      node :: Two (DTree a) -> Maybe (DTree a)
>      node (Two (DTree u1) (DTree u2)) = do
>        Refl <- testEquality (heightHTree u1) (heightHTree u2)
>        return $ (DTree (DNode (Two u1 u2)))

For the operation of "forgetting" that a tree is perfect, the GADT-based
version looks like the identity function it should be, modulo a little
syntactic noise from the `DNode` constructor.

> fromDTree :: DTree a -> Tree a
> fromDTree (DTree (DLeaf x)) = Leaf x
> fromDTree (DTree (DNode p)) = Node (fromDTree . DTree <$> p)

The nested datatype version, on the other hand, must defer to a helper
function to split the `NTree` at each step.

> fromNTree :: NTree a -> Tree a
> fromNTree (NLeaf x) = Leaf x
> fromNTree (NNode p) = Node (fromNTree <$> split p) where
>     split :: NTree (Two a) -> Two (NTree a)
>     split (NLeaf p) = NLeaf <$> p
>     split (NNode p) = NNode <$> split p

Due to the need for `dsplit` and `dmerge`, both of the operations take
longer than we might like for nested trees. The ideal would be `O(n)`,
but instead we get `O (n log n)`.

For the GADT approach, the injection function has a linear running time, but
validation is still `O (n log n)` due to the height computation and equality
comparison on unary nats. If we were to be a bit more clever (return the
height as we traverse the tree, use an representation of run time nats), we
could get a linear time conversion. However, it's probably not worth it in
practice to do so.


Other operations
----------------

Of course, these are not the only operations that one may define using perfect
trees. However, these operations are good exemplars of what the set of
operations might look like. Furthermore, the `Foldable` and `Traversable`
instances mean that many operations can be written generically, for all
trees.

On the other hand, there is one significant difference between nested
datatypes and GADTs: the former is supported directly by `GHC.Generics` but
the latter is not. This means that the `Generic` class, from `GHC.Generics`
is automatically derivable for nested datatypes, but not for GADTs. There may
be a way to create an instance of the `Generic` type class by hand, but GHC
cannot do so automatically.


Conclusions
===========

This is about as far as we can go with the comparison just using perfect
 trees. There isn't all that much you can do with them. From my point of view,
 I find the indexed version of the data structure a bit easier to understand
 because of the contortions required for operations such as
 `invertNTree`. However, maybe that is because I am already familiar with the
 patterns of Dependent Haskell. If you are the opposite, perhaps this
 explanation will serve as a Rosetta stone.

Other ways to define perfect trees
----------------------------------

There are still more ways to represent perfect trees in Haskell, using type
 families, a finally-tagless encoding, LiquidHaskell, etc. A few of these
 alternatives are collected
 [here](https://github.com/sweirich/dth/tree/master/examples/perfect-trees).

Other nested datatypes
----------------------

Perfect trees are an example of a fairly constrained, symmetric and artificial
data structure. So was it just a fluke that we could define a GADT analogue
to the nested datatype definition?

I don't think so.

I know of at least two other examples of constrained data structures that can
 be implemented by either nested datatypes and GADT-based alternatives.

* [Well-scoped expressions](http://www.staff.city.ac.uk/~ross/papers/debruijn.html)

A famous use of nested datatypes is to ensure that lambda calculus expressions
 are well-scoped. This idea underlies the design of Kmett's
 [bound](https://www.schoolofhaskell.com/user/edwardk/bound) library.

However, instead of using a nested datatype, it is also possible to use a
type-level natural number to bound the scopes of bound variables, as shown
in [this implementation](https://github.com/sweirich/lennart-lambda/blob/master/lib/DeBruijnScoped.lhs).

* [Finger trees](http://www.staff.city.ac.uk/~ross/papers/FingerTree.html)

Haskell's implementation of the
[sequence](https://hackage.haskell.org/package/containers-0.6.4.1/docs/Data-Sequence.html)
data structure is built on FingerTrees. In the module
[DFinger.lhs](DFinger.lhs) I've sketched out a nat-indexed replacement to the
nested datatype.


[0]: Many examples of nested datatypes, especially for perfect trees, use the type
`(a,a)` instead of `Two`. However, it is convenient in modern Haskell to
 have the appropriate definitions of `fmap` etc. available for this
auxiliary type.

[1]: Fritz Henglein, Type Inference with Polymorphic Recursion.
ACM Transactions on Programming Languages and Systems. Vol 15, Issue 2. April 1993.
[2]: Assaf J Kfoury, Jerzy  Tiuryn, Paweł Urzyczyn. Type reconstruction in the presence of polymorphic recursion. ACM Transactions on Programming Languages and Systems. Vol 15, Issue 2. April 1993.
[3]: https://www.haskell.org/onlinereport/decls.html#type-signatures
[4]: I follow the terminology of Coq and call `n` a type *index* (because it varies in the
result type) and `a` a type *parameter* (because it does not).
[5]: We could use https://hackage.haskell.org/package/singletons for these types but it is simpler to just write them here.
