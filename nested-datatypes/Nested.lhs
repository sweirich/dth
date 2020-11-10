

Do we need nested datatypes?
============================

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
--------------------

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
node have the same height. 

> data ITree (n :: Nat) (a :: Type) where
>   DLeaf :: a -> ITree 'Z a
>   DNode :: Two (ITree n a) -> ITree ('S n) a

In this case, our tree datatype is now a GADT --- the result types of the leaf
and node data constructors differ in the height index [4].

Because `ITree` is a GADT, we have to use standalone deriving for the
instances above. 

> deriving instance Show a => Show (ITree n a)
> deriving instance Eq a => Eq (ITree n a)
> deriving instance Ord a => Ord (ITree n a)
> deriving instance Functor (ITree n)
> deriving instance Foldable (ITree n)
> deriving instance Traversable (ITree n)

Furthermore, we haven't really implemented a type equivalent to `NTree a` because 
the height index n "leaks" into the `ITree` type. Therefore, to define the equivalent
type, we need to also use an existential type to hide this index. For
convenience we also include a singleton type for the natural number to have a runtime witness for
that height [5]. (This singleton corresponds to the height prefix on the nested
tree.)

> -- | Singleton type for natural numbers
> data SNat :: Nat -> Type where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)
> deriving instance Show (SNat n)
> -- no instance for Eq (SNat n)
> -- no instance for Ord (SNat n)

> data DTree a = forall n. DTree (SNat n) (ITree n a) 

> deriving instance Show a => Show (DTree a)
> -- no deriving instance Eq a => Eq (DTree a)
> -- no deriving instance Ord a => Ord (DTree a) 
> deriving instance Functor DTree
> deriving instance Foldable DTree
> deriving instance Traversable DTree


We can already see one cost to our GADT-based approach. The derived
implementations of `Eq` and `Ord` don't type check for `DTree` trees.

We can see the problem by looking at the error message for this attempt:

> -- treeEq :: Eq a => DTree a -> DTree a -> Bool
> -- treeEq (DTree _ t1) (DTree _ t2) = t1 == t2

If we try to define an equality function this way, the two `ITree`s have
potentially different height parameters, so we cannot use the derived
equality function for `ITree`s.

There are two ways we could implement equality for `DTree` trees. The
first is to first make sure that the two trees are the same size before
comparison. We can do this by checking if their height parameters are
the same.

> instance TestEquality SNat where
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

> instance Eq a => Eq (DTree a) where
>    DTree n1 t1 == DTree n2 t2 =
>      case testEquality n1 n2 of
>        Just Refl -> t1 == t2   -- now we know t1 and t2 have the same height
>        Nothing   -> False


Alternatively, we could define a heterogenous equality for `ITree`s and ignore
  the height parameter altogether.

> class Heq a b where
>    heq :: a -> b -> Bool
> instance Heq a b => Heq (Two a) (Two b) where
>    heq (Two x y) (Two z w) = heq x z && heq y w
> instance Eq a => Heq (ITree n a) (ITree m a) where
>    heq (DLeaf x) (DLeaf y)   = x == y
>    heq (DNode p1) (DNode p2) = heq p1 p2
>    heq _ _ = False

> peq :: Eq a => DTree a -> DTree a -> Bool
> peq (DTree _ t) (DTree _ u) = heq t u

Now, here are the examples. They look a lot more like the first tree type
than the second.

> d1 :: ITree 'Z Int
> d1 = DLeaf 1

> d2 :: ITree ('S 'Z) Int
> d2 = DNode (Two (DLeaf 1) (DLeaf 2))

> -- not perfect, doesn't type check
> -- d3 = DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2))) (DLeaf 3))
>
> d4 :: ITree ('S ('S 'Z)) Int
> d4 = DNode (Two (DNode (Two (DLeaf 1) (DLeaf 2)))
>                 (DNode (Two (DLeaf 3) (DLeaf 4))))

We can use the same definitions, once again, for our common instances.  This
time, we are using polymorphic recursion in the natural number, not in the
two type parameters.

> dtmap :: forall n a b. (a -> b) -> (ITree n a -> ITree n b)
> dtmap f (DLeaf x) = DLeaf (f x)
> dtmap f (DNode (z :: Two (ITree m a)))
>    = DNode (fmap (dtmap @m @a @b f) z)

Type Family-based approach
--------------------------

There is still one more way to define a perfect binary tree. We can use a type
 family.  This type definition computes the appropriate nesting of `Two`
 copies of its argument, similar to the way that the nested datatype does so.


> type family FTwo (n :: Nat) (a :: Type) :: Type where
>   FTwo Z     a = a
>   FTwo (S n) a = Two (FTwo n a)

The type `FTwo n a` is difficult to use. As a type family, it doesn't play
well with GHC's unification because it is not injective. That is not a problem as long as
all of the arguments are concrete:

> f1 :: FTwo Z Int
> f1 = 1
>
> f2 :: FTwo (S Z) Int
> f2 = Two 1 2
>
> f3 :: FTwo (S (S Z)) Int
> f3 = Two (Two 1 2) (Two 3 4)

As above, we can hide the type parameter to `FTwo` behind another existential
 type.

> data FTree a where
>   FTree :: SNat n -> FTwo n a -> FTree a 

However, with this type definition, we lose all possibility of deriving our
 standard instances. We must implement these definitions by hand. The
 implementations are fairly straightforward, but do require type annotations
 to resolve ambiguity.

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

> instance Eq a => Eq (FTree a) where
>   (FTree n1 x1) == (FTree n2 x2) 
>     | Just Refl <- testEquality n1 n2
>     = eqFTwo n1 x1 x2 where
>          eqFTwo :: SNat n -> FTwo n a -> FTwo n a -> Bool
>          eqFTwo SZ = (==) 
>          eqFTwo (SS n) = \(Two x1 x2)(Two y1 y2) -> eqFTwo n x1 y1 && eqFTwo n x2 y2
>   _ == _ = False

> instance Functor FTree where
>    fmap f (FTree n x) = FTree n (go f n x) where
>      go :: (a -> b) -> SNat n -> FTwo n a -> FTwo n b
>      go f SZ a = (f a)
>      go f (SS n) p = fmap (go f n) p

> instance Foldable FTree where
>    foldMap :: Monoid m => (a -> m) -> FTree a -> m
>    foldMap f (FTree n x) = go f n x where
>      go :: Monoid m => (a -> m) -> SNat n -> FTwo n a -> m
>      go f SZ a = f a
>      go f (SS n) p = foldMap (go f n) p

> instance Traversable FTree where
>    traverse :: Applicative f => (a -> f b) -> FTree a -> f (FTree b)
>    traverse f (FTree n x) = FTree n <$> go f n x where
>      go :: Applicative f => (a -> f b) -> SNat n -> FTwo n a -> f (FTwo n b)
>      go f SZ a = f a
>      go f (SS n) p = traverse (go f n) p



Comparison
==========

How do `NTree` and `ITree`/`DTree` and `FTree` compare? 

Can we do the same thing with all of the trees?

But can you invert that tree?
-----------------------------

Ok, let's mirror our trees. I don't know why you would want to do this. But it seems important.

Here's our basic building block. Swap the components of the Pair.

> swap :: Two a -> Two a
> swap (Two x y) = Two y x

For perfect trees, we rely on a helper function that tells us that inverting the tree preserves
its height. That's essential, because we reuse the same height when we package up the result.

> invertDTree :: DTree a -> DTree a
> invertDTree (DTree n t) = DTree n (invert t) where
>    invert :: ITree n a -> ITree n a
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

And, the type family definition needs more care to be taken with type
 applications in order to avoid ambiguity from the use of `FTwo n a`.

> invertFTree :: forall a. FTree a -> FTree a
> invertFTree (FTree n t) = FTree n (invert @a n t) where
>    invert :: forall a n. SNat n -> FTwo n a -> FTwo n a
>    invert SZ a = a
>    invert (SS n) p = swap (fmap (invert @a n) p)

Tree replication
----------------

Given some height `n`, and some value `x`, generate a perfect tree containing
 `2^n` copies of `x`.

Straightforward with the usual tree datatype. 

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

> fromInt :: Int -> Some SNat
> fromInt 0 = Some $ SZ
> fromInt n = case (fromInt (n-1)) of
>   Some sn -> Some $ SS sn

> replicateDTree :: a -> Int -> DTree a
> replicateDTree x i = case fromInt i of
>     Some n -> DTree n (go x n)
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
twice as much for reasons I do not understand.

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

Our `ITree` type can talk about joining together trees that are all the same shape.
But in this case, while we get a new perfect tree, it doesn't have the same height as the
original.

> djoin :: ITree n (ITree m a) -> ITree (Add n m) a
> djoin (DLeaf t) = t
> djoin (DNode (Two t1 t2)) = DNode (Two (djoin t1) (djoin t2))

> type family Add n m where
>   Add Z m  = m
>   Add (S n) m = S (Add n m)

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


Converting between representations
----------------------------------

We can, with effort, convert a `NTree` to a `DTree` tree. And we can, with
 effort, convert a `DTree` tree to a `NTree`.

Both of these conversions require the use of an auxiliary data structure that
captures a "decomposed" nested tree. i.e. one where we have eliminated unary
encoded prefix into a runtime natural number (i.e. `SNat`) and only have the
nesting of the `Two` data structure.

> data HT (a :: Type) where
>   HT :: SNat n -> NTwo n a -> HT a


> n2p :: NTree a -> DTree a
> n2p nt = case n2ht nt of
>           HT n s -> DTree n (ht2d n s)

> -- | decompose the prefix find out the height of the perfect tree
> n2ht :: NTree a -> HT a 
> n2ht (NLeaf a) = HT SZ a
> n2ht (NNode t) = case n2ht t of
>   HT m p -> HT (SS m) p
>
>  -- This is a nested type. We're just counting the number of iterations.
> type family NTwo (n :: Nat) (a :: Type) :: Type where
>   NTwo Z     a = a
>   NTwo (S n) a = NTwo n (Two a)

> 
> -- | take the tree structure itself and convert it to the indexed version
> ht2d :: SNat n -> NTwo n a -> ITree n a
> ht2d SZ a = DLeaf a
> ht2d (SS m) p = DNode (dsplit (ht2d m p))
>   where
>     dsplit :: ITree n (Two a) -> Two (ITree n a)
>     dsplit (DLeaf (Two x y))   = Two (DLeaf x) (DLeaf y)
>     dsplit (DNode (Two t1 t2)) = Two (DNode (Two t1a t2a)) (DNode (Two t1b t2b))
>        where
>          (Two t1a t1b) = dsplit t1
>          (Two t2a t2b) = dsplit t2
>

> p2n :: DTree a -> NTree a
> p2n (DTree n dt) = ht2n (HT n (d2ht dt))
>
> ht2n :: forall a. HT a -> NTree a
> ht2n (HT SZ x) = NLeaf x
> ht2n (HT (SS m) x) = NNode (ht2n (HT m x))

> d2ht :: forall n a. ITree n a -> NTwo n a
> d2ht (DLeaf a) = a
> d2ht (DNode (Two p1 p2)) = d2ht (dmerge p1 p2)
>   where
>     dmerge :: forall n a. ITree n a -> ITree n a -> ITree n (Two a)
>     dmerge (DLeaf x) (DLeaf y) = DLeaf (Two x y)
>     dmerge (DNode (Two t1a t1b)) (DNode (Two t2a t2b)) =
>          DNode (Two (dmerge t1a t2a) (dmerge t1b t2b))

Due to the need for `dsplit` and `dmerge`, both of these operations take
longer than we might like. The ideal would be `O (n + log n)`, which is just `O(n)`.
But instead we get `O (n log n)`.

Parse, don't validate
---------------------

Can we write functions that validate a perfect `Tree` as an `NTree`, `DTree`
  or `FTree`?

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

Due to the need for `dsplit` and `dmerge`, both of these operations take
longer than we might like. The ideal would be `O (n + log n)`, which is just `O(n)`.
But instead we get `O (n log n)`.

For the GADT and type family-based approaches, validation and conversion is
   much more straightforward and runs in linear time.

> toDTree :: Tree a -> Maybe (DTree a)
> toDTree (Leaf x) = return (DTree SZ (DLeaf x))
> toDTree (Node p) = traverse toDTree p >>= node where
>    node :: Two (DTree a) -> Maybe (DTree a)
>    node (Two (DTree n1 u1) (DTree n2 u2)) = do
>      Refl <- testEquality n1 n2
>      return $ DTree (SS n1) (DNode (Two u1 u2))
>
> fromDTree :: DTree a -> Tree a
> fromDTree (DTree _ t) = go t where
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

* Perfect trees with data at the nodes
* Other Okasaki data structures
* Well-scoped expressions
* Finger trees


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
