Persistent Data Structures
==========================

> {-# LANGUAGE KindSignatures, ScopedTypeVariables #-}

> module Set where

> import Control.Monad 
> import Test.QuickCheck hiding (elements)
> import Data.Maybe as Maybe
> import Data.List (sort,nub)

Persistent vs. Ephemeral
------------------------

* An *ephemeral* data structure is one for which only one version is
available at a time: after an update operation, the structure as it
existed before the update is lost.

For example, an array is ephemeral. After locations written to in the 
array are updated, the old information is no longer available.

* A *persistent* structure is one where multiple version are simultaneously
accessible: after an update, both old and new versions are available. For
example, a binary tree can be implemented persistently, so that after
insertion, the old value of the tree is still available.

Persistent data structures can be more expensive than their ephemeral
counterparts in terms of computational complexity, but that cost is often
small compared to their benefits:

   - better integration with concurrent programming, naturally lock-free
   - simpler, more-declarative programming 
   - better semantics for equality/hashing/etc.
   - access to *all* old versions (git for everything)


We'll talk about the implementation of some *simple* persistent data
structures in class. These lectures demonstrate that functional programming is
adept at implementing sophisticated data structures. In particular, datatypes
and pattern matching make the implementation of persistent tree-like data
structures remarkably straightforward. These examples are drawn from Chris
Okasaki's excellent book [Purely Functional Data
Structures](http://www.amazon.com/Purely-Functional-Structures-Chris-Okasaki/dp/0521663504).

However, we'll only scratch the surface. There are many industrial strength
persistent data structures out there.

  * Finger trees/Ropes, see  [Data.Sequence](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-Sequence.html)
  * Size balanced trees, see [Data.Map](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-Map.html)
  * Big-endian patricia trees, see [Data.IntMap](http://www.haskell.org/ghc/docs/7.6.3/html/libraries/containers-0.5.0.0/Data-IntMap.html)
  * Hash array mapped tries, used in the [Clojure](http://en.wikipedia.org/wiki/Hash_array_mapped_trie) language
  * and [many more](http://cstheory.stackexchange.com/questions/1539/whats-new-in-purely-functional-data-structures-since-okasaki)
  

A Set interface
===============

Let's think about what the interface to a persistent set should look
like. We can tell that this implementation is persistent just by
looking at the types of the operations.

> class Set s where
>    empty    :: s a
>    member   :: Ord a => a -> s a -> Bool
>    insert   :: Ord a => a -> s a -> s a
>    elements :: Ord a => s a -> [a]

For example, one trivial implementation of sets is with lists. 

> instance Set [] where
>    empty    = []
>    member   = elem
>    insert   = (:)
>    elements = sort . nub 

When we define an abstract data structure like `Set` above, we should
also specify properties that *all* implementations should satisfy.

For each of these properties, we will use a `Proxy` argument to tell
quickcheck exactly which implementation it should be testing. We could
use a type annotation instead (except for `prop_empty`) but the `Proxy`
argument is a little bit easier to use.

> data Proxy (s :: * -> *) = Proxy

For example, we can define a proxy for the list type.

> list :: Proxy []
> list = Proxy

The empty set has no elements.

> prop_empty :: forall s. (Set s) => Proxy s -> Bool
> prop_empty _ = null (elements (empty :: s Int))


The elements of the set are sorted.

> prop_elements :: (Set s) => Proxy s -> s Int -> Bool
> prop_elements _ x = elements x == nub (sort (elements x)) &&
>      all (\y -> member y x) (elements x)

When we insert an element in the set, we want to make sure that 
it is contained in the result.

> prop_insert1 :: (Set s) => Proxy s -> Int -> s Int -> Bool
> prop_insert1 _ x t = member x (insert x t)

And that the new set also contains all of the original elements.

> prop_insert2 :: (Set s) => Proxy s -> Int -> s Int -> Bool
> prop_insert2 _ x t = all (\y -> member y t') (elements t) where 
>    t' = insert x t

    *Persistent> quickCheck $ prop_empty list
    *Persistent> quickCheck $ prop_elements list
    *Persistent> quickCheck $ prop_insert1 list
    *Persistent> quickCheck $ prop_insert2 list









