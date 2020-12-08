> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE DeriveTraversable #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE UndecidableInstances #-}

> {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unticked-promoted-constructors #-}

> module SingletonTF where
>
> import Data.Kind (Type)
> import Data.Type.Equality
> 

Type Family-based approach
--------------------------

We can use a type family to define perfect trees.  This type-level function
 computes the appropriate nesting of `Two` copies of its argument.

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
number. 

> data FTree a where
>   FTree :: SNat n -> FTwo n a -> FTree a 

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


> instance Eq a => Eq (FTree a) where
>   (FTree n1 x1) == (FTree n2 x2) 
>     | Just Refl <- testEquality n1 n2
>     = eqFTwo n1 x1 x2 where
>          eqFTwo :: SNat n -> FTwo n a -> FTwo n a -> Bool
>          eqFTwo SZ = (==) 
>          eqFTwo (SS n) = \(Two x1 x2)(Two y1 y2) -> eqFTwo n x1 y1 && eqFTwo n x2 y2
>   _ == _ = False

Below, the scoped type variables and type application in the definition of the
 `Functor` instance demonstrate that we are using polymorphic recursion only
 on the height argument `n`, and not on the type arguments `a` and `b`.

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

> heightFTree :: FTree a -> Int
> heightFTree (FTree n _) = fromNat n

The code for tree inversion for the type family implementation is similar to the GADT version,
but needs more care.  In this case, the helper function must show that
inverting the tree does not change its height.  That's essential, because we
reuse the same height when we package up the result.  Furthermore, we must
use the type applications `@a` in this definition in order to avoid ambiguity
from the use of `FTwo n a`. (We don't need to explicitly supply `n` because
type inference can determine this type argument via `SNat`.)

> invertFTree :: forall a. FTree a -> FTree a
> invertFTree (FTree n t) = FTree n (invert @a n t) where
>    invert :: forall a n. SNat n -> FTwo n a -> FTwo n a
>    invert SZ a = a
>    invert (SS n) p = swap (fmap (invert @a n) p)

> replicateFTree :: a -> Int -> FTree a
> replicateFTree x i = case toSomeNat i of
>     Just (Some n) -> FTree n (replicateFTwo x n)
>     Nothing -> error "invalid argument to replicate FTree"
>
> replicateFTwo :: a -> SNat n -> FTwo n a 
> replicateFTwo x SZ = x
> replicateFTwo x (SS m) = Two y y where
>            y = replicateFTwo x m

We can also convert between (perfect) regular trees and FTrees.

> data Tree a = Leaf a | Node (Two (Tree a))

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

Auxiliary Definitions
---------------------

> data Two a = Two a a
>    deriving (Eq, Ord, Read, Show, Functor, Foldable, Traversable)

> swap :: Two a -> Two a
> swap (Two x y) = Two y x

> data Nat = S Nat | Z
>
> data Some (f :: k -> Type) = forall a. Some (f a)

> -- | Singleton type for natural numbers
> data SNat :: Nat -> Type where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)

> deriving instance Show (SNat n)
> -- no instance for Eq (SNat n)
> -- no instance for Ord (SNat n)

> instance TestEquality SNat where
>   testEquality :: SNat n1 -> SNat n2 -> Maybe (n1 :~: n2)
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

> toSomeNat :: Integral n => n -> Maybe (Some SNat)
> toSomeNat 0 =
>   return (Some SZ)
> toSomeNat n = do
>   Some sn <- toSomeNat (n-1)
>   return (Some (SS sn))

> fromNat :: SNat n -> Int
> fromNat SZ = 0
> fromNat (SS n) = 1 + fromNat n
