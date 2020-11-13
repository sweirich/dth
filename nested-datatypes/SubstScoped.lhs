
This is a general purpose library for defining substitution for debruijn indices

> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE QuantifiedConstraints #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveTraversable #-}

> {-# OPTIONS_GHC -Wno-unticked-promoted-constructors #-}
> 
> module SubstScoped where
>
> import Data.Kind (Type)
> import Nat
> import Control.Monad(ap)
> import Control.DeepSeq
> import Data.Foldable
> import Data.Traversable
> import Prelude hiding (all)

> ------------------------------------
> -- Directly taken from Bound.Term
> -- https://hackage.haskell.org/package/bound-2.0.2/docs/src/Bound.Term.html#substitute
> -- 
> -- | @'substitute' a p w@ replaces the free variable @a@ with @p@ in @w@.
> --
> -- >>> substitute "hello" ["goodnight","Gracie"] ["hello","!!!"]
> -- ["goodnight","Gracie","!!!"]
> substitute :: (Monad f, Eq a) => a -> f a -> f a -> f a
> substitute a p w = w >>= \b -> if a == b then p else return b
> {-# INLINE substitute #-}
> 
> -- | @'substituteVar' a b w@ replaces a free variable @a@ with another free variable @b@ in @w@.
> --
> -- >>> substituteVar "Alice" "Bob" ["Alice","Bob","Charlie"]
> -- ["Bob","Bob","Charlie"]
> substituteVar :: (Functor f, Eq a) => a -> a -> f a -> f a
> substituteVar a p = fmap (\b -> if a == b then p else b)
> {-# INLINE substituteVar #-}
> 
> -- | If a term has no free variables, you can freely change the type of
> -- free variables it is parameterized on.
> --
> -- >>> closed [12]
> -- Nothing
> --
> -- >>> closed ""
> -- Just []
> --
> -- >>> :t closed ""
> -- closed "" :: Maybe [b]
> closed :: Traversable f => f a -> Maybe (f b)
> closed = traverse (const Nothing)
> {-# INLINE closed #-}
> 
> -- | A closed term has no free variables.
> --
> -- >>> isClosed []
> -- True
> --
> -- >>> isClosed [1,2,3]
> -- False
> isClosed :: Foldable f => f a -> Bool
> isClosed = all (const False)
> {-# INLINE isClosed #-}
> 
> ------------------------------------

> data Idx :: Nat -> Type where
>    FZ :: Idx (S n)
>    FS :: Idx n -> Idx (S n)

> deriving instance Eq (Idx n)
> deriving instance Show (Idx n)

> toInt :: Idx n -> Int
> toInt FZ     = 0
> toInt (FS n) = 1 + toInt n

> shift :: SNat m -> Idx n -> Idx (Plus m n)
> shift n x = case n of 
>    SZ -> x
>    (SS m) -> FS (shift m x)


> ------------------------------------

> data Bind (a :: Nat -> Type -> Type) n b where
>    Bind :: !(Sub a m (S n) b) -> !(a m b) -> Bind a n b

> instance (forall m1 m2. Show (Sub a m1 m2 b), forall m1. Show (a m1 b)) => Show (Bind a n b) where
>    showsPrec p (Bind s a) = showString "Bind" . showsPrec p s . showString " " . showsPrec p a
> 
> instance (forall m. Show (a m b)) => Show (Sub a m n b) where
>    showsPrec p (Inc n) = showString "Inc " . showsPrec p n
>    showsPrec p (Cons x s) = showString "Cons " . showsPrec p x . showString " " . showsPrec p s
>    showsPrec p (s1 :<> s2) = showsPrec p s1 . showString " :<> " . showsPrec p s2


> instance (forall m1 m2. Functor (Sub a m1 m2), forall m1. Functor (a m1)) => Functor (Bind a n) where
>    fmap f (Bind s a) = Bind (fmap f s) (fmap f a)
> 
> instance (forall m. Functor (a m)) => Functor (Sub a m n) where
>    fmap f (Inc n) = Inc n
>    fmap f (Cons x s) = Cons (fmap f x) (fmap f s)
>    fmap f (s1 :<> s2) = fmap f s1 :<> fmap f s2

> {-
> instance (forall m1 m2. Applicative (Sub a m1 m2), forall m1. Applicative (a m1)) => Applicative (Bind a n) where
>    pure = return ; (<*>) = ap
> 
> instance (forall m. Applicative (a m)) => Applicative (Sub a m n) where
>    pure = return ; (<*>) = ap

> instance (forall m1 m2. Monad (Sub a m1 m2), forall m1. Monad (a m1)) => Monad (Bind a n) where
>    return x = Bind nil (return x)
>    Bind s a >>= k = Bind (s >>= k) (a >>= k)
> 
> instance (forall m. Monad (a m)) => Monad (Sub a m n) where
>    return x = single (return x)
>    Inc n >>= k = Inc n
>    Cons x s >>= k = Cons (x >>= k) (s >>= k)
>    (s1 :<> s2) >>= k = (s1 >>= k) :<> (s2 >>= k)
> -}



>

> instance (forall m1 m2. Foldable (Sub a m1 m2), forall m1. Foldable (a m1)) => Foldable (Bind a n) where
>    foldMap f (Bind s a) = foldMap f s <> foldMap f a
> 
> instance (forall m. Foldable (a m)) => Foldable (Sub a m n) where
>    foldMap f (Inc n) = mempty
>    foldMap f (Cons x s) = foldMap f x <> foldMap f s
>    foldMap f (s1 :<> s2) = foldMap f s1 <> foldMap f s2


> instance (forall m1 m2. Traversable (Sub a m1 m2), forall m1. Traversable (a m1)) => Traversable (Bind a n) where
>    traverse f (Bind s a) = Bind <$> traverse f s <*> traverse f a
> 
> instance (forall m. Traversable (a m)) => Traversable (Sub a m n) where
>    traverse f (Inc n) = pure $ Inc n
>    traverse f (Cons x s) = Cons <$> traverse f x <*> traverse f s
>    traverse f (s1 :<> s2) = (:<>) <$> traverse f s1 <*> traverse f s2


> bind :: a (S n) b -> Bind a n b
> bind = Bind (Inc Nat.zero)
> {-# INLINABLE bind #-}

> unbind :: SubstC a => Bind a n b -> a (S n) b 
> unbind (Bind s a) = subst s a
> {-# INLINABLE unbind #-}

> instantiate :: SubstC a => Bind a n b -> a n b -> a n b
> instantiate (Bind s a) b = subst (comp s (single b)) a
> {-# INLINABLE instantiate #-}

> substBind :: SubstC a => Sub a n m b -> Bind a n b -> Bind a m b
>   -- use comp instead of :<>
> substBind s2 (Bind s1 e) = Bind (comp s1 (lift s2)) e
> {-# INLINABLE substBind #-}

> instance (SubstC a, Eq (a (S n) b)) => Eq (Bind a n b) where
>    (Bind s1 x) == (Bind s2 y) = subst s1 x == subst s2 y

> ------------------------------------

> data Sub (a :: Nat -> Type -> Type) (n :: Nat) (m :: Nat) b where
>    Inc   :: !(SNat m) -> Sub a n (Plus m n) b             --  increment by m
>    Cons  :: a m b -> !(Sub a n m b) -> Sub a (S n) m b     --  extend a substitution (like cons)
>    (:<>) :: !(Sub a m n b) -> !(Sub a n p b) -> Sub a m p b  --  compose substitutions

> infixr :<>    -- like usual composition  (.)

> class SubstC (a :: Nat -> Type -> Type) where
>   var   :: Idx n -> a n b
>   subst :: Sub a n m b -> a n b -> a m b


> --  Value of the index x in the substitution s
> applyS :: SubstC a => Sub a n m b -> Idx n -> a m b
> applyS (Inc m)          x  = var (shift m x)
> applyS (Cons ty _s)    FZ  = ty
> applyS (Cons _ty s) (FS x) = applyS s x
> applyS (s1 :<> s2)      x  = subst s2 (applyS s1 x)
> {-# INLINABLE applyS #-}


> nil :: SubstC a => Sub a n n b
> nil = Inc Nat.zero
> {-# INLINABLE nil #-}

> lift :: SubstC a => Sub a n m b -> Sub a (S n) (S m) b
> lift s   = Cons (var FZ) (s :<> Inc (Nat.succ Nat.zero))
> {-# INLINABLE lift #-}

> single :: SubstC a => a n b -> Sub a (S n) n b
> single t = Cons t (Inc Nat.zero)
> {-# INLINABLE single #-}

> incSub :: Sub a n (S n) b
> incSub = Inc (Nat.succ Nat.zero)
> {-# INLINABLE incSub #-}

> -- smart constructor for composition
> comp :: SubstC a => Sub a m n b -> Sub a n p b -> Sub a m p b
> -- this one is difficult to type check
> -- comp (Inc k1) (Inc k2)  = Inc (k1 + k2)
> comp (Inc SZ) s       = s
> comp (Inc (SS n)) (Cons t s) = comp (Inc n) s
> comp s (Inc SZ)   = s
> comp (s1 :<> s2) s3 = comp s1 (comp s2 s3)
> comp (Cons t s1) s2 = Cons (subst s2 t) (comp s1 s2)
> comp s1 s2 = s1 :<> s2
> {-# INLINABLE comp #-}


> instance (forall n. NFData (a n b)) => NFData (Sub a m1 m2 b) where
>   rnf (Inc i) = rnf i
>   rnf (Cons t ts) = rnf t `seq` rnf ts
>   rnf (s1 :<> s2) = rnf s1 `seq` rnf s2

> instance (forall n. NFData (a n b)) => NFData (Bind a m b) where
>   rnf (Bind s a) = rnf s `seq` rnf a

> instance NFData (Idx a) where
>   rnf FZ = ()
>   rnf (FS s) = rnf s

