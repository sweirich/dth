> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE InstanceSigs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE StandaloneDeriving #-}
> {-# LANGUAGE TypeApplications #-}
> {-# LANGUAGE TypeInType #-}
> {-# LANGUAGE TypeFamilies #-}

> {-# OPTIONS_GHC -Wno-name-shadowing -Wno-unticked-promoted-constructors #-}

> module Nat
>    ( -- * Nat type
>      Nat(..)
>      -- * Basic arithmetic
>      , Plus, Minus, Mul,  Max, Min
>      , zero, succ, pred
> 
>      -- * Counting
>      , Repeat
>      -- , repeatP
>      -- * Comparisons
>      , Le, Lt, Gt, Ge
> 
>      -- * Runtime representation
>      , SNat(..)
>      , fromNat
>      , toSomeNat
> 
>      -- * Re-exports
>      , TestEquality(..)
>      , (:~:)(..)
>      , SingI(..), Sing
>      , Some(..)
>      , NFData(..)
>
> ) where
>
> import Prelude hiding (succ, pred)
> import Data.Type.Equality
> import Data.Singletons
> import Control.DeepSeq
> import Data.Some

> ------------------------------------------------------------------------
> -- * Peano arithmetic


> data Nat = S Nat | Z
>
> -- | Addition
> type family Plus (a :: Nat) (b :: Nat) :: Nat where
>   Plus Z     b = b
>   Plus (S a) b = S (Plus a b)
> 
> -- | Subtraction
> type family Minus (a :: Nat) (b :: Nat) :: Nat where
>   Minus Z     b     = Z
>   Minus (S a) (S b) = Minus a b
>   Minus a    Z      = a
> 
> -- | Multiplication
> type family Mul (a :: Nat) (b :: Nat) :: Nat where
>   Mul Z     b = Z
>   Mul (S a) b = Plus a (Mul a b)
> 
> -- | Less-than-or-equal
> type family Le  (a :: Nat) (b :: Nat) :: Bool where
>   Le  Z  b        = 'True
>   Le  a  Z        = 'False
>   Le  (S a) (S b) = Le a b
> 
> -- | Less-than
> type family Lt  (a :: Nat) (b :: Nat) :: Bool where
>   Lt a b = Le (S a) b
> 
> -- | Greater-than
> type family Gt  (a :: Nat) (b :: Nat) :: Bool where
>   Gt a b = Le b a
> 
> -- | Greater-than-or-equal
> type family Ge  (a :: Nat) (b :: Nat) :: Bool where
>   Ge a b = Lt b a
> 
> -- | Maximum
> type family Max (a :: Nat) (b :: Nat) :: Nat where
>   Max Z b = b
>   Max a Z = a
>   Max (S a) (S b) = S (Max a b)
> 
> -- | Minimum
> type family Min (a :: Nat) (b :: Nat) :: Nat where
>   Min Z b = Z
>   Min a Z = Z
>   Min (S a) (S b) = S (Min a b)
> 
> -- | Apply a constructor 'f' n-times to an argument 's'
> type family Repeat (m :: Nat) (f :: k -> k) (s :: k) :: k where
>   Repeat Z f s     = s
>   Repeat (S m) f s = f (Repeat m f s)

> ------------------------------------------------------------------------
> -- * Run time representation 
> 
> data SNat a where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)
>
> zero :: SNat Z
> zero = SZ
>
> succ :: SNat n -> SNat (S n)
> succ = SS

> pred :: SNat (S n) -> SNat n
> pred (SS n) = n

> type instance Sing = SNat
>
> fromNat :: Integral a => SNat n -> a
> fromNat SZ = 0
> fromNat (SS n) = fromNat n + 1
>
> toSomeNat :: Integral n => n -> Maybe (Some SNat)
> toSomeNat 0 = Just $ Some $ SZ
> toSomeNat n = do
>   Some sn <- toSomeNat (n-1)
>   return (Some (SS sn))


> ----------------------------------------------------------
> -- * Class instances for SNat

> instance Eq (SNat m) where
>   _ == _ = True

> instance Ord (SNat m) where
>   compare x y = EQ

> -- show as Int, not in unary
> instance Show (SNat n) where
>   show n = show ((fromNat n) :: Int)

> instance TestEquality SNat where
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing

> instance SingI Z where sing = SZ
> instance SingI n => SingI (S n) where sing = SS sing

> instance NFData (SNat a) where
>    rnf SZ = ()
>    rnf (SS v) = rnf v
