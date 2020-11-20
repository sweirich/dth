> {-|
> Description: Representations of a type-level natural at runtime.
> 
> -}
> 
> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE EmptyCase #-}
> {-# LANGUAGE ExplicitNamespaces #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE LambdaCase #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE NoStarIsType #-}
> {-# LANGUAGE PatternGuards #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE RankNTypes #-}
> {-# LANGUAGE RoleAnnotations #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE TypeOperators #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE UndecidableInstances #-}
> 
> module Peano
>    ( -- * Peano
>      Peano
>      , Z , S
> 
>      -- * Basic arithmetic
>      , Plus, Minus, Mul,  Max, Min
>      , plusP, minusP, mulP, maxP, minP
>      , zeroP, succP, predP
> 
>      -- * Counting
>      , Repeat
>      , repeatP
>      -- * Comparisons
>      , Le, Lt, Gt, Ge
> --     , leP, ltP, gtP, geP
> 
>      -- * Runtime representation
>      , SNat
>      , PeanoView(..), peanoView, viewRepr
> 
>      -- * 'Some Peano'
>      , peanoValue
>      , somePeano
>      , maxPeano
>      , minPeano
>      , peanoLength
> 
>      -- * Re-exports
>      , TestEquality(..)
>      , (:~:)(..)
>      , SingI(..), Sing
> 
>      ) where
> 
> import           Data.Word
> import           Unsafe.Coerce(unsafeCoerce)
> import           Data.Singletons
> import           Data.Type.Equality
> import           Data.Some
> import           Control.DeepSeq
> 
> 
> ------------------------------------------------------------------------
> -- * Peano arithmetic
> 
> -- | Unary representation for natural numbers
> data Peano = Z | S Peano
> -- | Peano zero
> type Z = 'Z
> -- | Peano successor
> type S = 'S
> 
> -- Peano numbers are more about *counting* than arithmetic.
> -- They are most useful as iteration arguments and list indices
> -- However, for completeness, we define a few standard
> -- operations.
> 
> 
> -- | Addition
> type family Plus (a :: Peano) (b :: Peano) :: Peano where
>   Plus Z     b = b
>   Plus (S a) b = S (Plus a b)
> 
> -- | Subtraction
> type family Minus (a :: Peano) (b :: Peano) :: Peano where
>   Minus Z     b     = Z
>   Minus (S a) (S b) = Minus a b
>   Minus a    Z      = a
> 
> -- | Multiplication
> type family Mul (a :: Peano) (b :: Peano) :: Peano where
>   Mul Z     b = Z
>   Mul (S a) b = Plus a (Mul a b)
> 
> -- | Less-than-or-equal
> type family Le  (a :: Peano) (b :: Peano) :: Bool where
>   Le  Z  b        = 'True
>   Le  a  Z        = 'False
>   Le  (S a) (S b) = Le a b
> 
> -- | Less-than
> type family Lt  (a :: Peano) (b :: Peano) :: Bool where
>   Lt a b = Le (S a) b
> 
> -- | Greater-than
> type family Gt  (a :: Peano) (b :: Peano) :: Bool where
>   Gt a b = Le b a
> 
> -- | Greater-than-or-equal
> type family Ge  (a :: Peano) (b :: Peano) :: Bool where
>   Ge a b = Lt b a
> 
> -- | Maximum
> type family Max (a :: Peano) (b :: Peano) :: Peano where
>   Max Z b = b
>   Max a Z = a
>   Max (S a) (S b) = S (Max a b)
> 
> -- | Minimum
> type family Min (a :: Peano) (b :: Peano) :: Peano where
>   Min Z b = Z
>   Min a Z = Z
>   Min (S a) (S b) = S (Min a b)
> 
> -- | Apply a constructor 'f' n-times to an argument 's'
> type family Repeat (m :: Peano) (f :: k -> k) (s :: k) :: k where
>   Repeat Z f s     = s
>   Repeat (S m) f s = f (Repeat m f s)
> 
> ------------------------------------------------------------------------
> -- * Run time representation of Peano numbers
> 
> -- | The run time value, stored as an Word64
> -- As these are unary numbers, we don't worry about overflow.
> newtype SNat (n :: Peano) =
>   SNat { peanoValue :: Word64 }
> -- n is Phantom in the definition, but we don't want to allow coerce
> type role SNat nominal
> 
> type instance Sing = SNat
> 
> -- | When we have optimized the runtime representation,
> -- we need to have a "view" that decomposes the representation
> -- into the standard form.
> data PeanoView (n :: Peano) where
>   SZ :: PeanoView Z
>   SS :: SNat n -> PeanoView (S n)
> 
> -- | Test whether a number is Zero or Successor
> peanoView :: SNat n -> PeanoView n
> peanoView (SNat i) =
>   if i == 0
>   then unsafeCoerce SZ
>   else unsafeCoerce (SS (SNat (i-1)))
> {-# INLINE peanoView #-}
> 
> -- | convert the view back to the runtime representation
> viewRepr :: PeanoView n -> SNat n
> viewRepr SZ     = SNat 0
> viewRepr (SS n) = SNat (peanoValue n + 1)
> 
> 
> ----------------------------------------------------------
> -- * Class instances for SNat
> 
> instance Eq (SNat m) where
>   _ == _ = True
> 
> instance TestEquality SNat where
>   testEquality (SNat m) (SNat n)
>     | m == n = Just (unsafeCoerce Refl)
>     | otherwise = Nothing
> 
> -- Display as digits, not in unary
> instance Show (SNat p) where
>   show p = show (peanoValue p)
> 
> instance NFData (SNat a) where
>    rnf (SNat v) = rnf v
> 
> ----------------------------------------------------------
> -- * Implicit runtime Peano numbers
> 
> -- | Implicit runtime representation
> 
> instance SingI Z where
>   sing = viewRepr SZ
> instance (SingI n) => SingI (S n) where
>   sing = viewRepr (SS sing)
> 
> ----------------------------------------------------------
> -- * Operations on runtime numbers
> 
> 
> -- | Zero
> zeroP :: SNat Z
> zeroP = SNat 0
> {-# INLINABLE zeroP #-}
> 
> -- | Successor, Increment
> succP :: SNat n -> SNat (S n)
> succP (SNat i) = SNat (i+1)
> {-# INLINABLE succP #-}
> 
> -- | Get the predecessor (decrement)
> predP :: SNat (S n) -> SNat n
> predP (SNat i) = SNat (i-1)
> 
> -- | Addition
> plusP :: SNat a -> SNat b -> SNat (Plus a b)
> plusP (SNat a) (SNat b) = SNat (a + b)
> 
> -- | Subtraction
> minusP :: SNat a -> SNat b -> SNat (Minus a b)
> minusP (SNat a) (SNat b) = SNat (a - b)
> 
> -- | Multiplication
> mulP :: SNat a -> SNat b -> SNat (Mul a b)
> mulP (SNat a) (SNat b) = SNat (a * b)
> 
> -- | Maximum
> maxP :: SNat a -> SNat b -> SNat (Max a b)
> maxP (SNat a) (SNat b) = SNat (max a b)
> 
> -- | Minimum
> minP :: SNat a -> SNat b -> SNat (Min a b)
> minP (SNat a) (SNat b) = SNat (min a b)
> 
> {-
> 
> -- | Less-than-or-equal-to
> leP :: SNat a -> SNat b -> SBool (Le a b)
> leP  (SNat a) (SNat b) =
>   if a <= b then unsafeCoerce (TrueRepr)
>             else unsafeCoerce(FalseRepr)
> 
> -- | Less-than
> ltP :: SNat a -> SNat b -> SBool (Lt a b)
> ltP a b = leP (succP a) b
> 
> -- | Greater-than-or-equal-to
> geP :: SNat a -> SNat b -> SBool (Ge a b)
> geP a b = ltP b a
> 
> -- | Greater-than
> gtP :: SNat a -> SNat b -> SBool (Gt a b)
> gtP a b = leP b a
> 
> -}
> 
> -- | Apply a constructor 'f' n-times to an argument 's'
> repeatP :: SNat m -> (forall a. repr a -> repr (f a)) -> repr s -> repr (Repeat m f s)
> repeatP n f s = case peanoView n of
>   SZ   -> s
>   SS m -> f (repeatP m f s)
> 
> 
> ------------------------------------------------------------------------
> -- * Some SNat
> 
> -- | Convert a 'Word64' to a 'SNat'
> mkSNat :: Word64 -> Some SNat
> mkSNat n = Some (SNat n)
> 
> -- | Turn an @Integral@ value into a 'SNat'.  Returns @Nothing@
> --   if the given value is negative.
> somePeano :: Integral a => a -> Maybe (Some SNat)
> somePeano x | x >= 0 = Just . mkSNat $! fromIntegral x
> somePeano _ = Nothing
> 
> -- | Return the maximum of two representations.
> maxPeano :: SNat m -> SNat n -> Some SNat
> maxPeano x y = Some (maxP x y)
> 
> -- | Return the minimum of two representations.
> minPeano :: SNat m -> SNat n -> Some SNat
> minPeano x y = Some (minP x y)
> 
> -- | List length as a Peano number
> peanoLength :: [a] -> Some SNat
> peanoLength [] = Some zeroP
> peanoLength (_:xs) = case peanoLength xs of
>   Some n -> Some (succP n)
> 


------------------------------------------------------------------------
--  LocalWords:  SNat runtime Peano unary
