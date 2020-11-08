> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE DataKinds #-}
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

> module Nat where
>
> import Data.Type.Equality

> data Nat = S Nat | Z 
> data SNat a where
>   SZ :: SNat Z
>   SS :: SNat n -> SNat (S n)
> deriving instance Show (SNat n)

> instance TestEquality SNat where
>   testEquality SZ SZ = Just Refl
>   testEquality (SS n) (SS m) 
>     | Just Refl <- testEquality n m
>     = Just Refl
>   testEquality _ _ = Nothing
