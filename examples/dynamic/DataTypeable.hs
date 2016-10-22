{-# LANGUAGE RankNTypes, PolyKinds, TypeOperators, ScopedTypeVariables,
             GADTs, MultiParamTypeClasses, ConstraintKinds,
             FunctionalDependencies, FlexibleContexts,
             AllowAmbiguousTypes,
             FlexibleInstances, TypeInType, UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-missing-methods #-}

module DataTypeable where

import GHC.Types hiding (TyCon)
import Unsafe.Coerce (unsafeCoerce)

-- eqT = undefined
cmpT = undefined
-- mkTyApp = undefined
-- splitApp = undefined
tyConPackage = undefined
tyConModule = undefined
-- tyConName = undefined
-- withTypeable = undefined
-- kindRep = undefined

-- Related definitions --------------------------------------------------------

data Proxy a where
  Proxy :: Proxy a

-- Informative propositional equality
data (a :: k1) :~: (b :: k2) where
  Refl :: forall k (a :: k). a :~: a

-- An informative ordering type, asserting type equality in the |EQ| case
data OrderingT a b where
  LTT  :: OrderingT a b
  EQT  :: OrderingT t t
  GTT  :: OrderingT a b

-- |Data.Typeable| ------------------------------------------------------------
data TyCon (a :: k) = TC (TypeRep k) String
  
  
data TypeRep (a :: k) where
  TR   :: TyCon a -> TypeRep a 
  TApp :: TypeRep a -> TypeRep b -> TypeRep (a b)

instance Show  (TypeRep a) where
  show (TR (TC _ ty))      = ty
  show (TApp t1 t2@(TR _)) = show t1 ++ " " ++ show t2 
  show (TApp t1 t2)        = show t1 ++ " (" ++ show t2  ++ ")"


class Typeable (a :: k) where
   typeRep :: TypeRep a
   -- Typeable instances automatically generated for all type constructors

ty :: TypeRep Type
ty = TR $ TC ty "Type"

tyA :: TypeRep (->)
tyA = TR $ TC tyTTT "(->)" where
  tyTTT :: TypeRep (Type -> (Type -> Type))
  tyTTT = TApp (TApp tyA ty) (TApp (TApp tyA ty) ty)

tyP :: TypeRep (,)
tyP = TR $ TC tyTTT "(,)" where
  tyTTT :: TypeRep (Type -> (Type -> Type))
  tyTTT = TApp (TApp tyA ty) (TApp (TApp tyA ty) ty)


instance Typeable (Type :: Type) where 
  typeRep = ty 

instance Typeable Char where typeRep = TR $ TC ty "Char" 
instance Typeable Int where typeRep = TR $ TC ty "Int"
instance Typeable Bool where typeRep = TR $ TC ty "Bool"
instance Typeable (,) where typeRep = tyP
instance Typeable (->) where typeRep = tyA
instance (Typeable (a :: k1 -> k2), Typeable (b :: k1)) => Typeable (a b) where
  typeRep = TApp typeRep typeRep

{-------------- withTypeable (horrible hack) -------------------}
  
newtype NT a r = NT (Typeable a => Proxy a -> r)

withTypeable :: forall a r. TypeRep a -> (Typeable a => Proxy a -> r) -> r
withTypeable a f = unsafeCoerce (NT f :: NT a r) a Proxy
{-# INLINE withTypeable #-}

-- existential version
data TypeRepX where
   TypeRepX :: TypeRep a -> TypeRepX
instance Eq    TypeRepX
instance Ord   TypeRepX
instance Show  TypeRepX

kindRep :: TypeRep (a :: k) -> TypeRep k
kindRep (TR (TC kr _)) = kr
kindRep (TApp t1 _) = undefined {- case kindRep t1 of 
  (TApp (TApp _ kr) _) -> kr
  _ -> error "BUG!" -}

-- comparison
eqT ::  forall k1 k2 (a :: k1) (b :: k2). (Typeable a, Typeable b) => Maybe (a :~: b)
eqT = eqT' typeRep typeRep

eqT'   :: forall k1 k2 (a :: k1) (b :: k2). TypeRep a -> TypeRep b -> Maybe (a :~: b)
eqT' (TR (TC _ s1))  (TR (TC _ s2)) | s1 == s2 = unsafeCoerce (Just Refl)
eqT' (TApp ta1 ta2) (TApp tb1 tb2) = do
  Refl <- eqT' ta1 tb1 
  Refl <- eqT' ta2 tb2 
  return Refl
eqT' _ _ = Nothing

cmpT  ::  TypeRep a -> TypeRep b -> OrderingT a b

-- construction
mkTyApp :: TypeRep a -> TypeRep b -> TypeRep (a b)
mkTyApp = TApp

-- pattern matching
splitApp :: TypeRep a -> Maybe (AppResult a)
splitApp (TApp t1 t2) = Just $ AppResult t1 t2
splitApp _ = Nothing

data AppResult (t :: k) where
  AppResult :: TypeRep a -> TypeRep b -> AppResult (a b)

-- information about the ``head'' type constructor
tyConPackage  :: TypeRep a -> String
tyConModule   :: TypeRep a -> String
tyConName     :: TypeRep a -> String
tyConName (TR (TC _ n)) = n
tyConName (TApp t1 _)   = tyConName t1

cast :: forall a b. (Typeable a, Typeable b) => a -> Maybe b
cast x = case eqT' (typeRep :: TypeRep a) (typeRep :: TypeRep b) of 
  Just Refl -> Just x
  Nothing   -> Nothing
  
gcast :: forall a b c. (Typeable a, Typeable b) => c a -> Maybe (c b)
gcast x = case eqT' (typeRep :: TypeRep a) (typeRep :: TypeRep b) of 
  Just Refl -> Just x
  Nothing   -> Nothing

