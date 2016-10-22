{-# LANGUAGE GADTs, ScopedTypeVariables, TypeOperators, DataKinds, FlexibleInstances, TypeFamilies, TypeApplications #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns -fno-warn-name-shadowing  #-}

module DataDynamic where  

import DataTypeable

-- |Data.Dynamic| ------------------------------


data Dynamic where
  ToDyn :: Typeable a => a -> Dynamic

toDyn :: Typeable a => a -> Dynamic          
toDyn = ToDyn

fromDynamic :: forall a. Typeable a => Dynamic -> Maybe a
fromDynamic (ToDyn (x :: b)) = case 
  eqT' (typeRep :: TypeRep a) (typeRep :: TypeRep b) of 
    Just Refl -> Just x
    Nothing   -> Nothing

fromDyn :: Typeable a => Dynamic -> a -> a
fromDyn d o = case fromDynamic d of 
  Just x  -> x
  Nothing -> o
  
showDynTypeRep :: Dynamic -> String
showDynTypeRep (ToDyn (x :: a)) = show (typeRep :: TypeRep a)

instance Typeable Dynamic where typeRep = TR $ TC ty "Dynamic"

instance Show Dynamic where
  show a = "<dyn of:" ++ showDynTypeRep a ++">"

---------------------------------------------------------------------------
-- decomposing type representations
    
dynFstWrong :: Dynamic -> Maybe Dynamic
dynFstWrong (ToDyn (x :: a)) = do
  Refl <- eqT' (typeRep :: TypeRep a) (typeRep :: TypeRep (Dynamic,Dynamic))
  return (ToDyn (fst x))

exampleWrong = do
  x <- dynFstWrong (toDyn ('c', 'a'))
  y <- fromDynamic x 
  return $ y == 'c'

dynFst :: Dynamic -> Maybe Dynamic    
dynFst (ToDyn (x :: pab) ) = do
  -- intuition, make sure that pab is a pair type,
  -- then call fst on it
  AppResult rpa (rb :: TypeRep b) <- splitApp (typeRep :: TypeRep pab)
  AppResult rp (ra :: TypeRep a)  <- splitApp rpa
  Refl       <- eqT' rp (typeRep :: TypeRep (,))
  return $ withTypeable ra (\p -> ToDyn (fst x))
  
example = do 
  x <- dynFst (toDyn ('c', 'a'))
  y <- fromDynamic x
  return $ y == 'c'
  
  
---------------------------------------------------------------------------
-- decomposing type representations

dynApp :: Dynamic -> Dynamic -> Maybe Dynamic    
dynApp (ToDyn (f :: tf)) (ToDyn (x :: tx)) = do
  -- intuition, make sure that pab is a pair type,
  -- then call fst on it
  AppResult rpa rb <- splitApp (typeRep :: TypeRep tf)
  AppResult rp ra  <- splitApp rpa
  Refl       <- eqT' rp (typeRep :: TypeRep (->))
  Refl       <- eqT' ra (typeRep :: TypeRep tx)
  return $ withTypeable rb (\p -> ToDyn (f x))

