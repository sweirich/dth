{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes, ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, MultiParamTypeClasses, FunctionalDependencies,
    FlexibleInstances, FlexibleContexts, ConstraintKinds #-}


-- A version of type-level maps, i.e. dictionaries indexed by lists
-- AKA records
-- Record labels are kept in order
-- Can construct via addition and joining


module Tmap where

import Data.Kind (Type, Constraint)
import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.TypeLits
import Data.Typeable

data Dict (m :: [(Symbol,Type)]) where
  Nil  :: Dict '[]
  Cons :: a -> Dict m -> Dict ('(s,a)':m)

class EqDict (m :: [(Symbol,Type)]) where
  eqDict :: Dict m -> Dict m -> Bool
instance EqDict '[] where
  eqDict Nil Nil = True
instance (KnownSymbol s, Eq a,EqDict m) => EqDict ('(s,a)':m) where
  eqDict (Cons x xs) (Cons y ys) = x == y && eqDict xs ys
instance (EqDict m) => Eq (Dict m) where
  (==) = eqDict 

class ShowDict (m :: [(Symbol,Type)]) where
  showDict :: Dict m -> String
instance ShowDict '[] where
  showDict Nil = ""
instance (KnownSymbol s, Show a,ShowDict m) => ShowDict ('(s,a)':m) where
  showDict (Cons x xs) =
     "{" ++ (symbolVal (sym @s)) ++ "=" ++ show x ++ "}" ++ showDict xs
instance (ShowDict m) => Show (Dict m) where
  show = showDict


data Index (s :: Symbol) (a :: Type) (m :: [(Symbol, Type)]) where
  DH :: Index s a ('(s,a)':m)
  DT :: Index s a m -> Index s a ('( t, b) ': m)

type family ShowMap (m :: [(Symbol,Type)]) :: ErrorMessage where
  ShowMap '[] = Text ""
  ShowMap ('(a,t) ': m) = Text "{ " :<>: Text a :<>: Text " : " :<>: ShowType t :<>: Text " }" :$$: ShowMap m

-- Using a closed type family to implement the partial function
type family Find (s :: Symbol) (m :: [(Symbol,Type)]) (m2 :: [(Symbol,Type)]) :: Index s a m where
  Find s ('(s , a) ': m) m2 = DH
  Find s ('(t , a) ': m) m2 = DT (Find s m m2)
  Find s '[] m2 = TypeError (Text "Field " :<>: Text s :<>: Text " not found in dict containing" :$$: Text "    " :<>: ShowMap m2)

t1 :: Find "a" '[ '("a", Int) ] '[] :~: DH
t1 = Refl

t2 :: Find "b" '[ '("a", Int), '("b", Bool) ] '[] :~: DT DH
t2 = Refl

-- Functional dependency between the kinds!
-- But we need this dependency to satify the functional dependendency
-- in the HasField class  | s m -> a
class Get (p :: Index s a m) | s m -> a where
  getp :: Dict m -> a
  updatep :: a -> Dict m -> Dict m
instance Get DH where
  getp (Cons v _ ) = v
  updatep nv (Cons _ xs) = Cons nv xs
instance (Get l) => Get (DT l) where
  getp    (Cons _ xs) = getp @_ @_ @_ @l xs
  updatep nv (Cons x xs) = Cons x (updatep @_ @_ @_ @l nv xs)


-- Eventually in GHC.Records
-- | x r -> a 
class HasField (x :: k) r a | x r -> a where
  getField :: r -> a
  updateField :: a -> r -> r 

-- Maybe GHC.Records can have this too
class AddField (x :: k) r a where
   type Insert x a r :: Type
   add :: a -> r -> Insert x a r


-- Instance for symbols and Dicts
instance (p ~ (Find s m m :: Index s a m), Get p) => HasField s (Dict m) a where
  getField = getp @_ @_ @_ @p
  updateField = updatep @_ @_ @_ @p

-- test case
d :: Dict '[ '("a", Int), '("b", Bool)]
d = Cons 2 (Cons True Nil)

get :: forall s m a. HasField s (Dict m) a => Dict m -> a
get = getField @s

x = get @"a" d
y = get @"b" d
-- c = get @"c" d


-- can we test for merge dynamically? need overlapping type classes? or what?

data InsertIndex (s :: Symbol) (a :: Type) (m :: [(Symbol, Type)]) where
  IN :: InsertIndex s a m
  IT :: InsertIndex s a m -> InsertIndex s a ('( t, b) ': m)

data instance Sing (ii :: InsertIndex s a m) = SInsertIndex

type family FindInsert (s :: Symbol) (a :: Type) (m :: [(Symbol,Type)] )
     :: InsertIndex s a m where
  FindInsert s a '[] = IN
  FindInsert s a ('(t,b)':m)  = Helper (CmpSymbol s t) s t a b m

type family Helper (o :: Ordering) s t (a :: Type) (b :: Type) (m :: [(Symbol,Type)] )
     :: InsertIndex s a ('(t,b)':m) where
  Helper EQ s s a b m = TypeError (Text "duplicate field " :<>: Text s)
  Helper LT s t a b m = IN
  Helper GT s t a b m = IT (FindInsert s a m)


type family InsertAt  (s :: Symbol) (a :: Type) (m :: [(Symbol,Type)] )
     (p :: InsertIndex s a m) where
  InsertAt s a m IN                = '(s,a)':m
  InsertAt s a ('(t,b) ':m) (IT p) = '(t,b) ': (InsertAt s a m p)



-- Static resolution (via type classes)

class AddP (p :: InsertIndex s a m) where
  addp :: a -> Dict m -> Dict (InsertAt s a m p)
instance AddP IN where
  addp x xs = (Cons x xs)
instance (AddP (p :: InsertIndex s a m)) => AddP (IT p) where
  addp x (Cons y xs) = Cons y (addp @s @a @m @p x xs)


instance (FindInsert s a m ~ (p :: InsertIndex s a m), AddP p) => AddField (s :: Symbol) (Dict m) a where
   type Insert s a (Dict m) = Dict (InsertAt s a m (FindInsert s a m))
   add = addp @s @a @m @p


a1 = add @"aa" 'c' d
x3 = get @"aa" a1

-- Glue two different dictionaries together
type Ins s a m = InsertAt s a m (FindInsert s a m)


-- dynamic insertion

-- Dynamic version
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s

data SInsertIndex (ii :: InsertIndex s a m) where
  SIN :: SInsertIndex IN
  SIT :: SInsertIndex ii -> SInsertIndex (IT ii)

data Dom (m :: [(Symbol,Type)]) where
  DNil  :: Dom '[]
  DCons :: forall a s m p1 p2. (KnownSymbol s) => p1 s -> p2 a -> Dom m -> Dom ( '(s,a) ': m )

class ShowDom m where
  showDom :: Dom m -> String
instance ShowDom '[] where  
  showDom DNil = ""
instance (Typeable a, ShowDom m) => ShowDom ( '(s,a) ': m ) where
  showDom (DCons ps _ dom) =
       "{" ++ (symbolVal ps) ++ ":" ++ showsTypeRep (typeRep @_ @a undefined) "" ++  "}" ++ show dom 

instance ShowDom m => Show (Dom m) where
  show = showDom

  
sFindInsert :: Sing (s :: Symbol) -> Dom m -> Maybe (SInsertIndex (FindInsert s a m))
sFindInsert ss DNil = return SIN
sFindInsert ss (DCons (p :: proxy t) _ m1) = case (ss %~ sym @t) of
      Proved Refl -> Nothing
      Disproved _ -> case (sCompare ss (sym @t)) of
        SLT -> return SIN
        SGT -> fmap SIT (sFindInsert ss m1)

sInsertDom :: forall s a m ii. (KnownSymbol s) =>
             SInsertIndex (ii :: InsertIndex s a m)
                -> Dom m -> (Dom (InsertAt s a m ii))
sInsertDom SIN  dom = (DCons (sym @s) Proxy dom)
sInsertDom (SIT ii) (DCons ss pa dom) = (DCons ss pa dom') where 
  dom' = sInsertDom ii dom 

addDom :: forall s a m. (KnownSymbol s) => Sing s ->  Dom m -> Maybe (Dom (Ins s a m))
addDom s dom = do
  ii <- sFindInsert s dom
  return $ sInsertDom @_ @a ii dom

sInsertAt :: forall s a m ii. (KnownSymbol s) =>
             a -> SInsertIndex (ii :: InsertIndex s a m)
                -> Dom m -> Dict m -> (Dom (InsertAt s a m ii),
                                       Dict (InsertAt s a m ii))
sInsertAt a SIN dom d = (DCons (sym @s) Proxy dom, Cons a d)
sInsertAt a (SIT ii) (DCons ss pa dom) (Cons b d)  =
  case sInsertAt a ii dom d of
    (dom, dict) -> (DCons ss pa dom, Cons b dict)

addD :: (KnownSymbol s) => Sing s -> a -> Dom m -> Dict m -> Maybe (Dom (Ins s a m),
                                                                    Dict (Ins s a m))
addD s a dom dict = do
  ii <- sFindInsert s dom
  return $ sInsertAt a ii dom dict



---------------------------


---------------------------

-- Only dynamic version of merging.  Perhaps we can 

type family Join (m1 :: [(Symbol,Type)]) (m2 :: [(Symbol, Type)]) where
  Join '[] m2          = m2
  Join ('(s,a)':m1) m2 = Ins s a (Join m1 m2) 



sJoinDom :: Dom m1 -> Dom m2 -> Maybe (Dom (Join m1 m2))
sJoinDom DNil d2                   = Just d2
sJoinDom (DCons (ps :: p1 s) (pa :: p2 a) d1) d2 = 
  do dom <- sJoinDom d1 d2
     addDom @s @a sym dom


sJoin :: forall m1 m2.
   Dom m1 -> Dom m2 -> Dict m1 -> Dict m2 -> Maybe (Dom (Join m1 m2),
                                                    Dict (Join m1 m2))
sJoin DNil         dom2 Nil            dict2 = Just (dom2, dict2)
sJoin (DCons (p :: p s) pa (dom1 :: Dom m1')) dom2 (Cons a dict1) dict2 =
  case (sJoin dom1 dom2 dict1 dict2) of
    Just (dom,dict) -> addD (sym @s) a dom dict
    Nothing -> Nothing


data A = MkA deriving (Typeable, Show)
data B = MkB deriving (Typeable, Show)
data C = MkC deriving (Typeable, Show)


dom1 = DCons @A (sym @"a") Proxy DNil
dict1 = (Cons MkA Nil)
dom2 = DCons @B (sym @"b") Proxy DNil
dict2 = Cons MkB Nil
dom3 = DCons @C (sym @"c") Proxy DNil
dict3 = Cons MkB Nil

foo = sJoin dom1 dom2 dict1 dict2


{-
type Join m1 m2 = JoinInsertAt m1 m2 (JoinFindIndex m1 m2)

data JoinIndex m1 m2 where
  JNil  :: JoinIndex '[] m2
  JCons :: InsertIndex s a (Join m1 m2)
              -> JoinIndex m1 m2 -> JoinIndex ('(s,a)':m1) m2

type family JoinInsertAt m1 m2 (p :: JoinIndex m1 m2) where
  

type family JoinFindIndex
    (m1 :: [(Symbol,Type)]) (m2 :: [(Symbol, Type)]) :: JoinIndex m1 m2 where
-}



{-
join :: Dict d1 -> Dict d2 -> Dict (Join d1 d2)
join Nil         d2 = d2
join (Cons (p :: Sing s) (v :: a) (d1 :: Dict m)) d2 = add @s v (join d1 d2)
-}

-- adding fields that already exist in the record is an error
-- a2 = add @"a" (2 :: Int) d



-- class AddField s (Dict m) a | s m -> a where
--   addField :: a -> Dict m -> (Dict (Insert s a m))





-- dInsert :: SSymbol s -> a -> Dict

-- dJoin :: Dict m1 -> Dict m2 -> Dict (Join m1 m2)
