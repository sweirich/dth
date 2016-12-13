{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}


-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using Partial Derivatives

-- So far, inefficient version only
-- Type system keeps track of the named matches that can be
-- produced by the regexp
-- Doesn't allow marking inside of Kleene-*

import Data.Kind (Type)

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import Data.Typeable

import Unsafe.Coerce                  
----
----

data Occ = Fin Nat | Inf
data SOcc (o :: Occ) where
  SFin :: SNat n -> SOcc (Fin n)
  SInf :: SOcc Inf

data instance Sing (n :: Occ) = SOcc

{-                                
sequOcc :: Occ -> Occ -> Occ
sequOcc (Fin i) (Fin j) = Fin (i + j)
sequOcc (Fin i) Inf = Inf
sequOcc Inf (Fin i) = Inf
sequOcc Inf Inf     = Inf

altOcc :: Occ -> Occ -> Occ
altOcc (Fin i) (Fin j) = Fin (max i j)
altOcc (Fin i) Inf = Inf
altOcc Inf (Fin i) = Inf
altOcc Inf Inf     = Inf
-}

sMaxNat :: SNat i -> SNat j -> SNat (Max i j)
sMaxNat si sj = unsafeCoerce k where
  k :: Integer
  k = max (fromSing si) (fromSing sj)

sAltOcc :: SOcc o1 -> SOcc o2 -> SOcc (Alt o1 o2)
sAltOcc (SFin i) (SFin j) = SFin (sMaxNat i j)
sAltOcc SInf SInf         = SInf
sAltOcc (SFin i) SInf     = SInf
sAltOcc SInf (SFin j)     = SInf


sSequOcc :: SOcc o1 -> SOcc o2 -> SOcc (Sequ o1 o2)
sSequOcc (SFin i) (SFin j) = SFin (i %:+ j)
sSequOcc SInf SInf         = SInf
sSequOcc (SFin i) SInf     = SInf
sSequOcc SInf (SFin j)     = SInf
                    
type family Fail  (k :: Type) :: k
type family Empty (k :: Type) :: k
type family Sequ  (m :: k) (n :: k) :: k
type family Alt   (m :: k) (n :: k) :: k
type family Star  (m :: k) :: k

type instance Sequ (Fin i :: Occ) (Fin j) = Fin (i + j)
type instance Sequ (Fin i) Inf = Inf
type instance Sequ Inf (Fin i) = Inf
type instance Sequ Inf Inf     = Inf

type instance Alt (Fin i :: Occ) (Fin j) = Fin (Max i j)
type instance Alt (Fin i) Inf = Inf
type instance Alt Inf (Fin i) = Inf
type instance Alt Inf Inf     = Inf

type instance Star (m :: Occ)  = Inf

type S = [(Symbol,Occ)]

data SS (s :: S) where
  SSNil :: SS '[]
  SSCons :: KnownSymbol s => proxy s -> SOcc o -> SS ss -> SS ('(s,o)':ss)


type instance Empty S = '[]

-- sequencing

type instance Sequ (l1 :: [(Symbol,k)]) (l2 :: [(Symbol,k)]) = SequAL l1 l2

type family SequAL (l1 :: [(Symbol,k)]) (l2 :: [(Symbol,k)]) :: [(Symbol,k)] where
    SequAL '[] '[] = '[]
    SequAL ('(s1,o1)':t1) ('(s2,o2)':t2) = MergeHelper (Compare s1 s2) s1 o1 t1 s2 o2 t2
    SequAL m '[] = m
    SequAL '[] m = m

type family MergeHelper (ord :: Ordering) s1 o1 t1 s2 o2 t2 :: [(Symbol,Occ)]  where
    MergeHelper EQ s o1 t1 s o2 t2   = '(s,Sequ o1 o2)': Sequ t1 t2
    MergeHelper LT s1 o1 t1 s2 o2 t2 = '(s1,o1) ': Sequ t1 ('(s2,o2)':t2)
    MergeHelper GT s1 o1 t1 s2 o2 t2 = '(s2,o2) ': Sequ ('(s1,o1)':t1) t2

    
type instance Sequ (Just l1) (Just l2) = Just (SequAL l1 l2)
type instance Sequ Nothing (Just l2)   = Nothing
type instance Sequ (Just l1) Nothing   = Nothing
type instance Sequ Nothing Nothing     = Nothing


sSequAL :: SS l1 -> SS l2 -> SS (SequAL l1 l2)
sSequAL SSNil SSNil = SSNil
sSequAL (SSCons (ps :: p1 s) o1 t1) (SSCons (pt :: p2 t) o2 t2) =
  case (sym @s %~ sym @t) of
  Proved Refl -> SSCons ps (sSequOcc o1 o2) (sSequAL t1 t2)
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> SSCons ps o1 (sSequAL t1 (SSCons pt o2 t2))
    SGT -> SSCons pt o2 (sSequAL (SSCons ps o1 t1) t2)
sSequAL m SSNil = m
sSequAL SSNil m = m


-- alternation

type instance Alt (l1 :: [(Symbol,k)]) (l2 :: [(Symbol,k)]) = AltAL l1 l2

type family AltAL (l1 :: [(Symbol,k)]) (l2 :: [(Symbol,k)]) :: [(Symbol,k)] where
  AltAL '[] '[] = '[]
  AltAL ('(s1,o1)':t1) ('(s2,o2)':t2) = AltALHelper (Compare s1 s2) s1 o1 t1 s2 o2 t2
  AltAL m '[] = m
  AltAL '[] m = m

type family AltALHelper (ord :: Ordering) s1 o1 t1 s2 o2 t2 :: [(Symbol,Occ)]  where
    AltALHelper EQ s o1 t1 s o2 t2   = '(s,Alt o1 o2)': Alt t1 t2
    AltALHelper LT s1 o1 t1 s2 o2 t2 = '(s1,o1) ': Alt t1 ('(s2,o2)':t2)
    AltALHelper GT s1 o1 t1 s2 o2 t2 = '(s2,o2) ': Alt ('(s1,o1)':t1) t2

type instance Alt (Just l1) (Just l2) = Just (AltAL l1 l2)
type instance Alt Nothing (Just l2)   = Just l2
type instance Alt (Just l1) Nothing   = Just l1
type instance Alt Nothing Nothing     = Nothing

sAltAL :: SS m1 -> SS m2 -> SS (AltAL m1 m2)
sAltAL SSNil SSNil = SSNil
sAltAL (SSCons (ps :: p1 s) o1 t1) (SSCons (pt :: p2 t) o2 t2) =
  case (sym @s %~ sym @t) of
  Proved Refl -> SSCons ps (sAltOcc o1 o2) (sAltAL t1 t2)
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> SSCons ps o1 (sAltAL t1 (SSCons pt o2 t2))
    SGT -> SSCons pt o2 (sAltAL (SSCons ps o1 t1) t2)
sAltAL m SSNil = m
sAltAL SSNil m = m

-- Star

type family StarAL (l1 :: [(Symbol,k)]) where
  StarAL '[] = '[]
  StarAL ('(s1,o1)':t1) = '(s1, Star o1)': StarAL t1

type instance Star (l :: [(Symbol,k)]) = StarAL l
--type instance Star (Just l1) = Just (Star l1)
--type instance Star Nothing   = Nothing

sStar :: SS m -> SS (StarAL m)
sStar SSNil             = SSNil
sStar (SSCons s1 o1 t1) = SSCons s1 SInf (sStar t1)


-------------------------------------------------------------------------
-------------------------------------------------------------------------

 -- A data structure containing *at most* (n+1) strings
data FinList (n :: Nat) where
  FNil  :: FinList n
  FCons :: String -> FinList n -> FinList (1 + n)

axiomWeakenPlus :: FinList n -> FinList (m + n)
axiomWeakenPlus fn = unsafeCoerce fn

axiomWeakenMax :: forall m n. FinList n -> FinList (Max m n)
axiomWeakenMax fn = unsafeCoerce fn

axiomWeakenMax2 :: forall n m. FinList m -> FinList (Max m n)
axiomWeakenMax2 fn = unsafeCoerce fn

fappend :: FinList n -> FinList m -> FinList (n + m)
fappend FNil         gs = (axiomWeakenPlus gs)
fappend (FCons s fs) gs = FCons s (fappend fs gs)

toList :: FinList n -> [String]
toList FNil = []
toList (FCons s ss) = s:toList ss

data Group (o :: Occ) where
  Bo   :: FinList n -> Group (Fin n)
  Un   :: [String]  -> Group Inf

defaultGroup :: SOcc o -> Group o
defaultGroup (SFin i) = Bo FNil
defaultGroup SInf     = Un []

weakenGroupLeft :: SOcc (o1 :: Occ) -> Group (o2 :: Occ) -> Group (Alt o1 o2)
weakenGroupLeft (SFin (i :: SNat i)) (Bo m) = Bo (axiomWeakenMax @i m)
weakenGroupLeft (SFin i)  (Un l) = Un l
weakenGroupLeft SInf      (Bo m) = Un (toList m)
weakenGroupLeft SInf      (Un l) = Un l

weakenGroupRight :: Group (o1 :: Occ) -> SOcc (o2 :: Occ) -> Group (Alt o1 o2)
weakenGroupRight (Bo m) (SFin (i :: SNat i)) = Bo (axiomWeakenMax2 @i m)
weakenGroupRight (Un l) (SFin i) = Un l
weakenGroupRight (Bo m)    SInf   = Un (toList m)
weakenGroupRight (Un l)    SInf   = Un l


data Dict (ss :: S) where
  Nil  :: Dict (Empty S)
  Cons :: KnownSymbol s => proxy s -> Group o -> Dict ss -> Dict  ('(s,o)': ss)

instance Show (FinList n) where
  show FNil           = ""
  show (FCons s FNil) = s
  show (FCons s fs)   = s ++ "," ++ show fs
instance Show (Group o) where
  show (Bo fn) = show fn
  show (Un ls) = show ls
instance Show (Dict '[]) where
  show Nil = ""
instance Show (Dict ss) => Show (Dict ('(s,o):ss)) where
  show (Cons (ps :: p s1) g ss) = "{" ++ show (symbolVal ps) ++ "=" ++ show g ++ "}" ++  show ss


altGroup :: Group o1 -> Group o2 -> [Group (Alt o1 o2)]
altGroup (Bo (fn1 :: FinList m))(Bo (fn2 :: FinList n)) =
  [ Bo (axiomWeakenMax2 @n fn1), Bo (axiomWeakenMax @m fn2) ]
altGroup (Bo s1) (Un s2)  = [ Un (toList s1), Un s2]
altGroup (Un s1) (Bo fn2) = [ Un s1, Un (toList fn2)]
altGroup (Un s1) (Un s2)  = [ Un s1, Un s2 ]

alt :: Dict s1 -> Dict s2 -> [Dict (Alt s1 s2)]
alt Nil Nil = [Nil]
alt (Cons ps g1 d1) Nil = [Cons ps g1 d1]
alt Nil (Cons ps g1 d1) = [Cons ps g1 d1]
alt (Cons (ps :: p1 s) g1 m1) (Cons (pt :: p2 t) g2 m2) = case (sym @s %~ sym @t) of
  Proved Refl -> [Cons ps g d|  d <- alt m1 m2,  g <- altGroup g1 g2]
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> fmap (Cons ps g1) (alt m1 (Cons pt g2 m2))
    SGT -> fmap (Cons pt g2) (alt (Cons ps g1 m1) m2)


defaultDict :: SS s -> Dict s
defaultDict SSNil = Nil
defaultDict (SSCons (ps :: proxy s) o1 ss) =
   Cons ps (defaultGroup o1) (defaultDict ss)
   
weakenDictLeft :: forall s1 s2. SS s1 -> Dict s2 -> Dict (Alt s1 s2)
weakenDictLeft SSNil Nil = Nil
weakenDictLeft (SSCons (ps :: proxy s) o1 ss) Nil =
   Cons ps (defaultGroup o1) (weakenDictLeft ss Nil)
weakenDictLeft SSNil (Cons (pt :: p' t) g2 dd) =
   Cons pt g2 (weakenDictLeft SSNil dd)
weakenDictLeft (SSCons (ps :: proxy s) o1 ss) (Cons (pt :: p' t) g2 dd) =
  case (sym @s %~ sym @t) of
   Proved Refl ->
     Cons pt (weakenGroupLeft o1 g2) $ weakenDictLeft ss dd
   Disproved _ -> case (sCompare (sym @s) (sym @t)) of
     SLT -> Cons ps (defaultGroup o1) (weakenDictLeft ss (Cons pt g2 dd))
     SGT -> Cons pt g2 (weakenDictLeft (SSCons ps o1 ss) dd)

weakenDictRight :: forall s2 s1. SS s2 -> Dict s1 -> Dict (Alt s1 s2)
weakenDictRight SSNil Nil = Nil
weakenDictRight (SSCons (ps :: proxy s) o1 ss) Nil =
   Cons ps (defaultGroup o1) (weakenDictRight ss Nil)
weakenDictRight SSNil (Cons (pt :: p' t) g2 dd) =
   Cons pt g2 (weakenDictRight SSNil dd)
weakenDictRight (SSCons (ps :: proxy s) o1 ss) (Cons (pt :: p' t) g2 dd) =
  case (sym @t %~ sym @s) of
   Proved Refl ->
     Cons pt (weakenGroupRight g2 o1) $ weakenDictRight ss dd
   Disproved _ -> case (sCompare (sym @t) (sym @s)) of
     SGT -> Cons ps (defaultGroup o1) (weakenDictRight ss (Cons pt g2 dd))
     SLT -> Cons pt g2 (weakenDictRight (SSCons ps o1 ss) dd)



sequGroup :: Group o1 -> Group o2 -> Group (Sequ o1 o2)
sequGroup (Bo fn1) (Bo fn2) = Bo (fappend fn1 fn2)
sequGroup (Bo s1) (Un s2)   = Un (toList s1 ++ s2)
sequGroup (Un s1) (Bo fn2)  = Un (s1 ++ toList fn2)
sequGroup (Un s1) (Un s2)   = Un (s1 ++ s2)

sequ :: Dict s1 -> Dict s2 -> Dict (Sequ s1 s2)
sequ Nil Nil = Nil
sequ (Cons ps g1 d1) Nil = (Cons ps g1 d1)
sequ Nil (Cons ps g1 d1) = (Cons ps g1 d1)
sequ (Cons (ps :: p1 s) g1 m1) (Cons (pt :: p2 t) g2 m2) = case (sym @s %~ sym @t) of
  Proved Refl -> Cons ps (sequGroup g1 g2) (sequ m1 m2)
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> Cons ps g1 (sequ m1 (Cons pt g2 m2))
    SGT -> Cons pt g2 (sequ (Cons ps g1 m1) m2)


-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- Singleton symbol
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s

data R (ss :: S) where
  Rempty :: R (Empty S)
  Rvoid  :: R (Empty  S)
  Rseq   :: R s1 -> R s2 -> R (Sequ s1 s2)
  Ralt   :: R s1 -> R s2 -> R (Alt s1 s2)
  Rstar  :: R s  -> R (Star s)
  Rchar  :: Char -> R (Empty S)
  Rmark  :: KnownSymbol s => proxy s -> String -> R (Empty S) -> R ( '[ '(s, Fin 1) ])

toSingR :: R ss -> SS ss
toSingR Rempty = SSNil
toSingR Rvoid  = SSNil
toSingR (Rseq r1 r2) = sSequAL (toSingR r1) (toSingR r2)
toSingR (Ralt r1 r2) = sAltAL  (toSingR r1) (toSingR r2)
toSingR (Rstar r)    = sStar (toSingR r)
toSingR (Rchar c)    = SSNil
toSingR (Rmark (ps :: p s) _ _) = SSCons (sym @s) (SFin (SNat @1)) SSNil

instance Show (R n) where
  show Rempty = "ε"
  show Rvoid  = "∅"   
  show (Rseq r1 r2)   = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = [c]
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

r1 :: R (Empty S)
r1 = Ralt (Rchar 'a') (Rchar 'b')

--r2 :: R '[ '("a", String) ]
r2 = Rmark (sym @"a") "" r1

--r4 :: R '[ '("b", [String]) ]
r4 = Rstar (Rmark (sym @"b") "" (Rseq r1 r1))

r5 :: R '[ '("b", 'Fin 1) ]
r5 = Ralt (Rmark (sym @"b") "" (Rchar 'a')) (Rmark (sym @"b") "" (Rchar 'b'))

r6 :: R ('[ '("a", Fin 1), '("b", Fin 1) ])
r6 = Ralt (Rmark (sym @"a") "" (Rchar 'a')) (Rmark (sym @"b") "" (Rchar 'b'))

-- r7 :: R '[ '("b", 'Fin 1) ]
r7 = Ralt (Rmark (sym @"b") "" (Rchar 'b')) (Rmark (sym @"b") "" (Rchar 'b'))

-------------------------------------------------------------------------
-------------------------------------------------------------------------

axiom :: Alt m m :~: m
axiom = unsafeCoerce Refl

axiomDistrib :: Star s :~: (SequAL s (Star s))
axiomDistrib = unsafeCoerce Refl


match :: R m -> String -> Maybe [Dict m]
match r w = extract (deriveWord r w)

deriveWord :: R n -> String -> R n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 

extract :: R m -> Maybe [Dict m]
extract Rempty       = return [Nil]
extract Rvoid        = Nothing
extract (Rchar c)    = return [Nil]
extract (Rseq r1 r2) = do
  s1 <- extract r1
  s2 <- extract r2
  return $ [ sequ v1 v2 | v1 <- s1, v2 <- s2 ]
extract (Ralt (r1 :: R m1) (r2 :: R m2)) = case (extract r1, extract r2) of
  (Just s1, Just s2) -> Just (concat [ alt v1 v2 | v1 <- s1, v2 <- s2 ])
  (Just s1, Nothing) -> Just (map (weakenDictRight (toSingR r2)) s1)
  (Nothing, Just s2) -> Just (map (weakenDictLeft (toSingR r1)) s2)
  (Nothing, Nothing) -> Nothing
  
extract (Rstar r)      = return [ defaultDict (toSingR (Rstar r)) ]
extract (Rmark _ s r)  = if nullable r then 
  return [Cons Proxy (Bo (FCons s FNil)) Nil] else Nothing

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rempty         = True
nullable (Rchar c)      = False
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Rstar re)     = True
nullable Rvoid          = False
nullable (Rmark _ _ r)  = nullable r


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: R n -> R n
markEmpty (Rmark p w r) | nullable r = (Rmark p w Rempty)
markEmpty (Rmark p w r) = Rmark p w Rvoid
markEmpty (Ralt r1 r2)  = Ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = Rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = Rstar (markEmpty r)
markEmpty r             = r  

deriv :: forall n. R n -> Char -> R n
deriv (Rchar s)    c   = if s == c then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1, Refl <- axiom @n = 
     Ralt (Rseq (deriv r1 c) r2) (Rseq (markEmpty r1) (deriv r2 c))
deriv (Rstar (r :: R s)) c | Refl <- axiomDistrib @s =
     (Rseq (deriv r c) (Rstar r))
deriv (Rseq r1 r2) c   = Rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = Ralt (deriv r1 c) (deriv r2 c)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)

  
{-                    
class Kleene a where
  alt   :: a -> a -> a
  sequ  :: a -> a -> a
  void  :: a
  empty :: a

instance Kleene a => Kleene (Maybe a) where
  void = Nothing

  empty = Just empty

  alt (Just x) (Just y) = Just (alt x y)
  alt (Just x) Nothing  = Just x
  alt Nothing (Just y)  = Just y
  alt Nothing Nothing   = Nothing

  sequ (Just x) (Just y) = Just (sequ x y)
  sequ _ _ = Nothing


instance Kleene Occ where
  void    = Fin 0
  empty   = Fin 0

  sequ (Fin i)(Fin j) = Fin (i + j)
  sequ _ _ = Inf

  alt (Fin i) (Fin j) = Fin (max i j)
  alt _ _ = Inf
-}
