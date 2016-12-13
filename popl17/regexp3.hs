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

-- For FinList
import qualified Data.Set as Set

import Kleene

---------------------------------------------
----

axiomDistribNat :: (1 + Max i j) :~: Max (1 + i) (1 + j)
axiomDistribNat = unsafeCoerce Refl

sMaxNat :: SNat i -> SNat j -> SNat (Max i j)
sMaxNat si sj = unsafeCoerce k where
  k :: Integer
  k = max (fromSing si) (fromSing sj)
---------------------------------------------
--
-- "Tropical Semi-ring"
-- natural numbers + infinity
-- with (+) and (max)
data Occ = Fin Nat | Inf

instance KKleene Occ where
   type Empty Occ = Fin 0
  
   type Sequ (Fin i :: Occ) (Fin j) = Fin (i + j)
   type Sequ f Inf = Inf
   type Sequ Inf f = Inf

   type Alt (Fin i :: Occ) (Fin j) = Fin (Max i j)
   type Alt f Inf = Inf
   type Alt Inf f = Inf

   type Star (m :: Occ) = Inf

instance Axiom (Fin k :: Occ) where
  axiomAltIdem = Refl
  axiomStar = Refl
  
instance Axiom (Inf   :: Occ) where
  axiomAltIdem = Refl
  axiomStar = Refl

data SOcc (o :: Occ) where
  SFin :: SNat n -> SOcc (Fin n)
  SInf :: SOcc Inf

instance IKleene SOcc where
   iempty = SFin (SNat @0)

   ialt (SFin i) (SFin j) = SFin (sMaxNat i j)
   ialt SInf     m        = SInf
   ialt m        SInf     = SInf

   isequ (SFin i) (SFin j) = SFin (i %:+ j)
   isequ SInf SInf         = SInf
   isequ (SFin i) SInf     = SInf
   isequ SInf (SFin j)     = SInf
   
   istar _ = SInf

---------------------------------------------
-- ? Can we generalize Occ -> k, Kleene k
-- 
type S = [(Symbol,Occ)]

instance KKleene [(Symbol,Occ)] where
   type Empty [(Symbol,Occ)] = '[]

   type Sequ '[] '[] = '[]
   type Sequ ('(s1,o1)':t1) ('(s2,o2)':t2) = MergeHelper (Compare s1 s2) s1 o1 t1 s2 o2 t2
   type Sequ m '[] = m
   type Sequ '[] m = m
   
   type Alt '[] '[] = '[]
   type Alt ('(s1,o1)':t1) ('(s2,o2)':t2) = AltALHelper (Compare s1 s2) s1 o1 t1 s2 o2 t2
   type Alt m '[] = m
   type Alt '[] m = m

   type Star '[] = '[]
   type Star ('(s1,o1)':t1) = '(s1, Star o1) ': Star t1

type family MergeHelper (ord :: Ordering) s1 o1 t1 s2 o2 t2 :: [(Symbol,Occ)]  where
    MergeHelper EQ s o1 t1 s o2 t2   = '(s,Sequ o1 o2)': Sequ t1 t2
    MergeHelper LT s1 o1 t1 s2 o2 t2 = '(s1,o1) ': Sequ t1 ('(s2,o2)':t2)
    MergeHelper GT s1 o1 t1 s2 o2 t2 = '(s2,o2) ': Sequ ('(s1,o1)':t1) t2

type family AltALHelper (ord :: Ordering) s1 o1 t1 s2 o2 t2 :: [(Symbol,Occ)]  where
    AltALHelper EQ s o1 t1 s o2 t2   = '(s,Alt o1 o2)': Alt t1 t2
    AltALHelper LT s1 o1 t1 s2 o2 t2 = '(s1,o1) ': Alt t1 ('(s2,o2)':t2)
    AltALHelper GT s1 o1 t1 s2 o2 t2 = '(s2,o2) ': Alt ('(s1,o1)':t1) t2


instance Axiom ('[] :: S) where
   axiomAltIdem = Refl
   axiomStar    = Refl
instance (Axiom (o :: Occ), Axiom (ss :: S)) => Axiom ('(s,o)':ss) where
   axiomAltIdem = case (axiomAltIdem @S @ss, axiomAltIdem @Occ @o) of
     (Refl,Refl) -> Refl
   axiomStar = case (axiomStar @S @ss, axiomStar @Occ @o) of
     (Refl,Refl) -> Refl

-- Singleton
data SS (so :: Occ -> Type) (s :: S) where
  SSNil :: SS so (Empty S)
  SSCons :: KnownSymbol s => proxy s -> so o -> SS so ss -> SS so ('(s,o)':ss)

instance IKleene so => IKleene (SS so) where
   iempty = SSNil

   isequ SSNil SSNil = SSNil
   isequ (SSCons (ps :: p1 s) o1 t1) (SSCons (pt :: p2 t) o2 t2) =
     case (sym @s %~ sym @t) of
       Proved Refl -> SSCons ps (isequ o1 o2) (isequ t1 t2)
       Disproved _ -> case (sCompare (sym @s) (sym @t)) of
         SLT -> SSCons ps o1 (isequ t1 (SSCons pt o2 t2))
         SGT -> SSCons pt o2 (isequ (SSCons ps o1 t1) t2)
   isequ m SSNil = m
   isequ SSNil m = m

   ialt SSNil SSNil = SSNil
   ialt (SSCons (ps :: p1 s) o1 t1) (SSCons (pt :: p2 t) o2 t2) =
     case (sym @s %~ sym @t) of
       Proved Refl -> SSCons ps (ialt o1 o2) (ialt t1 t2)
       Disproved _ -> case (sCompare (sym @s) (sym @t)) of
         SLT -> SSCons ps o1 (ialt t1 (SSCons pt o2 t2))
         SGT -> SSCons pt o2 (ialt (SSCons ps o1 t1) t2)
   ialt m SSNil = m
   ialt SSNil m = m

   istar SSNil             = SSNil
   istar (SSCons s1 o1 t1) = SSCons s1 (istar o1) (istar t1)


-------------------------------------------------------------------------
-------------------------------------------------------------------------

 -- A data structure containing *at most* (n+1) strings
data FinList (n :: Nat) where
  FNil  :: FinList n
  FCons :: Set.Set String -> FinList n -> FinList (1 + n)

axiomWeakenPlus :: FinList n -> FinList (m + n)
axiomWeakenPlus fn = unsafeCoerce fn

axiomWeakenMaxLeft :: forall m n. FinList n -> FinList (Max m n)
axiomWeakenMaxLeft fn = unsafeCoerce fn

axiomWeakenMaxRight :: forall n m. FinList m -> FinList (Max m n)
axiomWeakenMaxRight fn = unsafeCoerce fn

fappend :: FinList n -> FinList m -> FinList (n + m)
fappend FNil         gs = (axiomWeakenPlus gs)
fappend (FCons s fs) gs = FCons s (fappend fs gs)

toList :: FinList n -> [Set.Set String]
toList FNil = []
toList (FCons s ss) = s : toList ss

fmerge :: forall n m. FinList n -> FinList m -> FinList (Max n m)
fmerge FNil f = axiomWeakenMaxLeft @n f
fmerge f FNil = axiomWeakenMaxRight @m f
fmerge (FCons s1 (ss1 :: FinList n1)) (FCons s2 (ss2 :: FinList m1)) =
  case axiomDistribNat @n1 @m1 of
     Refl -> FCons (Set.union s1 s2) (fmerge ss1 ss2)
  -- ss1 :: FL n1  where n ~ 1 + n1
  -- ss2 :: FL m1  where m ~ 1 + m1
  -- WTP 1 + (Max n1 m1) ~ Max (1 + n1) (1 + m1)
instance Show (FinList n) where
  show FNil           = ""
  show (FCons s FNil) = show s
  show (FCons s fs)   = show s ++ "," ++ show fs

-------------------------------------------------------------------------
instance Kleene [Set.Set String] where
  empty = []
  sequ l1 l2 = l1 ++ l2

  alt [] x = x
  alt x [] = x
  alt (s1 : l1) (s2 : l2) = (Set.union s1 s2) : alt l1 l2

  star l = l ++ star l
-------------------------------------------------------------------------

data Group (o :: Occ) where
  Bo   :: FinList n         -> Group (Fin n)
  Un   :: [Set.Set String]  -> Group Inf

instance IKleene Group where
  iempty = Bo FNil

  isequ (Bo fn1) (Bo fn2) = Bo (fappend fn1 fn2)
  isequ (Bo s1) (Un s2)   = Un (toList s1 ++ s2)
  isequ (Un s1) (Bo fn2)  = Un (s1 ++ toList fn2)
  isequ (Un s1) (Un s2)   = Un (s1 ++ s2)

  ialt (Bo (fn1 :: FinList m))(Bo (fn2 :: FinList n)) = Bo (fmerge fn1 fn2)
  ialt (Bo s1) (Un s2)  = Un (alt (toList s1) s2)
  ialt (Un s1) (Bo fn2) = Un (alt s1 (toList fn2))
  ialt (Un s1) (Un s2)  = Un (alt s1 s2)

  istar = undefined

altGroup :: Group o1 -> Group o2 -> [Group (Alt o1 o2)]
altGroup (Bo (fn1 :: FinList m))(Bo (fn2 :: FinList n)) =
  [ Bo (axiomWeakenMaxRight @n fn1), Bo (axiomWeakenMaxLeft @m fn2) ]
altGroup (Bo s1) (Un s2)  = [ Un (toList s1), Un s2]
altGroup (Un s1) (Bo fn2) = [ Un s1, Un (toList fn2)]
altGroup (Un s1) (Un s2)  = [ Un s1, Un s2 ]
  
defaultGroup :: SOcc o -> Group o
defaultGroup (SFin i) = Bo FNil
defaultGroup SInf     = Un []

weakenGroupLeft :: SOcc (o1 :: Occ) -> Group (o2 :: Occ) -> Group (Alt o1 o2)
weakenGroupLeft (SFin (i :: SNat i)) (Bo m) = Bo (axiomWeakenMaxLeft @i m)
weakenGroupLeft (SFin i)  (Un l) = Un l
weakenGroupLeft SInf      (Bo m) = Un (toList m)
weakenGroupLeft SInf      (Un l) = Un l

weakenGroupRight :: Group (o1 :: Occ) -> SOcc (o2 :: Occ) -> Group (Alt o1 o2)
weakenGroupRight (Bo m) (SFin (i :: SNat i)) = Bo (axiomWeakenMaxRight @i m)
weakenGroupRight (Un l) (SFin i) = Un l
weakenGroupRight (Bo m)    SInf   = Un (toList m)
weakenGroupRight (Un l)    SInf   = Un l

instance Show (Group o) where
  show (Bo fn) = show fn
  show (Un ls) = show ls

-------------------------------------------------------------------------

type Dict s = SS Group s

data Dict (ss :: S) where
  Nil  :: Dict (Empty S)
  Cons :: KnownSymbol s => proxy s -> Group o -> Dict ss -> Dict  ('(s,o)': ss)

instance IKleene Dict where
  iempty = Nil

  isequ Nil Nil = Nil
  isequ (Cons ps g1 d1) Nil = (Cons ps g1 d1)
  isequ Nil (Cons ps g1 d1) = (Cons ps g1 d1)
  isequ (Cons (ps :: p1 s) g1 m1) (Cons (pt :: p2 t) g2 m2) = case (sym @s %~ sym @t) of
    Proved Refl -> Cons ps (isequ g1 g2) (isequ m1 m2)
    Disproved _ -> case (sCompare (sym @s) (sym @t)) of
      SLT -> Cons ps g1 (isequ m1 (Cons pt g2 m2))
      SGT -> Cons pt g2 (isequ (Cons ps g1 m1) m2)

  ialt Nil Nil = Nil
  ialt (Cons ps g1 d1) Nil = Cons ps g1 d1
  ialt Nil (Cons ps g1 d1) = Cons ps g1 d1
  ialt (Cons (ps :: p1 s) g1 m1) (Cons (pt :: p2 t) g2 m2) = case (sym @s %~ sym @t) of
    Proved Refl -> Cons ps (ialt g1 g2) (ialt m1 m2)
    Disproved _ -> case (sCompare (sym @s) (sym @t)) of
      SLT -> (Cons ps g1) (ialt m1 (Cons pt g2 m2))
      SGT -> (Cons pt g2) (ialt (Cons ps g1 m1) m2)

  istar = undefined

altDict :: Dict s1 -> Dict s2 -> [Dict (Alt s1 s2)]
altDict Nil Nil = [Nil]
altDict (Cons ps g1 d1) Nil = [Cons ps g1 d1]
altDict Nil (Cons ps g1 d1) = [Cons ps g1 d1]
altDict (Cons (ps :: p1 s) g1 m1) (Cons (pt :: p2 t) g2 m2) = case (sym @s %~ sym @t) of
  Proved Refl -> [Cons ps g d|  d <- altDict m1 m2,  g <- altGroup g1 g2]
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> fmap (Cons ps g1) (altDict m1 (Cons pt g2 m2))
    SGT -> fmap (Cons pt g2) (altDict (Cons ps g1 m1) m2)


defaultDict :: SS SOcc s -> Dict s
defaultDict SSNil = Nil
defaultDict (SSCons (ps :: proxy s) o1 ss) =
   Cons ps (defaultGroup o1) (defaultDict ss)


weakenDictLeft :: forall s1 s2. SS SOcc s1 -> Dict s2 -> Dict (Alt s1 s2)
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

weakenDictRight :: forall s2 s1. SS SOcc s2 -> Dict s1 -> Dict (Alt s1 s2)
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

{-

-- not the same for some reason

weakenDictLeft :: forall s1 s2. SS s1 -> Dict s2 -> Dict (Alt s1 s2)
weakenDictLeft ss dd = head (alt (defaultDict ss) dd)

weakenDictRight :: forall s2 s1. SS s2 -> Dict s1 -> Dict (Alt s1 s2)
weakenDictRight ss dd = head (alt dd (defaultDict ss))
-}


instance Show (Dict '[]) where
  show Nil = ""
instance Show (Dict ss) => Show (Dict ('(s,o):ss)) where
  show (Cons (ps :: p s1) g ss) = "{" ++ show (symbolVal ps) ++ "=" ++ show g ++ "}" ++  show ss


-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- Singleton symbol
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s

data R (ss :: S) where
  Rempty :: R (Empty S)
  Rvoid  :: R (Empty  S)
  Rseq   :: (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Sequ s1 s2)
  Ralt   :: (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Alt s1 s2)
  Rstar  :: (Axiom s) => R s  -> R (Star s)
  Rchar  :: Char -> R (Empty S)
  Rmark  :: KnownSymbol s => proxy s -> String -> R (Empty S) -> R ( '[ '(s, Fin 1) ])

toSingR :: R ss -> SS SOcc ss
toSingR Rempty = iempty
toSingR Rvoid  = SSNil
toSingR (Rseq r1 r2) = isequ (toSingR r1) (toSingR r2)
toSingR (Ralt r1 r2) = ialt  (toSingR r1) (toSingR r2)
toSingR (Rstar r)    = istar (toSingR r)
toSingR (Rchar c)    = iempty
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

-- axiom :: forall k (m :: k). Alt m m :~: m
-- axiom = unsafeCoerce Refl

axiomDistrib :: forall k s. Star (s :: k) :~: (Alt (Empty k) (Sequ s (Star s)))
axiomDistrib = unsafeCoerce Refl


match :: Axiom m => R m -> String -> Maybe (Dict m)
match r w = extract (deriveWord r w)

deriveWord :: Axiom n => R n -> String -> R n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 

{-
extract :: R m -> Maybe [Dict m]
extract Rempty       = return [Nil]
extract Rvoid        = Nothing
extract (Rchar c)    = return [Nil]
extract (Rseq r1 r2) = do
  s1 <- extract r1
  s2 <- extract r2
  return $ [ isequ v1 v2 | v1 <- s1, v2 <- s2 ]
extract (Ralt (r1 :: R m1) (r2 :: R m2)) = case (extract r1, extract r2) of
  (Just s1, Just s2) -> Just (concat [ altDict v1 v2 | v1 <- s1, v2 <- s2 ])
  (Just s1, Nothing) -> Just (map (weakenDictRight (toSingR r2)) s1)
  (Nothing, Just s2) -> Just (map (weakenDictLeft (toSingR r1)) s2)
  (Nothing, Nothing) -> Nothing
  
extract (Rstar r)      = return [ defaultDict (toSingR (Rstar r)) ]
extract (Rmark _ s r)  = if nullable r then 
  return [Cons Proxy (Bo (FCons (Set.singleton s) FNil)) Nil] else Nothing
-}

extract :: R m -> Maybe (Dict m)
extract Rempty       = return iempty
extract Rvoid        = Nothing
extract (Rchar c)    = return iempty
extract (Rseq r1 r2) = do
  s1 <- extract r1
  s2 <- extract r2
  return $ isequ s1 s2
extract (Ralt (r1 :: R m1) (r2 :: R m2)) = case (extract r1, extract r2) of
  (Just s1, Just s2) -> return $ ialt s1 s2
  (Just s1, Nothing) -> return $ weakenDictRight (toSingR r2) s1
  (Nothing, Just s2) -> return $ weakenDictLeft (toSingR r1) s2
  (Nothing, Nothing) -> Nothing
  
extract (Rstar r)      = return $ defaultDict (toSingR (Rstar r)) 
extract (Rmark _ s r)  = if nullable r then 
  return (Cons Proxy (Bo (FCons (Set.singleton s) FNil)) Nil) else Nothing



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

deriv :: forall n. Axiom n => R n -> Char -> R n
deriv (Rchar s)    c   = if s == c then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1, Refl <- axiomAltIdem @S @n = 
     Ralt (Rseq (deriv r1 c) r2) (Rseq (markEmpty r1) (deriv r2 c))
deriv (Rstar (r :: R s)) c | Refl <- axiomStar @S @s =
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
