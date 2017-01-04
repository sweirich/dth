{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, FunctionalDependencies #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses, ConstraintKinds #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module RegexpOcc where

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..),TestEquality(..))

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude hiding ((:$$$))
import Data.Singletons.TypeLits (Symbol(..),KnownSymbol(..),Sing(..))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

import Data.List(foldl')


-- This type system infers the marked subexpressions of a given
-- regular expression, and uses that information to make sure that
-- submatching are used correctly.

-- It tracks the number of times a pattern occurs in a regular expression,
-- and uses that to determine whether the range type for the label should be
-- "String", "Maybe String", or "[String]"


-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using (Partial) Derivatives
-- Note: This version doesn't use partial (Antimorov) derivatives. For
-- simplicity it uses the Brzowozki derivatives instead, which are backtracking.



-------------------------------------------------------------------------
-- Type system keeps track of a list of all possible
-- labels that *could* appear in the output

instance Ord Symbol where (<=) = error "no term"
instance Eq  Symbol where (==) = error "no term"
-- Type-level set operation


$(singletons [d|
    
  -- automatically defines "max"
  data Occ = Str | Opt | Many deriving (Eq, Ord, Show)

  empty :: [(Symbol,Occ)]
  empty = []

  one :: Symbol -> [(Symbol,Occ)]
  one s = [(s, Str)]

  merge :: [(Symbol,Occ)] -> [(Symbol,Occ)] -> [(Symbol,Occ)]
  merge [] [] = []
  merge m  [] = m
  merge [] m  = m
  merge (e1@(s1,o1):t1) (e2@(s2,o2):t2) =
    if s1 == s2 then (s1, Many) : merge t1 t2
    else if s1 <= s2 then e1 : merge t1 (e2:t2)
      else e2 : merge (e1:t1) t2

  makeOpt :: Occ -> Occ
  makeOpt Str  = Opt
  makeOpt Opt  = Opt
  makeOpt Many = Many

  alt :: [(Symbol,Occ)] -> [(Symbol,Occ)] -> [(Symbol,Occ)]
  alt [] [] = []
  alt ((s1,o1):t1) [] = (s1,makeOpt o1) : alt t1 []
  alt [] ((s2,o2):t2) = (s2,makeOpt o2) : alt [] t2
  alt ((s1,o1):t1)((s2,o2):t2) =
      if s1 == s2 then (s1, max o1 o2) : alt t1 t2
      else if s1 <= s2 then (s1,makeOpt o1) : alt t1 ((s2,o2):t2)
           else (s2,makeOpt o2) : alt ((s1,o1):t1) t2

  repeat :: [(Symbol,Occ)] -> [(Symbol,Occ)]
  repeat [] = []
  repeat ((s,o):t) = ((s,Many):repeat t)

  |])

type U = [(Symbol,Occ)]

rtest = rmark @"name" rname 
        `rseq` (ralt rempty (rstar rsep `rseq` rmark @"address" raddress))
        `rseq` (rstar rsep `rseq` (rstar (rmark @"email" rphone)))



-- Singleton symbol
sym :: forall s. SingI s => Sing (s :: Symbol)
sym = sing @Symbol @s

sset :: forall s. SingI s => Sing (s :: U)
sset = sing @U @s

showSymbol :: forall (s :: Symbol) p. SingI s => p s -> String
showSymbol ps = case sing :: Sing s of SSym -> symbolVal ps



-- The Singletons library above generates the following definitions:
{-
type family Merge (a :: U) (b :: U) :: U where
    Merge '[] '[] = '[]
    Merge m '[] = m
    Merge '[] m = m
    Merge ('(s1,o1):t1)('(s2,o2):t2) =
      If (s1 :== s2)
         ('(s1, Many) : Merge t1 t2)
         (If (s1 :<= s2) ('(s1,o1) : (Merge t1 ('(s2,o2):t2)))
                         ('(s2,o2) : (Merge ('(s1,o1):t1) t2)))

type family MakeOpt (o :: Occ) :: U where
   MakeOpt Str  = Opt
   MakeOpt Opt  = Opt
   MakeOpt Many = Many

type family Alt (a :: U) (b :: U) :: U where
    Alt '[] '[] = '[]
    Alt m '[] = m
    Alt '[] m = m
    Alt ('(s1,o1):t1)('(s2,o2):t2) =
      If (s1 :== s2)
         ('(s1, AltOcc o1 o2) : Alt t1 t2)
         (If (s1 :<= s2) ('(s1,MakeOpt o1) : (Alt t1 ('(s2,o2):t2)))
                         ('(s2,MakeOpt o2) : (Alt ('(s1,o1):t1) t2)))      

-}
class (o ~ Max o o, SingI o) => WfOcc (o :: Occ) where
instance WfOcc Str
instance WfOcc Opt
instance WfOcc Many

-- Well-founded sets are exactly those constructed only
-- from a finite number of [] and :
-- Well-founded sets have the following properies:
class (m ~ Alt m m,
       Repeat m ~ Repeat (Repeat m),
       Merge m (Repeat m) ~ Repeat m,
       Alt '[] (Repeat m) ~ Repeat m,
       Repeat m ~ Merge (Repeat m) (Repeat m),
       -- they also have runtime representations
       SingI m) =>
       WfSet (m :: U) where
       singSet :: SingSet m

data SingSet (s :: U) where
  WNil  :: SingSet '[]
  WCons :: (SingI a, SingI o, WfOcc o, WfSet t) => proxy1 a -> proxy2 o ->
     SingSet t -> SingSet ('(a,o) : t)
       
  
-- note the superclass constraint is proved automatically
-- by Haskell's type class resolution 
instance WfSet '[] where
   singSet = WNil
instance (SingI a, WfOcc o, WfSet s) => WfSet ('(a,o) : s) where
   singSet = WCons sing sing singSet


data WfSetD s where
  SomeSet :: WfSet s => SingSet s -> WfSetD s

rmerge :: (WfSet s1, WfSet s2) => SingSet (s1 :: U) -> SingSet (s2 :: U) -> WfSetD (Merge s1 s2)
rmerge WNil WNil = SomeSet WNil
rmerge m WNil = SomeSet m
rmerge WNil m = SomeSet m
rmerge s1@(WCons (pr1 :: p1a s1) (pr1a :: p1b o1) st1)
       s2@(WCons (pr2 :: p2a s2) (pr2a :: p2b o2) st2) = 
  case (sym @s1 %:== sym @s2) of
    STrue  ->  (case (rmerge st1 st2) of
       SomeSet st -> SomeSet $ WCons (Proxy @s1) (Proxy @Many) st)
    SFalse -> case (sym @s1) `sCompare` (sym @s2) of
      SLT -> (case (rmerge st1 s2) of
               SomeSet st -> SomeSet $ WCons (Proxy @s1) (Proxy @o1) st)
      SGT -> (case (rmerge s1 st2) of
               SomeSet st -> SomeSet $ WCons (Proxy @s2) (Proxy @o2) st)

data WfOccD s where
  SomeOcc :: WfOcc s => Sing s -> WfOccD s

wfMakeOpt :: WfOcc o => Sing o -> WfOccD (MakeOpt o)
wfMakeOpt SStr  = SomeOcc SOpt
wfMakeOpt SOpt  = SomeOcc SOpt
wfMakeOpt SMany = SomeOcc SMany

wfMax :: (WfOcc o1, WfOcc o2) => Sing o1 -> Sing o2 -> WfOccD (Max o1 o2)
wfMax SMany SMany = SomeOcc SMany
wfMax SMany SOpt  = SomeOcc SMany
wfMax SMany SStr  = SomeOcc SMany
wfMax SOpt  SMany = SomeOcc SMany
wfMax SStr  SMany = SomeOcc SMany
wfMax SOpt  SOpt  = SomeOcc SOpt
wfMax SOpt  SStr  = SomeOcc SOpt
wfMax SStr  SOpt  = SomeOcc SOpt
wfMax SStr  SStr  = SomeOcc SStr

wfAlt :: (WfSet s1, WfSet s2) => SingSet (s1 :: U) -> SingSet (s2 :: U) -> WfSetD (Alt s1 s2)
wfAlt WNil WNil = SomeSet WNil
wfAlt s1@(WCons (pr1 :: p1a s1) (pr1a :: p1b o1) st1) WNil =
  case (wfAlt st1 WNil, wfMakeOpt (sing @Occ @o1)) of
    (SomeSet st, SomeOcc o) -> SomeSet $ WCons pr1 o st
wfAlt WNil s2@(WCons (pr2 :: p2a s2) (pr2a :: p2b o2) st2) =
  case (wfAlt WNil st2, wfMakeOpt (sing @Occ @o2)) of
    (SomeSet st, SomeOcc o) -> SomeSet $ WCons pr2 o st
wfAlt s1@(WCons (pr1 :: p1a s1) (pr1a :: p1b o1) st1)
      s2@(WCons (pr2 :: p2a s2) (pr2a :: p2b o2) st2) = 
  case (sym @s1 %:== sym @s2) of
    STrue  ->  (case (wfAlt st1 st2, wfMax (sing @Occ @o1) (sing @Occ @o2)) of
       (SomeSet st, SomeOcc o) -> SomeSet $ WCons (Proxy @s1) o st)
    SFalse -> case (sym @s1) `sCompare` (sym @s2) of
      SLT -> case (wfAlt st1 s2, wfMakeOpt (sing @Occ @o1)) of
               (SomeSet st, SomeOcc o) -> SomeSet $ WCons (Proxy @s1) o st
      SGT -> case (wfAlt s1 st2, wfMakeOpt (sing @Occ @o2)) of
               (SomeSet st, SomeOcc o) -> SomeSet $ WCons (Proxy @s2) o st


                                               
-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: U where
  T = '("a", Str) : T

testWf :: WfSet a => ()
testWf = ()

-- x1 = testWf @'[ '("a", Str), '("b", Str), '("c", Many) ]
-- x2 = testWf @T   -- doesn't type check

-------------------------------------------------------------------------

-- A data structure indexed by a type-level set
-- Keeps the entries in sorted order by key

type Result (s :: U) = Maybe (List Entry s)

type family TOcc (o :: Occ) :: Type where
  TOcc Str  = String
  TOcc Opt  = Maybe String
  TOcc Many = [String]

data Entry (sym ::(Symbol,Occ)) where
   Entry :: (SingI s, WfOcc o) => proxy (s :: Symbol) -> Sing o -> TOcc o -> Entry '(s,o)                                                                          
data List (sa :: (Symbol,Occ) -> Type) (s :: U) where
   Nil  :: List sa '[]
   Cons :: sa a -> List sa tl -> List sa (a : tl)

------
-- show instance
data EEntry = EEntry String String
instance Show EEntry where
  show (EEntry s ss) = s ++ ":" ++ ss

showOcc :: Sing o -> TOcc o -> String
showOcc SStr  s = s
showOcc SOpt  s = show s
showOcc SMany s = show s


toList :: List Entry s -> [ EEntry ]
toList Nil = []
toList (Cons (Entry (ps :: p a) so ss) xs) =
  (EEntry (showSymbol ps) (showOcc so ss)) : toList xs where x = sym @a
             
instance Show (List Entry s) where
  show x = show (toList x)
------


toMany :: Sing o -> TOcc o -> [String]
toMany SStr s = [s]
toMany SOpt (Just s) = [s]
toMany SOpt Nothing  = []
toMany SMany ss = ss

-- if s1 == s2 then this is "mappend" for the List Entry monoid
-- (but, not the usual list monoid, the one where we glue each element
-- together pointwise)
-- this is *almost* sMerge, but it works with entries, not singleton symbols
combine :: List Entry s1 -> List Entry s2 -> List Entry (Merge s1 s2)
combine Nil Nil = Nil
combine Nil b = b
combine b Nil = b
combine (Cons e1@(Entry (ps :: p s) so1 ss) t1)
        (Cons e2@(Entry (pt :: p2 t) so2 ts) t2) =
  case ((sym @s) %:== (sym @t)) of
   STrue ->  Cons (Entry ps SMany (toMany so1 ss ++ toMany so2 ts))
                           (combine t1 t2)     
   SFalse -> case sCompare (sym @s) (sym @t) of
     SLT  -> Cons e1 (combine t1 (Cons e2 t2))
     SGT ->  Cons e2 (combine (Cons e1 t1) t2) 

-- combine the two sets together
join :: Result s1 -> Result s2 -> Result (Merge s1 s2)
join xss yss = do
  xs <- xss
  ys <- yss
  return $ combine xs ys


defocc :: Sing o -> TOcc (MakeOpt o)
defocc SStr  = Nothing    
defocc SOpt  = Nothing
defocc SMany = []

weaken :: Sing o -> TOcc o -> TOcc (MakeOpt o)
weaken SStr  s = Just s
weaken SOpt  s = s
weaken SMany s = s

-- This was a nice one to define.  I made it an id function for every
-- case, then used the four type errors to adjust

glueOccLeft :: Sing o1 -> Sing o2 -> TOcc o2 -> TOcc (Max o1 o2)
glueOccLeft SStr SStr  m = m
glueOccLeft SStr SOpt  m = m
glueOccLeft SStr SMany m = m
glueOccLeft SOpt SStr  m = Just m
glueOccLeft SOpt SOpt  m = m
glueOccLeft SOpt SMany m = m
glueOccLeft SMany SStr  m = [m]
glueOccLeft SMany SOpt (Just m) = [m]
glueOccLeft SMany SOpt Nothing = []
glueOccLeft SMany SMany m = m

glueOccRight :: Sing o1 -> TOcc o1 -> Sing o2 -> TOcc (Max o1 o2)
glueOccRight SStr m SStr   = m
glueOccRight SStr m SOpt   = Just m
glueOccRight SStr m SMany  = [m]
glueOccRight SOpt m SStr   = m
glueOccRight SOpt m SOpt   = m
glueOccRight SOpt (Just m) SMany  = [m]
glueOccRight SOpt Nothing SMany  = []
glueOccRight SMany m SStr  = m
glueOccRight SMany m SOpt  = m
glueOccRight SMany m SMany = m

glueLeft :: Sing s1 -> List Entry s2 -> List Entry (Alt s1 s2)
glueLeft SNil Nil = Nil
glueLeft SNil (Cons  e2@(Entry (pt :: p2 t) so2 ts) t2) =
  case wfMakeOpt so2 of
    SomeOcc so ->
      Cons (Entry pt so tocc) (glueLeft SNil t2) where
--                 so   = sMakeOpt so2
                 tocc = weaken so2 ts
glueLeft (SCons (STuple2 ps so) t) Nil =
    Cons (withSingI ps (Entry ps (sMakeOpt so) (defocc so))) (glueLeft t Nil)
 
glueLeft (SCons e1@(STuple2 (ps :: Sing s) so1)  t1) 
         (Cons  e2@(Entry (pt :: p2 t) so2 ts) t2) =
  case (ps %:== (sym @t)) of
   STrue -> case wfMax so1 so2 of
     SomeOcc so ->
        Cons (withSingI ps (Entry ps so tocc)) (glueLeft t1 t2) where
        --         so   = sMax so1 so2
                 tocc = glueOccLeft so1 so2 ts
   SFalse -> case sCompare ps (sym @t) of
     SLT  -> case wfMakeOpt so1 of
       SomeOcc so ->
          Cons u1 (glueLeft t1 (Cons e2 t2)) where
                u1 = (withSingI ps (Entry ps so tocc))
   --             so   = sMakeOpt so1
                tocc = defocc so1 
     SGT -> case wfMakeOpt so2 of
       SomeOcc so ->
         Cons (Entry pt so tocc) (glueLeft (SCons e1 t1) t2) where
         --        so   = sMakeOpt so2
                 tocc = weaken so2 ts

glueRight :: List Entry s1 -> Sing s2 -> List Entry (Alt s1 s2)
glueRight Nil SNil = Nil
glueRight (Cons  e2@(Entry (pt :: p2 t) so2 ts) t2) SNil =
  case wfMakeOpt so2 of 
    SomeOcc o -> Cons (Entry pt so tocc) (glueRight t2 SNil) where
---                 so   = sMakeOpt so2
                 tocc = weaken so2 ts
glueRight Nil (SCons (STuple2 ps so) t) =
  case wfMakeOpt so of
    SomeOcc so' ->
      Cons (withSingI ps (Entry ps so' (defocc so))) (glueRight Nil t)

glueRight (Cons   e1@(Entry (ps :: p1 s) so1 ss)  t1) 
          (SCons  e2@(STuple2 (pt :: Sing t) so2) t2) =
  case ((sym @s) %:== pt) of
   STrue -> case wfMax so1 so2 of
     SomeOcc so -> Cons (Entry ps so tocc) (glueRight t1 t2) where
                 -- so   = sMax so1 so2
                 tocc = glueOccRight so1 ss so2 
   SFalse ->  case sCompare (sym @s) pt of
     SLT  -> case wfMakeOpt so1 of
       SomeOcc so -> Cons u1 (glueRight t1 (SCons e2 t2)) where
                u1 = (Entry ps so tocc)
                --so   = sMakeOpt so1
                tocc = weaken so1 ss
     SGT -> case wfMakeOpt so2 of
       SomeOcc so ->
         Cons (withSingI pt (Entry pt so tocc)) (glueRight (Cons e1 t1) t2) where
         --        so   = sMakeOpt so2
                 tocc = defocc so2 
          



-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
firstSuccess :: forall s1 s2. (SingI s1, SingI s2) =>
                      Result s1 -> Result s2 -> Result (Alt s1 s2)
firstSuccess Nothing Nothing  = Nothing                   
firstSuccess Nothing (Just y) = Just (glueLeft (sing @U @s1) y)
firstSuccess (Just x) _       = Just (glueRight x (sing @U @s2))


repeatOcc :: Sing o -> TOcc o -> TOcc Many
repeatOcc SStr s = [s]
repeatOcc SOpt (Just s) = [s]
repeatOcc SOpt Nothing = []
repeatOcc SMany s = s

repeatList :: List Entry s -> List Entry (Repeat s)
repeatList  Nil = Nil
repeatList (Cons (Entry (ps :: p s) o v) t) =
  Cons (Entry ps SMany (repeatOcc o v)) (repeatList t)

repeatResult :: (SingI s) => Result s -> Result (Repeat s)
repeatResult Nothing = Nothing
repeatResult (Just x) = Just (repeatList x)
  
-------------------------------------------------------------------------

-- eventually in data.record
class HasField (x :: k) r a | x r -> a where
  getField    :: r -> a

data Index (s :: Symbol)  (o :: Occ) (m :: U) where
  DH :: Index s o ('(s,o):m)
  DT :: Index s o m -> Index s o (t:m)

type family ShowU (m :: U) :: ErrorMessage where
  ShowU '[] = Text ""
  ShowU '[ '(a,o)] = Text a
  ShowU ('(a,o): m) = Text a :<>: Text ", " :<>: ShowU m

type family Find (s :: Symbol) (m :: U) :: Index s o m where
  Find s m = FindH s m m

-- Using a closed type family to implement the partial function
type family FindH (s :: Symbol) (m :: U) (m2 :: U) :: Index s o m where
  FindH s ('(s,o): m) m2 = DH
  FindH s ('(t,p): m) m2 = DT (FindH s m m2)
  FindH s '[] m2  = TypeError (Text s :<>: Text " not found in " :$$:
                                 Text "    " :<>: ShowU m2)

-- How to look up in the list, given an index
class Get (p :: Index s o m) | s m -> o where
  getp :: List Entry m -> TOcc o

instance Get DH where
  getp (Cons (Entry _ _ v) _ ) = v

instance (Get l) => Get (DT l) where
  getp (Cons _ xs) = getp @_ @_ @_ @l xs

-- Instance for the result
instance (HasField s (List Entry m) t) => 
     HasField s (Result m) (Maybe t) where
  getField (Just x) = Just  (getField @s x)
  getField Nothing = Nothing

-- Instance for a list of entries
instance (Get (Find s m :: Index s o m), t ~ TOcc o) =>
                      HasField s (List Entry m) t where
  getField x = getp @_ @_ @_ @(Find s m) x




-------------------------------------------------------------------------
-- smart constructors
-- we might as well optimize the regular expression whenever we
-- build it.  

-- smart constructor -- optimizes on construction
-- reduces: r + r to just r
ralt :: forall s1 s2. (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Alt s1 s2)
--ralt Rvoid r = r   --doesn't type check
--ralt r Rvoid = r   --doesn't type check
ralt (Rchar s1) (Rchar s2) = Rchar (Set.union s1 s2)
ralt r1 r2 | Just Refl <- r1 `testEquality` r2 = r1
ralt r1 r2 = Ralt r1 r2

-- reduces (r,epsilon) (epsilon,r) to just r
-- and r*r* to r*
-- our abstraction won't let us optimize (r,void) -> void though
-- it doesn't know that the matches in r cannot occur.
rseq :: forall s1 s2. (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq (Rchar s) r2 | Set.null s = r2
rseq r1 (Rchar s) | Set.null s = r1
--rseq (Rstar r1) (Rstar r2) | Just Refl <- r1 `testEquality` r2 = (Rstar r1)
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2

isVoid :: R s1 -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rstar r)      = isVoid r
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- convenience function for marks
-- MUST use explicit type application for 'sym' to avoid ambiguity
rmark :: forall sym s. (KnownSymbol sym, WfSet s) =>
     R s -> R (Merge (One sym) s)
rmark r = Rmark (sym @sym) "" r

-- convenience function for single characters
rchar :: Char -> R Empty
rchar c = Rchar (Set.singleton c)


rchars :: Set Char -> R Empty
rchars s = Rchar s

-- r** = r*
-- empty* = empty
rstar :: (WfSet s) => R s -> R (Repeat s)
rstar (Rstar s) = Rstar s
rstar r@(Rchar s) | Set.null s = r
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R Empty
rvoid = Rvoid

rempty :: R Empty
rempty = Rchar Set.empty

-- Our GADT, indexed by the set of pattern variables
-- Note that we require all sets to be Wf. (Empty is known to be.)
data R (ss :: U) where
-- Rempty :: R Empty  -- the empty word is represent by Rchar Set.empty
  Rvoid  :: R s  -- try adding a singleton here to pin down s
                 -- can be anything b/c will always fail
  Rseq   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Alt   s1 s2)
  Rstar  :: (WfSet s) => R s  -> R (Repeat s)
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rchar  :: Set Char -> R Empty
  Rmark  :: (KnownSymbol sym, WfSet s) =>
     proxy sym -> String -> R s -> R (Merge (One sym) s)

-- This does not really compare for equality --- the voids get in the way
instance TestEquality R where
  Rseq t1 t2 `testEquality` Rseq u1 u2 |
    Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2    = Just Refl
  Ralt t1 t2 `testEquality` Ralt u1 u2 |
    Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2    = Just Refl
  Rstar t1   `testEquality` Rstar u1   |
    Just Refl <- testEquality t1 u1    = Just Refl
  Rchar s1   `testEquality` Rchar s2   | s1 == s2 = Just Refl
  Rmark (_ :: p1 s) s1 r1 `testEquality` Rmark (_ :: p2 t) s2 r2 |
    s1 == s2,
    Just Refl <- testEquality (sym @s) (sym @t),
    Just Refl <- r1 `testEquality` r2  = Just Refl
  Rvoid      `testEquality` Rvoid      = Nothing    -- have to ignore voids                                     
  _          `testEquality` _          = Nothing


-- displaying regular expressions  
instance Show (R n) where
  show Rvoid  = "∅"   
  show (Rseq r1 r2) = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = if c == (Set.fromList ['0' .. '9']) then "\\d"
                   else if c == (Set.fromList [' ', '-', '.']) then "\\w"
                   else show c
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"
  show (Rany) = "."
  show (Rnot cs) = "^" ++ show cs
------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: WfSet s => R s -> String -> Result s
match r w = extract (foldl deriv r w)

-- extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: WfSet s => R s -> Result s
extract Rvoid        = Nothing 
extract (Rchar cs)   = if Set.null cs then Just Nil else Nothing
extract (Rseq r1 r2) = join (extract r1) (extract r2)
extract (Ralt r1 r2) = firstSuccess (extract r1) (extract r2)
extract (Rstar r)    = firstSuccess (Just Nil)   (repeatResult (extract r))
extract (Rmark (ps :: p s) s r) =
  if nullable r
    then join (mark ps s)   (extract r)
    else join @'[ '(s,Str) ] Nothing (extract r)
  where
    mark ps t = Just (Cons (Entry ps SStr t) Nil)
extract (Rnot cs)    = if Set.null cs then Nothing else Just Nil
extract Rany         = Nothing


-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rvoid          = False
nullable (Rchar cs)     = Set.null cs
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable Rany           = False
nullable (Rnot cs)      = not (Set.null cs)

-- regular expression derivative function
deriv :: forall n. WfSet n => R n -> Char -> R n
deriv (Rchar s)    c   = if Set.member c s then (Rchar Set.empty) else Rvoid
deriv (Rseq r1 r2) c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) (rseq (markEmpty r1) (deriv r2 c))
deriv (Rseq r1 r2) c   = rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar (r :: R s)) c = (rseq (deriv r c) (rstar r))
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)
deriv (Rnot s)     c   = if Set.member c s then Rvoid else (Rchar Set.empty)
deriv Rany         c   = Rchar Set.empty

-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: R n -> R n
markEmpty (Rmark p w r) | nullable r = (Rmark p w (markEmpty r))
markEmpty (Rmark p w r) = Rmark p w (markVoid r)
markEmpty (Ralt r1 r2)  = Ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = Rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = Rstar (markEmpty r)
markEmpty (Rchar c)     = Rchar Set.empty
markEmpty Rvoid         = Rvoid
markEmpty (Rnot  c)     = Rchar Set.empty
markEmpty (Rany)        = Rchar Set.empty

-- create a regexp that doesn't match any strings, but still
-- contains the data at marks
markVoid :: R n -> R n
markVoid (Rmark p w r) = Rmark p w (markVoid r)
markVoid (Ralt r1 r2)  = Ralt  (markVoid r1) (markVoid r2)
markVoid (Rseq r1 r2)  = Rseq  (markVoid r1) (markVoid r2)
markVoid (Rstar r)     = Rstar (markVoid r)
markVoid _             = Rvoid


----------------------------------------------------------

r1 = ralt (rchar 'a') (rchar 'b')

r2 = rmark @"a" r1

r4 = rstar (rmark @"b" (rseq r1 r1))

r5 = ralt (rmark @"b" (rchar 'a')) (rmark @"b" (rchar 'b'))

r6 = ralt (rmark @"a" (rchar 'a')) (rmark @"b" (rchar 'b'))

r7 = ralt (rmark @"b" (rchar 'b')) (rmark @"b" (rchar 'b'))

r8 = rmark @"x" (rstar (rchar 'a'))

r9 = rmark @"c" (rseq (rstar (rchar 'c')) r6)


-------------------------------------------------------------------------

digit = Rchar (Set.fromList ['0' .. '9'])
dash  = Rchar (Set.fromList ['-','.',' '])
rsep  = dash


opt_dash = ralt dash rempty

rphone = 
   (digit `rseq` digit `rseq` digit `rseq` opt_dash
    `rseq` digit `rseq`  digit `rseq` digit `rseq` digit)

alpha  = Rchar (Set.fromList ['a' .. 'z' ])
alphaC = Rchar (Set.fromList ['A' .. 'Z' ])

rname   = rseq alphaC (rstar alpha)

raddress = rstar digit `rseq` rstar rname

entry  = (rmark @"name" rname) `rseq` rstar opt_dash `rseq` (ralt rempty
                                                             (rmark @"phone" rphone))

pbook  = rstar (rchar '(' `rseq` (rmark @"entry" entry) `rseq` rchar ')')

pbookstring = "(Steve 123-2222)(Stephanie   1202323)(Ellie)(Sarah 324-3444)"

fullname = rname `rseq` rstar (rchar ' ') `rseq` rname

-------------------------------------------------------------------------

result = match pbook pbookstring


nm  = getField @"entry" result
num = getField @"phone" result

-- Doesn't type check
--bad = getField @"email" result



result2 = match entry "Stephanie"
nm2 = getField @"name" result2
num2  = getField @"phone" result2

-------------------------------------------------------------------------

-- difficult pattern for backtracking implementations, like this one.
difficult = rstar (ralt (rchar 'a') (rchar 'a' `rseq` rchar 'a')) `rseq` (rchar 'b')

sloooow =  match difficult "aaaaaaaaaaaaaaaaaaaaaaaab"

greedy = rstar (rmark @"a" (rchar 'a')
                `ralt` (rmark @"ab" (rchar 'a' `rseq` rchar 'b'))
                `ralt` (rmark @"b" (rchar 'b')))

greedytest = match greedy "ab"
