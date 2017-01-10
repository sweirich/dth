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
import Data.Maybe(maybeToList)

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
  alt ((s1,o1):t1) [] = (s1,makeOpt o1): alt t1 []
  alt [] ((s2,o2):t2) = (s2,makeOpt o2): alt [] t2
  alt ((s1,o1):t1)((s2,o2):t2) =
      if s1 == s2 then (s1, max o1 o2) : alt t1 t2
      else if s1 <= s2 then (s1,makeOpt o1) : alt t1 ((s2,o2):t2)
           else (s2,makeOpt o2) : alt ((s1,o1):t1) t2

  repeat :: [(Symbol,Occ)] -> [(Symbol,Occ)]
  repeat [] = []
  repeat ((s,o):t) = ((s,Many):repeat t)

  |])

type U = [(Symbol,Occ)]

showSymbol :: Sing (s :: Symbol) -> String
showSymbol ps = case ps of SSym -> symbolVal ps


class (o ~ Max o o, SingI o, Show (TOcc o)) => WfOcc (o :: Occ) where
instance WfOcc Str
instance WfOcc Opt
instance WfOcc Many

-- Well-founded sets are exactly those constructed only
-- from a finite number of [] and :
-- Well-founded sets have the following properies:
class (m ~ Alt m m,
       Repeat m ~ Repeat (Repeat m),
       Merge m (Repeat m) ~ Repeat m,
--       Alt '[] (Repeat m) ~ Repeat m,
--       Repeat m ~ Merge (Repeat m) (Repeat m),
       -- they also have runtime representations
       SingI m) =>
       Wf (m :: U) where

-- note the superclass constraint is proved automatically
-- by Haskell's type class resolution 
instance Wf '[] where
instance (SingI a, WfOcc o, Wf s) => Wf ('(a,o) : s) where

-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: U where
  T = '("a", Str) : T

testWf :: Wf a => ()
testWf = ()

-- x1 = testWf @'[ '("a", Str), '("b", Str), '("c", Many) ]
-- x2 = testWf @T   -- doesn't type check

-------------------------------------------------------------------------

-- A data structure indexed by a type-level set
-- Keeps the entries in sorted order by key

type Result (s :: U) = Maybe (Dict s)

type family TOcc (o :: Occ) :: Type where
  TOcc Str  = String
  TOcc Opt  = Maybe String
  TOcc Many = [String]

data Entry (no :: (Symbol,Occ) ) where
   Entry :: Sing (s :: Symbol) -> Sing o -> TOcc o -> Entry '(s,o)                                                                          
data Dict (s :: U) where
   Nil  :: Dict '[]
   (:>) :: Entry a -> Dict tl -> Dict (a : tl)

infixr 5 :>

-------------------------------------------------------------------------
-- show instances

instance Show (Sing (n :: Symbol)) where
  show ps@SSym = symbolVal ps

instance Show (Entry s) where
  show (Entry sn so ss) = show sn ++ "=" ++ showData so ss where
    showData :: Sing o -> TOcc o -> String
    showData SStr  ss = ss
    showData SOpt  ss = show ss
    showData SMany ss = show ss

instance Show (Dict s) where
  show xs = "{" ++ show' xs where
    show' :: Dict xs -> String
    show' Nil = "}"
    show' (e :> Nil) = show e ++ "}"
    show' (e :> xs)  = show e ++ "," ++ show' xs

------

toMany :: Sing o -> TOcc o -> [String]
toMany SStr  s        = [s]
toMany SOpt  (Just s) = [s]
toMany SOpt  Nothing  = []
toMany SMany ss       = ss

combine :: Dict s1 -> Dict s2 -> Dict (Merge s1 s2)
combine Nil Nil = Nil
combine Nil b = b
combine b Nil = b
combine (e1@(Entry ps so1 ss) :> t1)
        (e2@(Entry pt so2 ts) :> t2) =
  case (ps %:== pt) of
   STrue -> Entry ps SMany (toMany so1 ss ++ toMany so2 ts) :> combine t1 t2     
   SFalse -> case ps %:<= pt of
     STrue  -> e1 :> combine t1 (e2 :> t2)
     SFalse -> e2 :> combine (e1 :> t1) t2 

-- combine the two sets together
both :: Result s1 -> Result s2 -> Result (Merge s1 s2)
both (Just xs) (Just ys) = Just $ combine xs ys
both _         _         = Nothing


-- A "default" Dict.
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
{-
nilsOpt :: forall s. (Wf s, SingI s) => Dict (OptU s)
nilsOpt = nils' (sing :: Sing s) where 
    nils' :: Sing ss -> Dict (OptU ss)
    nils' SNil                        = Nil
    nils' (SCons (STuple2 n SMany) r) = Entry n SMany [] :> nils' r
    nils' (SCons (STuple2 n SOpt ) r) = Entry n SOpt  Nothing :> nils' r
    nils' (SCons (STuple2 n SStr ) r) = Entry n SOpt  Nothing :> nils' r

maxEntry :: Entry '(n,o1) -> Entry '(n,o2) -> Entry '(n, Max o1 o2)
maxEntry = undefined
maxEntry (Entry ps SStr ss) (Entry _ SStr ts) = Entry ps SMany (ss ++ ts)
maxEntry (Entry ps SStr ss) (Entry _ SOpt ts) = Entry ps SMany
maxEntry (Entry ps SOpt ss) (Entry _ SStr ts) = Entry ps S
maxEntry (Entry ps SStr ss) (Entry _ SMany ts) = Entry ps SMany
maxEntry (Entry ps SMany ss) (Entry _ SStr ts) = Entry ps SMany

altDict :: forall s1 s2. Dict s1 -> Dict s2 -> Dict (Alt s1 s2)
altDict Nil Nil = Nil
altDict Nil b = nilsOpt @s2
altDict b Nil = nilOpt  @s1
altDict (e1@(Entry ps so1 ss) :> t1)
        (e2@(Entry pt so2 ts) :> t2) =
  case (ps %:== pt) of
   STrue -> maxEntry e1 e2 :> altDict t1 t2     
   SFalse -> case ps %:<= pt of
     STrue  -> e1 :> altDict t1 (e2 :> t2)
     SFalse -> e2 :> altDict (e1 :> t1) t2 
-}

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

glueLeft :: Sing s1 -> Dict s2 -> Dict (Alt s1 s2)
glueLeft SNil Nil = Nil
glueLeft SNil (e2@(Entry pt so2 ts) :> t2) =
      (Entry pt so tocc) :> (glueLeft SNil t2) where
                 so   = sMakeOpt so2
                 tocc = weaken so2 ts
glueLeft (SCons (STuple2 ps so) t) Nil =
      (Entry ps (sMakeOpt so) (defocc so)) :> (glueLeft t Nil)
 
glueLeft (SCons e1@(STuple2 (ps :: Sing s) so1)  t1) 
         (e2@(Entry pt so2 ts) :> t2) =
  case (ps %:== pt) of
   STrue -> 
         (Entry ps so tocc) :> (glueLeft t1 t2) where
                 so   = sMax so1 so2
                 tocc = glueOccLeft so1 so2 ts
   SFalse -> case sCompare ps pt of
     SLT  -> 
          u1 :> (glueLeft t1 (e2 :> t2)) where
                u1 = (Entry ps so tocc)
                so   = sMakeOpt so1
                tocc = defocc so1 
     SGT -> 
         (Entry pt so tocc) :> (glueLeft (SCons e1 t1) t2) where
                 so   = sMakeOpt so2
                 tocc = weaken so2 ts

glueRight :: Dict s1 -> Sing s2 -> Dict (Alt s1 s2)
glueRight Nil SNil = Nil
glueRight (e2@(Entry pt so2 ts) :> t2) SNil =
    (Entry pt so tocc) :> (glueRight t2 SNil) where
                 so   = sMakeOpt so2
                 tocc = weaken so2 ts
glueRight Nil (SCons (STuple2 ps so) t) =
     (Entry ps (sMakeOpt so) (defocc so)) :> (glueRight Nil t)

glueRight ( e1@(Entry ps so1 ss) :> t1) 
          (SCons e2@(STuple2 (pt :: Sing t) so2) t2) =
  case (ps %:== pt) of
   STrue -> (Entry ps so tocc) :> (glueRight t1 t2) where
                 so   = sMax so1 so2
                 tocc = glueOccRight so1 ss so2 
   SFalse ->  case sCompare ps pt of
     SLT  -> u1 :> (glueRight t1 (SCons e2 t2)) where
                u1 = (Entry ps so tocc)
                so   = sMakeOpt so1
                tocc = weaken so1 ss
     SGT -> 
          (Entry pt so tocc) :> (glueRight (e1 :> t1) t2) where
                 so   = sMakeOpt so2
                 tocc = defocc so2 
          
-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
first :: forall s1 s2. (SingI s1, SingI s2) =>
                      Result s1 -> Result s2 -> Result (Alt s1 s2)
first Nothing Nothing  = Nothing                   
first Nothing (Just y) = Just (glueLeft (sing @U @s1) y)
first (Just x) _       = Just (glueRight x (sing @U @s2))

-- A "default" Dict.
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
nils :: forall s. (Wf s, SingI s) => Dict (Repeat s)
nils = nils' (sing :: Sing s) where 
    nils' :: Sing ss -> Dict (Repeat ss)
    nils' SNil                        = Nil
    nils' (SCons (STuple2 n _) r) = Entry n SMany [] :> nils' r
  
-------------------------------------------------------------------------

-- eventually in data.record
class HasFieldD (x :: k) r a | x r -> a where
  getFieldD    :: r -> a

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
  getp :: Dict m -> TOcc o

instance Get DH where
  getp ((Entry _ _ v) :> _ ) = v

instance (Get l) => Get (DT l) where
  getp ( _ :> xs) = getp @_ @_ @_ @l xs

-- Instance for the result
instance (HasFieldD s (Dict m) t) => 
     HasFieldD s (Result m) (Maybe t) where
  getFieldD (Just x) = Just  (getFieldD @s x)
  getFieldD Nothing = Nothing

-- Instance for a list of entries
instance (Get (Find s m :: Index s o m), t ~ TOcc o) =>
                      HasFieldD s (Dict m) t where
  getFieldD x = getp @_ @_ @_ @(Find s m) x

class HasField (x :: k) r a | x r -> a where
  getField    :: r -> a

instance (SingI o, (Get (Find n s :: Index n o s))) => HasField n (Result s) [String] where
  getField (Just x) = gg (sing :: Sing o) (getp @_ @_ @_ @(Find n s) x) where
     gg :: Sing o -> TOcc o -> [String]
     gg SStr s = [s]
     gg SOpt (Just s) = [s]
     gg SOpt Nothing  = []
     gg SMany s = s
  getField Nothing  = [] 

-------------------------------------------------------------------------

-- Our GADT, indexed by the set of pattern variables
-- Note that we require all sets to be Wf. (Empty is known to be.)
data R (s :: U) where
  Rempty :: R Empty 
  Rvoid  :: R s
  Rseq   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt   s1 s2)
  Rstar  :: (Wf s) => R s  -> R (Repeat s)
  Rchar  :: Set Char -> R Empty
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rmark  :: (Wf s) => Sing sym -> String -> R s -> R (Merge (One sym) s)

-------------------------------------------------------------------------
-- smart constructors
-- we might as well optimize the regular expression whenever we
-- build it.  


-- reduces (r,epsilon) (epsilon,r) to just r
-- (r,void) and (void,r) to void
rseq :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq r1 r2 | Just Refl <- isEmpty r1 = r2
rseq r1 r2 | Just Refl <- isEmpty r2 = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2

ralt :: forall s1 s2. (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt s1 s2)
ralt r1@Rvoid r2 = case (sing :: Sing s1, sing :: Sing s2) of
   (SNil, SNil) -> r2
   _ -> Ralt r1 r2
ralt r1 r2@Rvoid = case (sing :: Sing s1, sing :: Sing s2) of
   (SNil, SNil) -> r1
   _ -> Ralt r1 r2
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2 = Ralt r1 r2


-- convenience function for marks
-- MUST use explicit type application for 'sym' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) => R s -> R (Merge (One n) s)
rmark r = rmarkSing (sing @Symbol @n) r

rmarkSing :: forall n s proxy.
   (KnownSymbol n, Wf s) => proxy n -> R s -> R (Merge (One n) s)
rmarkSing n r = Rmark (sing @Symbol @n) "" r

-- r** = r*
-- empty* = empty
rstar :: (Wf s) => R s -> R (Repeat s)
rstar (Rstar s) = Rstar s
rstar r | Just Refl <- isEmpty r = r
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R Empty
rvoid = Rvoid

rempty :: R Empty
rempty = Rempty

-- convenience function for single characters
rchar :: Char -> R Empty
rchar c = Rchar (Set.singleton c)

rchars :: Set Char -> R Empty
rchars s = Rchar s


------------------------------------------------------
isVoid :: R s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rstar r)      = False
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False



-- is this the regexp that accepts only the empty string?
isEmpty :: Wf s => R s -> Maybe (s :~: Empty)
isEmpty Rempty    = Just Refl
isEmpty (Rstar r) = case isEmpty r of
    Just Refl -> Just Refl
    Nothing   -> Nothing
isEmpty _         = Nothing


markResult :: Sing n -> String -> Result (One n)
markResult n s = Just (Entry n SStr s :> Nil)

-- | extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
{-
extract :: forall s. Wf s => R s -> Result s
extract Rempty       = Just Nil
extract (Rchar cs)   = Nothing 
extract (Rseq r1 r2) = both (extract r1) (extract r2)
extract (Ralt r1 r2) = first (extract r1) (extract r2)
extract (Rstar r)    = Just $ nils @s
extract (Rmark n s r) = both (markResult n s) (extract r)
extract (Rnot cs)    = if Set.null cs then Nothing else Just Nil
extract _            = Nothing
-}
