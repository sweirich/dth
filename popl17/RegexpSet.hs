{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, FunctionalDependencies #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses, ConstraintKinds #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- This type system infers the set of names for marked subexpressions of a
-- given regular expression, and uses that information to construct the
-- appropriate result of submatching.

-- Based on:
-- Sulzmann & Lu
-- "Regular Expression SubMatching Using (Partial) Derivatives"
-- Note: For simplicity, this implementation uses the Brzowozki
-- derivatives, which are Posix based and backtracking.

-- See RegexpExample.hs for this library in action.

module RegexpSet where

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..), TestEquality(..))

import GHC.TypeLits(TypeError(..),ErrorMessage(..),symbolVal,Symbol(..),KnownSymbol(..))
import Data.Singletons.Prelude
    ((:<=),(:==),If(..),(%:==),(%:<=),Sing(STrue,SFalse,SNil,SCons),SingI(..),withSingI)
import Data.Singletons.TypeLits (Sing(SSym))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

import Data.List(foldl')

-------------------------------------------------------------------------
-- Type system keeps track of the set of all possible
-- marked subpatterns that *could* appear in the output

-- We represent such sets in the type system as a sorted list of
-- symbols, aka names (n).
type S = [Symbol]

type Empty = '[]

type One n = '[ n ]

-- | Union of two sets, defined as a closed type family
-- Assumes both lists are sorted
type family Union (a :: S) (b :: S) :: S where
    Union '[] '[] = '[]
    Union m '[] = m
    Union '[] m = m
    Union (n1:t1) (n2:t2) =
      If (n1 :== n2)
         (n1 : Union t1 t2)
         (If (n1 :<= n2)
             (n1 : Union t1 (n2:t2))
             (n2 : Union (n1:t1) t2))
-- Note that :== and :<= are equality and comparison operators for Symbols
-- defined in the GHC.TypeLits extension.


-- Well-founded sets are exactly those constructed only from [] and :
-- Well-founded sets have the property (among others) that
-- the union of a set with itself does not change the set.
-- Haskell can prove this property (automatically) for [] and :
-- Well-founded sets also have singletons (SingI constraints),
-- which we wouldn't need if Haskell were a full-spectrum
-- dependently-typed language
class (s ~ Union s s,
      SingI s) => Wf (s :: S) where
instance Wf '[] where
instance (SingI n, Wf s) => Wf (n : s) where


------------------------------------------------------------------------
-- Shhh! Don't tell anyone!

type Π n = Sing n

------------------------------------------------------------------------
-- A dictionary indexed by a type-level set (the potential domain)

type Result (s :: S) = Maybe (Dict s)

data Entry (n :: Symbol) where
   Entry :: Π n -> [String] -> Entry n

data Dict (s :: S) where
   Nil   :: Dict '[]
   (:>)  :: Entry n -> Dict s -> Dict (n : s)

infixr 5 :>

-------------------------------------------------------------------------
-- Show instances

instance Show (Sing (n :: Symbol)) where
  show ps@SSym = symbolVal ps

instance Show (Entry s) where
  show (Entry sn ss) = show sn ++ "=" ++ show ss where

instance Show (Dict s) where
  show xs = "{" ++ show' xs where
    show' :: Dict xs -> String
    show' Nil = "}"
    show' (e :> Nil) = show e ++ "}"
    show' (e :> xs)  = show e ++ "," ++ show' xs


------


combine :: Dict s1 -> Dict s2 -> Dict (Union s1 s2)
combine Nil Nil = Nil
combine Nil d   = d
combine d   Nil = d 
combine (e1@(Entry n1 ss1) :> t1)
        (e2@(Entry n2 ss2) :> t2) =
  case (n1 %:== n2) of
   STrue ->  Entry n1 (ss1 ++ ss2) :> combine t1 t2     
   SFalse -> case n1 %:<= n2 of
     STrue  -> e1 :> combine t1 (e2 :> t2)
     SFalse -> e2 :> combine (e1 :> t1) t2 

-- | Combine two results together, combining their lists (if present)
-- If either result fails, return Nothing
both :: Result s1 -> Result s2 -> Result (Union s1 s2)
both (Just xs) (Just ys) = Just $ combine xs ys
both _         _         = Nothing

-- A "default" Dict.
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
nils :: SingI s => Dict s
nils = nils' sing where 
    nils' :: Sing ss -> Dict ss
    nils' SNil        = Nil
    nils' (SCons n r) = Entry n [] :> nils' r



-- | Combine two results together, taking the first successful one
-- Note that we need to add in empty labels for the ones that may
-- not be present in the successful version
first :: forall s1 s2. (SingI s1, SingI s2) =>
                Result s1 -> Result s2 -> Result (Union s1 s2)
first Nothing  Nothing  = Nothing                      
first Nothing  (Just y) = Just $ nils @s1 `combine` y
first (Just x) _        = Just $ x `combine` nils @s2



-------------------------------------------------------------------------
-- Type class instances for accessing the dictionary statically.

-- This general purpose class for overloaded record selectors will 
-- eventually be added to  Data.Record. We can use this generic interface
-- for our special purpose result data structure
class HasField (n :: k) r a | n r -> a where
  getField    :: r -> a

-- Instance for the result
instance (HasField n (Dict s) [t]) => HasField n (Result s) [t] where
  getField (Just x) = (getField @n x)
  getField Nothing  = []

-- Instance for a list of entries: first we have to find the string in the
-- list (using the Find type family), and then we have to access the data
-- structure using that index (using the Get type class).
instance (Get (Find n s)) => HasField n (Dict s) [String] where
  getField x = getIndex @_ @_ @(Find n s) x


data Index (n :: Symbol) (s :: S) where
  DH :: Index n (n:s)
  DT :: Index n s -> Index n (m:s)

type family Find (n :: Symbol) (s :: S) :: Index n s where
  Find n s = FindH n s s

-- Using a closed type family to implement the partial function
-- We take the list twice so that we can use it in the custom error message
type family FindH (n :: Symbol) (s :: S) (t :: S) :: Index n s where
  FindH n (n: s) t = DH
  FindH n (m: s) t = DT (FindH n s t)
  FindH n '[]    t = TypeError (Text n :<>: Text " not found in domain " :$$:
                                 Text "    {" :<>: ShowU t :<>: Text "}")

type family ShowU (s :: S) :: ErrorMessage where
  ShowU '[]   = Text ""
  ShowU '[n]  = Text n
  ShowU (n:s) = Text n :<>: Text ", " :<>: ShowU s

-- Look up in the list, given an index into the list. This function is total
-- because we know that the string will be in the domain.
class Get (p :: Index n s) where
  getIndex :: Dict s -> [String]

instance Get DH where
  getIndex (Entry _ v :> _) = v

instance (Get i) => Get (DT i) where
  getIndex (_ :> xs) = getIndex @_ @_ @i xs

------------------------------------------------------
-- Our GADT for regular expressions
-- indexed by the set of pattern names
data R (s :: S) where
  Rempty :: R Empty   
  Rvoid  :: R s       
  Rseq   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Union s1 s2)
  Ralt   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Union s1 s2)
  Rstar  :: (Wf s) => R s -> R s
  Rchar  :: (Set Char) -> R Empty
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rmark  :: (Wf s) => Sing n -> String -> R s -> R (Union (One n) s)


-------------------------------------------------------------------------
-- Smart constructors for regular expressions
--
-- We optimize the regular expression whenever we build it. These
-- optimizations are necessary for efficient execution of the regular
-- expression matcher.

-- reduces (r,epsilon) (epsilon,r) to r
-- (r,void) and (void,r) to void
rseq :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Union s1 s2)
rseq r1 r2 | Just Refl <- isEmpty r1 = r2
rseq r1 r2 | Just Refl <- isEmpty r2 = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2

ralt :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Union s1 s2)
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2                 = Ralt r1 r2

-- convenience function for marks
-- MUST use scoped type variables and
-- explicit type application for 'n' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) => R s -> R (Union (One n) s)
rmark r = rmarkSing (sing @Symbol @n) r

rmarkSing :: forall n s proxy.
   (KnownSymbol n, Wf s) => proxy n -> R s -> R (Union (One n) s)
rmarkSing n r = Rmark (sing @Symbol @n) "" r

-- r** ~> r*
-- empty* ~> empty
rstar :: (Wf s) => R s -> R s
rstar (Rstar s) = Rstar s
rstar r | Just Refl <- isEmpty r = rempty
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R Empty
rvoid = Rvoid

-- convenience function for empty string
rempty :: R Empty
rempty = Rempty

-- convenience function for single characters
rchar :: Char -> R Empty
rchar c = Rchar (Set.singleton c)

-- completeness
rchars :: Set Char -> R Empty
rchars s = Rchar s

------------------------------------------------------
-- is this the regexp that always fails?
isVoid :: R s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rstar r)      = isVoid r
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- is this the regexp that accepts only the empty string?
isEmpty :: R s -> Maybe (s :~: Empty)
isEmpty Rempty  = Just Refl
isEmpty _       = Nothing

markResult :: Sing n -> String -> Result (One n)
markResult n s = Just (Entry n [s] :> Nil)





{-
------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: Wf s => R s -> String -> Result s
match r w = extract (foldl' deriv r w)
-}

{-
-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = True
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable (Rany)         = False
nullable (Rnot cs)      = False

-- regular expression derivative function
deriv :: forall s. Wf s => R s -> Char -> R s
deriv Rempty        c = Rvoid
deriv (Rseq r1 r2)  c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) 
          (rseq (markEmpty r1) (deriv r2 c))
deriv (Rseq r1 r2)  c = rseq (deriv r1 c) r2
deriv (Ralt r1 r2)  c = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)     c = rseq (deriv r c) (rstar r)
deriv Rvoid         c = Rvoid
deriv (Rmark n w r) c = Rmark n (w ++ [c]) (deriv r c)
deriv (Rchar s)     c = if Set.member c s then rempty else Rvoid
deriv Rany  c         = rempty
deriv (Rnot s)      c = if Set.member c s then Rvoid else rempty


-- Create a regexp that *only* matches the empty string
-- (if it matches anything), but retains all captured strings
markEmpty :: R n -> R n
markEmpty (Rmark p w r) | nullable r = (Rmark p w (markEmpty r))
markEmpty (Rmark p w r) = Rvoid
markEmpty (Ralt r1 r2)  = ralt (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = rseq (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = markEmpty r
markEmpty (Rchar s)     = rempty
markEmpty Rany          = rempty
markEmpty (Rnot cs)     = rempty
markEmpty Rvoid         = Rvoid
markEmpty Rempty        = Rempty

-}
-------------------------------------------------------------------------

{-
rinit :: R Empty -> String -> Maybe (String, String)
rinit r s | nullable r  = Just ([], s)
          | [] <- s     = Nothing
          | (x:xs) <- s = case rinit (deriv r x) xs of
              Just (hd,tl) -> Just (x:hd, tl)
              Nothing      -> Nothing
-}





-------------------------------------------------------------------------

-- | Singleton version of union function (not used here)
sUnion :: Π s1 -> Π s2 -> Sing (Union s1 s2)
sUnion SNil SNil = SNil
sUnion m    SNil = m
sUnion SNil m    = m
sUnion s1@(n1 `SCons` st1)
       s2@(n2 `SCons` st2) =
  case n1 %:== n2 of
    STrue  -> n1 `SCons` sUnion st1 st2
    SFalse -> case n1 %:<= n2 of
      STrue  -> n1 `SCons` sUnion st1 s2
      SFalse -> n2 `SCons` sUnion s1 st2


-- | All sets that we have singletons for are well-formed
-- Could replace with unsafeCoerce...
{-
withWf :: Sing s -> (Wf s => c) -> c
withWf ss f = case wfSing ss of
  SomeSet _ -> f

data WfD s where
  SomeSet :: Wf s => p s -> WfD s

wfSing :: Sing (s :: S) -> WfD s
wfSing SNil = SomeSet SNil
wfSing s@(SCons sn ss) = case wfSing ss of
  SomeSet _ -> withSingI sn $ SomeSet s
  -}
-------------------------------------------------------
-- We can define a monoid instance for Dicts

{-
instance SingI s => Monoid (Dict s) where
  mempty  = nils

  mappend = mappend' where
    mappend' :: Dict ss -> Dict ss -> Dict ss    
    mappend' Nil Nil = Nil
    mappend' (Entry n1 ss1 :> t1) (Entry _ ss2 :> t2) =
       Entry n1 (ss1 ++ ss2) :> mappend' t1 t2
 
-}

------------------------------------------------------------------------  
-- the Wf constraint rules out "infinite" sets of the form
type family T :: S where
  T = "a" : T

testWf :: Wf a => ()
testWf = ()

x1 = testWf @'[ "a", "b" ]
-- x2 = testWf @T   -- doesn't type check

