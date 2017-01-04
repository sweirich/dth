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

module RegexpSet
       where

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..),TestEquality(..))

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
-- symbols.
type U = [Symbol]

type Empty = '[]

type One n = '[ n ]

-- | Union of two sets, defined as a closed type family
-- Assumes both lists are sorted
type family Union (a :: U) (b :: U) :: U where
    Union '[] '[] = '[]
    Union m '[] = m
    Union '[] m = m
    Union (n1:t1)(n2:t2) =
      If (n1 :== n2)
         (n1 : Union t1 t2)
         (If (n1 :<= n2) (n1 : Union t1 (n2:t2)) (n2 : Union (n1:t1) t2))

-- Well-founded sets are exactly those constructed only
--   from a finite number of [] and :
-- Well-founded have the property (among others) that
--   the union of a set with itself does not change the set
-- They also have singletons (SingI) for these sets,
-- which we wouldn't need if Haskell were a full-spectrum
-- dependently-typed language
class (s ~ Union s s, SingI s) => Wf (s :: U) where
  
instance Wf '[] where
instance (SingI n, Wf s) => Wf (n : s) where
  

------------------------------------------------------------------------  
-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the union property?)
type family T :: U where
  T = "a" : T

testWf :: Wf a => ()
testWf = ()

x1 = testWf @'[ "a", "b" ]
-- x2 = testWf @T   -- doesn't type check

------------------------------------------------------------------------
-- Shhh! Don't tell anyone!

type Π n = Sing n
------------------------------------------------------------------------
-- A dictionary indexed by a type-level set (the domain)
-- Keeps the entries in the same sorted order as the keys
-- For convenience, we store the keys in the data structure, although
--     this is not strictly required.

type Result (s :: U) = Maybe (EntryList s)

data Entry (n :: Symbol) where
   Entry :: Π n -> [String] -> Entry n
   
data EntryList (s :: [Symbol]) where
   Nil  :: EntryList '[]
   (:>) :: Entry n -> EntryList tl -> EntryList (n : tl) 

infixr 5 :>


------

combine :: EntryList s1 -> EntryList s2 -> EntryList (Union s1 s2)
combine Nil Nil = Nil
combine Nil b   = b
combine b   Nil = b
combine (e1@(Entry n1 ss1) :> t1) (e2@(Entry n2 ss2) :> t2) =
  case (n1 %:== n2) of
   STrue ->  Entry n1 (ss1 ++ ss2) :> combine t1 t2     
   SFalse -> case n1 %:<= n2 of
     STrue  -> e1 :> combine t1 (e2 :> t2)
     SFalse ->  e2 :> combine (e1 :> t1) t2 

-- Combine two results together, combining their lists (if present)
-- If either result fails, return Nothing
both :: Result s1 -> Result s2 -> Result (Union s1 s2)
both (Just xs) (Just ys) = Just $ combine xs ys
both _         _         = Nothing



-- nils for each string in the regular expression
nils :: SingI s => EntryList s
nils = nils' sing where 
    nils' :: Sing ss -> EntryList ss
    nils' SNil         = Nil
    nils' (SCons sn r) = Entry sn [] :> nils' r

-- Combine two results together, taking the first successful one
-- (if present) 
-- Note that we need to merge in empty labels for the ones that may
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
instance (HasField n (EntryList s) t) => HasField n (Result s) (Maybe t) where
  getField (Just x) = Just  (getField @n x)
  getField Nothing  = Nothing

-- Instance for a list of entries: first we have to find the string in the
-- list (using the Find type family), and then we have to access the data
-- structure using that index (using the Get type class).
instance (Get (Find n s)) => HasField n (EntryList s) [String] where
  getField x = getIndex @_ @_ @(Find n s) x


data Index (n :: Symbol) (s :: U) where
  DH :: Index n (n:s)
  DT :: Index n s -> Index n (m:s)

type family Find (n :: Symbol) (s :: U) :: Index n s where
  Find n s = FindH n s s

-- Using a closed type family to implement the partial function
-- We take the list twice so that we can use it in the custom error message
type family FindH (n :: Symbol) (s :: U) (t :: U) :: Index n s where
  FindH n (n: s) t = DH
  FindH n (m: s) t = DT (FindH n s t)
  FindH n '[]    t = TypeError (Text n :<>: Text " not found in domain " :$$:
                                 Text "    {" :<>: ShowU t :<>: Text "}")

type family ShowU (s :: U) :: ErrorMessage where
  ShowU '[]   = Text ""
  ShowU '[n]  = Text n
  ShowU (n:s) = Text n :<>: Text ", " :<>: ShowU s

-- Look up in the list, given an index into the list. This function is total
-- because we know that the string will be in the domain.
class Get (p :: Index n s) where
  getIndex :: EntryList s -> [String]

instance Get DH where
  getIndex (Entry _ v :> _) = v

instance (Get i) => Get (DT i) where
  getIndex (_ :> xs) = getIndex @_ @_ @i xs



-------------------------------------------------------------------------
-- Smart constructors for regular expressions:
--
-- We optimize the regular expression whenever we
-- build it. These optimizations are necessary for efficient execution of
-- the regular expression matcher.

-- Construct an alternative
-- reduces: r + r to just r
ralt :: (Wf s1, Wf s2) =>
        R s1 -> R s2 -> R (Union s1 s2)
--ralt r1 r2 | isVoid r1 = r2  -- cannot do this because may be remembering some marks
--ralt r1 r2 | isVoid r2 = r1
--ralt r1 r2 | Just Refl <- r1 `testEquality` r2 = r1 
ralt r1 r2 = Ralt r1 r2

-- reduces (r,epsilon) (epsilon,r) to r
-- (r,void) and (void,r) to void
rseq :: (Wf s1, Wf s2) =>
        R s1 -> R s2 -> R (Union s1 s2)
rseq r1 r2 | Just Refl <- isEmpty r1 = r2
rseq r1 r2 | Just Refl <- isEmpty r2 = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2

isVoid :: R s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rstar r)      = isVoid r
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

isEmpty :: R s -> Maybe (s :~: Empty)
isEmpty (Rchar s) = if Set.null s then Just Refl else Nothing
isEmpty _ = Nothing

-- convenience function for marks
-- MUST use scoped type variables and
-- explicit type application for 'sym' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) =>
     R s -> R (Union (One n) s)
rmark r = Rmark (sing @Symbol @n) "" r

-- r** = r*
-- empty* = empty
rstar :: (Wf s) => R s -> R s
rstar (Rstar s) = Rstar s
rstar r | Just Refl <- isEmpty r = rempty
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R Empty
rvoid = Rvoid

-- convenience function for empty string
rempty :: R Empty
rempty = Rchar Set.empty

-- convenience function for single characters
rchar :: Char -> R Empty
rchar c = Rchar (Set.singleton c)

-- completeness
rchars :: Set Char -> R Empty
rchars s = Rchar s


-- Our GADT, indexed by the set of pattern variables
data R (ss :: U) where
  -- Rempty :: R Empty  -- can replace with RChar (Set.empty)
  Rvoid  :: R s      -- try adding a singleton here to pin down s?
                     -- can be anything b/c will always fail
  Rseq   :: (Wf s1, Wf s2) =>
            R s1 -> R s2 -> R (Union s1 s2)
  Ralt   :: (Wf s1, Wf s2) =>
            R s1 -> R s2 -> R (Union s1 s2)
  Rstar  :: (Wf s) => R s -> R s
  Rchar  :: (Set Char) -> R Empty
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rmark  :: (Wf s) => Π n -> String -> R s -> R (Union (One n) s)



------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: Wf s => R s -> String -> Result s
match r w = extract (foldl deriv r w)

-- extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: Wf s => R s -> Result s
extract (Rchar cs)
      | Set.null cs    = Just Nil 
extract (Rseq r1 r2)   = both (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = first (Just Nil)   (extract r)
extract (Rmark n s r)  = both mark (extract r) where
      mark = Just (Entry n [s] :> Nil)
extract _              = Nothing

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
-- nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = Set.empty == cs
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable (Rany)         = False
nullable (Rnot cs)      = False

-- regular expression derivative function
deriv :: forall s. Wf s => R s -> Char -> R s
deriv (Rchar s)     c = if Set.member c s then rempty else Rvoid
--deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) r1' where
       r1' = rseq (markEmpty r1) (deriv r2 c)
deriv (Rseq r1 r2)  c = rseq (deriv r1 c) r2
deriv (Ralt r1 r2)  c = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)     c = rseq (deriv r c) (rstar r)
deriv Rvoid         c = Rvoid
deriv (Rmark n w r) c = Rmark n (w ++ [c]) (deriv r c)
deriv Rany  c          = rempty
deriv (Rnot s)      c  = if Set.member c s then rvoid else rempty


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

-- create a regexp that doesn't match any strings, but still
-- contains the data at marks
markVoid :: R n -> R n
markVoid (Rmark p w r) = Rmark p w (markVoid r)
markVoid (Ralt r1 r2)  = ralt  (markVoid r1) (markVoid r2)
markVoid (Rseq r1 r2)  = rseq  (markVoid r1) (markVoid r2)
markVoid (Rstar r)     = rstar (markVoid r)
markVoid (Rchar s)     = Rvoid
--markVoid Rempty        = Rvoid
markVoid Rvoid         = Rvoid  
markVoid Rany          = Rvoid
markVoid (Rnot cs)     = Rvoid


-------------------------------------------------------------------------

-- Show instance for the EntryList dictionary
instance Show (Entry s) where
  show (Entry sn ss) = showSymbol sn ++ "=" ++ show ss
instance Show (EntryList s) where
  show xs = "{" ++ show' xs where
    show' :: EntryList xs -> String
    show' Nil = "}"
    show' (e :> Nil) = show e ++ "}"
    show' (e :> xs)  = show e ++ "," ++ show' xs

-------------------------------------------------------
-- Show instance for regular expressions
instance Show (R n) where
  show Rvoid  = "∅"   
  show (Rseq r1 r2) = show r1 ++ show r2
  show (Ralt r1 r2) = show r1 ++ "|" ++ show r2
  show (Rstar r)    = show r  ++ "*"
  show (Rchar cs) = if (Set.size cs == 1) then (Set.toList cs)
                   else if Set.size cs == 0 then "ε"                                            
                   else if cs == (Set.fromList ['0' .. '9']) then "\\d"
                   else if cs == (Set.fromList [' ', '-', '.']) then "\\w"
                   else "[" ++ Set.toList cs ++ "]"
  show (Rmark pn w r)  = "(<?" ++ showSymbol pn ++ ">" ++ show r ++ ")"
  show (Rany) = "."
  show (Rnot cs) = "[^" ++ show cs ++ "]"

-------------------------------------------------------------------------


-- | Convenience function for showing symbols
showSymbol :: Π (n :: Symbol) -> String
showSymbol ps = case ps of SSym -> symbolVal ps

-------------------------------------------------------------------------

-- | Singleton version of union function (not used here, but for completeness)
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
withWf :: Sing s -> (Wf s => c) -> c
withWf ss f = case wfSing ss of
  SomeSet _ -> f

data WfD s where
  SomeSet :: Wf s => p s -> WfD s

wfSing :: Sing (s :: U) -> WfD s
wfSing SNil = SomeSet SNil
wfSing s@(SCons sn ss) = case wfSing ss of
  SomeSet _ -> withSingI sn $ SomeSet s
  
-------------------------------------------------------
-- Note: we can define a monoid instance for EntryLists

instance SingI s => Monoid (EntryList s) where
  mempty  = nils

  mappend = mappend' where
    mappend' :: EntryList ss -> EntryList ss -> EntryList ss    
    mappend' Nil Nil = Nil
    mappend' (Entry n1 ss1 :> t1) (Entry _ ss2 :> t2) =
       Entry n1 (ss1 ++ ss2) :> mappend' t1 t2

------------------------------------------------------------------------
-- This does not really compare for equality --- the voids get in the way
instance TestEquality R where
--  Rempty     `testEquality` Rempty     = Just Refl
  Rany     `testEquality` Rany     = Just Refl
  Rseq t1 t2 `testEquality` Rseq u1 u2 |
    Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2    = Just Refl
  Ralt t1 t2 `testEquality` Ralt u1 u2 |
    Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2    = Just Refl
  Rstar t1   `testEquality` Rstar u1   |
    Just Refl <- testEquality t1 u1    = Just Refl
  Rchar s1   `testEquality` Rchar s2   | s1 == s2 = Just Refl
  Rnot s1   `testEquality` Rnot s2   | s1 == s2 = Just Refl
  Rmark n1 s1 r1 `testEquality` Rmark n2 s2 r2 |
    s1 == s2,
    Just Refl <- testEquality n1 n2,
    Just Refl <- r1 `testEquality` r2  = Just Refl
  Rvoid      `testEquality` Rvoid      = Nothing    -- have to ignore voids                                     
  _          `testEquality` _          = Nothing
