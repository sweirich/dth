{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, FunctionalDependencies #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses, ConstraintKinds #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE TemplateHaskell #-}
import Language.Haskell.TH hiding (Type, match)

-- This type system infers the marked subexpressions of a given
-- regular expression, and uses that information to make sure that
-- submatching are used correctly.

-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using (Partial) Derivatives
-- Note: This version doesn't use partial (Antimorov) derivatives. For
-- simplicity it uses the Brzowozki derivatives instead, which are backtracking.


import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..),TestEquality(..))

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude 
import Data.Singletons.TypeLits (Symbol(..),KnownSymbol(..),Sing(..))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char


import Data.List(foldl')

-- Singleton symbol
sym :: forall s. SingI s => Sing (s :: Symbol)
sym = sing @Symbol @s

sset :: forall s. SingI s => Sing (s :: U)
sset = sing @U @s

showSymbol :: forall (s :: Symbol) p. SingI s => p s -> String
showSymbol ps = case sing :: Sing s of SSym -> symbolVal ps

-------------------------------------------------------------------------
-- Type system keeps track of a list of all possible
-- labels that *could* appear in the output

type U = [Symbol]

--instance Ord Symbol where (<=) = error "no term"
--instance Eq  Symbol where (==) = error "no term"
-- Type-level set operation

{-
$(singletons [d|

  empty :: U
  empty = []

  one :: Symbol -> U
  one s = [s]
              
  merge :: U -> U -> U
  merge [] [] = []
  merge m  [] = m
  merge [] m  = m
  merge (s1:t1) (s2:t2) =
    if s1 == s2 then (s1 : merge t1 t2)
    else if s1 <= s2 then (s1 : merge t1 (s2:t2))
       else s2 : merge (s1:t1) t2
  |])
-}



type Empty = '[]

type One s = '[ s ]

-- Union of two sets
type family Merge (a :: U) (b :: U) :: U where
    Merge '[] '[] = '[]
    Merge m '[] = m
    Merge '[] m = m
    Merge (s1:t1)(s2:t2) =
      If (s1 :== s2)
         (s1 : Merge t1 t2)
         (If (s1 :<= s2) (s1 : (Merge t1 (s2:t2))) (s2 : (Merge (s1:t1) t2)))


type family Union s1 s2 where
   Union s1 s2 = Merge s1 s2

-- Well-founded sets are exactly those constructed only
-- from a finite number of [] and :
-- Well-founded sets have the property (among others) that
class (m ~ Union m m, SingI m) => WfSet (m :: U) where
  
-- note the superclass constraint is proved automatically
-- by Haskell's type class resolution 
instance WfSet '[] where
instance (SingI a, WfSet s) => WfSet (a : s) where

-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: U where
  T = "a" : T

testWf :: WfSet a => ()
testWf = ()

x1 = testWf @'[ "a", "b", "c" ]
-- x2 = testWf @T   -- doesn't type check

-------------------------------------------------------------------------

-- A data structure indexed by a type-level set
-- Keeps the keys in sorted order

-- Can we replace this with a (read-only) array?
-- We need to store the symbols in the data structure so that
-- we can merge them. However, we could separate the symbols and
-- store them elsewhere if we wish

type Result (s :: U) = Maybe (List Entry s)

data Entry (sym ::Symbol) where
   Entry :: (SingI s) => proxy (s :: Symbol) -> [String] -> Entry s                                                                          
data List (sa :: Symbol -> Type) (s :: [Symbol]) where
   Nil  :: List sa '[]
   Cons :: sa a -> List sa tl -> List sa (a : tl)

------
-- show instance
data EEntry = EEntry String [String]
instance Show EEntry where
  show (EEntry s ss) = s ++ ":" ++ show ss

toList :: List Entry s -> [ EEntry ]
toList Nil = []
toList (Cons (Entry (ps :: p a) ss) xs) =
  (EEntry (showSymbol ps) ss) : toList xs where x = sym @a
             
instance Show (List Entry s) where
  show x = show (toList x)
------

-- nils for each string in the regular expression
-- like "mempty" for the 'List Entry s' monoid
nils :: Sing s -> List Entry s
nils SNil = Nil
nils (SCons ps r) = Cons (withSingI ps (Entry ps) []) (nils r)

-- if s1 == s2 then this is "mappend" for the List Entry monoid
-- (but, not the usual list monoid, the one where we glue each element
-- together pointwise)
-- this is *almost* sMerge, but it works with entries, not singleton symbols
combine :: List Entry s1 -> List Entry s2 -> List Entry (Merge s1 s2)
combine Nil Nil = Nil
combine Nil b = b
combine b Nil = b
combine (Cons e1@(Entry (ps :: p s) ss) t1) (Cons e2@(Entry (pt :: p2 t) ts) t2) =
  case ((sym @s) %:== (sym @t)) of
   STrue ->  Cons (Entry ps (ss ++ ts)) (combine t1 t2)     
   SFalse -> case sCompare (sym @s) (sym @t) of
     SLT  -> Cons e1 (combine t1 (Cons e2 t2))
     SGT ->  Cons e2 (combine (Cons e1 t1) t2) 

-- combine the two sets together
join :: Result s1 -> Result s2 -> Result (Merge s1 s2)
join xss yss = do
  xs <- xss
  ys <- yss
  return $ combine xs ys 

-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
firstSuccess :: forall s1 s2. (SingI s1, SingI s2) =>
                      Result s1 -> Result s2 -> Result (Merge s1 s2)
firstSuccess Nothing y = fmap (combine (nils (sset @s1))) y
firstSuccess x  _      = fmap (\x -> combine x (nils (sset @s2))) x


                       
-------------------------------------------------------------------------

-- eventually in data.record
class HasField (x :: k) r a | x r -> a where
  getField    :: r -> a

data Index (s :: Symbol) (m :: U) where
  DH :: Index s (s:m)
  DT :: Index s m -> Index s (t:m)

type family ShowU (m :: U) :: ErrorMessage where
  ShowU '[] = Text ""
  ShowU '[a] = Text a
  ShowU (a: m) = Text a :<>: Text ", " :<>: ShowU m

type family Find (s :: Symbol) (m :: U) :: Index s m where
  Find s m = FindH s m m

-- Using a closed type family to implement the partial function
type family FindH (s :: Symbol) (m :: U) (m2 :: U) :: Index s m where
  FindH s (s: m) m2 = DH
  FindH s (t: m) m2 = DT (FindH s m m2)
  FindH s '[] m2    = TypeError (Text s :<>: Text " not found in " :$$:
                                 Text "    " :<>: ShowU m2)

-- How to look up in the list, given an index
class Get (p :: Index s m) where
  getp :: List Entry m -> [String]

instance Get DH where
  getp (Cons (Entry _ v) _ ) = v

instance (Get l) => Get (DT l) where
  getp (Cons _ xs) = getp @_ @_ @l xs

-- Instance for the result
instance (HasField s (List Entry m) [String]) => 
     HasField s (Result m) (Maybe [String]) where
  getField (Just x) = Just  (getField @s x)
  getField Nothing = Nothing

-- Instance for a list of entries
instance (Get (Find s m)) => HasField s (List Entry m) [String] where
  getField x = getp @_ @_ @(Find s m) x




-------------------------------------------------------------------------
-- smart constructors
-- we might as well optimize the regular expression whenever we
-- build it.  

-- smart constructor -- optimizes on construction
-- reduces: r + r to just r
ralt :: forall s1 s2. (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
--ralt Rvoid r = r
--ralt r Rvoid = r
ralt r1 r2 | Just Refl <- r1 `testEquality` r2 = r1 
ralt r1 r2 = Ralt r1 r2

-- reduces (r,epsilon) (epsilon,r) to just r
-- and r*r* to r*
-- our abstraction won't let us optimize (r,void) -> void though
-- it doesn't know that the matches in r cannot occur.
rseq :: forall s1 s2. (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq Rempty r = r
rseq r Rempty = r
rseq (Rstar r1) (Rstar r2) | Just Refl <- r1 `testEquality` r2 = (Rstar r1)
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
-- void* = void
rstar :: (WfSet s) => R s -> R s
rstar (Rstar s) = Rstar s
rstar Rempty = Rempty
rstar Rvoid = Rvoid
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R Empty
rvoid = Rvoid

-- for completeness, not necessary
rempty :: R Empty
rempty = Rempty


-- Our GADT, indexed by the set of pattern variables
-- Note that we require all sets to be Wf. (Empty is known to be.)
data R (ss :: U) where
  Rempty :: R Empty
  Rvoid  :: R s  -- try adding a singleton here to pin down s
                 -- can be anything b/c will always fail
  Rseq   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Rstar  :: (WfSet s) => R s  -> R s
  Rchar  :: (Set Char) -> R Empty
  Rmark  :: (KnownSymbol sym, WfSet s) =>
     proxy sym -> String -> R s -> R (Merge (One sym) s)

-- This does not really compare for equality --- the voids get in the way
instance TestEquality R where
  Rempty     `testEquality` Rempty     = Just Refl
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
  show Rempty = "ε"
  show Rvoid  = "∅"   
  show (Rseq r1 r2) = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = if c == (Set.fromList ['0' .. '9']) then "\\d"
                   else if c == (Set.fromList [' ', '-', '.']) then "\\w"
                   else show c
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

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
extract Rempty       = Just Nil
extract Rvoid        = Nothing 
extract (Rchar cs)   = Nothing
extract (Rseq r1 r2) = join (extract r1) (extract r2)
extract (Ralt r1 r2) = firstSuccess (extract r1) (extract r2)
extract (Rstar r)    = firstSuccess (Just Nil)   (extract r)
extract (Rmark (ps :: p s) s r) =
  if nullable r
    then join (mark ps s)   (extract r)
    else join @'[s] Nothing (extract r)
  where
    mark ps t = Just (Cons (Entry ps [t]) Nil)

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = Set.empty == cs
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r


-- regular expression derivative function
deriv :: forall n. WfSet n => R n -> Char -> R n
deriv (Rchar s)    c   = if Set.member c s then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) (rseq (markEmpty r1) (deriv r2 c))
deriv (Rseq r1 r2) c   = rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar (r :: R s)) c = (rseq (deriv r c) (rstar r))
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)

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
markEmpty (Rchar c)     = Rempty
markEmpty Rvoid         = Rvoid
markEmpty Rempty        = Rempty

-- create a regexp that doesn't match any strings, but still
-- contains the data at marks
markVoid :: R n -> R n
markVoid (Rmark p w r) = Rmark p w (markVoid r)
markVoid (Ralt r1 r2)  = Ralt  (markVoid r1) (markVoid r2)
markVoid (Rseq r1 r2)  = Rseq  (markVoid r1) (markVoid r2)
markVoid (Rstar r)     = Rstar (markVoid r)
markVoid (Rchar s)     = Rvoid
markVoid Rempty        = Rvoid
markVoid Rvoid         = Rvoid  


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

opt_dash = ralt dash rempty

phone = rmark @"phone"
   (digit `rseq` digit `rseq` digit `rseq` opt_dash
    `rseq` digit `rseq`  digit `rseq` digit `rseq` digit)

alpha  = Rchar (Set.fromList ['a' .. 'z' ])
alphaC = Rchar (Set.fromList ['A' .. 'Z' ])

name   = rmark @"name" (rseq alphaC (rstar alpha))

entry  = name `rseq` rstar opt_dash `rseq` phone 

pbook  = rstar (rchar '(' `rseq` (rmark @"entry" entry) `rseq` rchar ')')

pbookstring = "(Steve 123-2222)(Stephanie   1202323)(Ellie 121.1222)(Sarah 324-3444)"

-------------------------------------------------------------------------

result = match pbook pbookstring


nm  = getField @"name"  result
num = getField @"phone" result

-- Doesn't type check
-- bad = getField @"email" result

-------------------------------------------------------------------------

-- difficult pattern for backtracking implementations, like this one.
difficult = rstar (ralt (rchar 'a') (rchar 'a' `rseq` rchar 'a')) `rseq` (rchar 'b')

sloooow =  match difficult "aaaaaaaaaaaaaaaaaaaaaaaab"
