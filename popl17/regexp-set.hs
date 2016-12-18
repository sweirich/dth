{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, FunctionalDependencies #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

{-# LANGUAGE TemplateHaskell #-}
import Language.Haskell.TH hiding (Type, match)

-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using (Partial) Derivatives

-- This version doesn't use partial (Antimorov) derivatives. For
-- simplicity it uses the Brzowozki derivatives instead.

import Data.Kind (Type)
import Data.Type.Equality ((:~:)(..),TestEquality(..))

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude 
import Data.Singletons.TypeLits (Symbol(..),KnownSymbol(..))

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

-- Singleton symbol
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s


-------------------------------------------------------------------------
-- Type system keeps track of a list of all possible
-- labels that *could* appear in the output

type U = [Symbol]

instance Ord Symbol where (<=) = error "no term"
instance Eq  Symbol where (==) = error "no term"
-- Type-level set operation


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


{-

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
-}

-- Well-founded sets are exactly those constructed only
-- from a finite number of [] and :
-- Well-founded sets have the property (among others) that
-- merge is XXX
class (m ~ Merge m m) => WfSet (m :: U) where

-- note the superclass constraint is proved automatically
-- by Haskell's type class resolution 
instance WfSet '[] where
instance (WfSet s) => WfSet (a : s) where

-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: U where
  T = "a" : T

testWf :: WfSet a => ()
testWf = ()

-- x1 = testWf '[ "a", "b", "c"]
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
   Entry :: KnownSymbol s => proxy s -> [String] -> Entry s                                                                          
data List sa (s :: [Symbol]) where
   Nil  :: List sa '[]
   Cons :: sa a -> List sa tl -> List sa (a : tl)

------
-- show instance
data EEntry = EEntry String [String]
instance Show EEntry where
  show (EEntry s ss) = s ++ ":" ++ show ss

toList :: List Entry s -> [ EEntry ]
toList Nil = []
toList (Cons (Entry ps ss) xs) = (EEntry (symbolVal ps) ss) : toList xs
             
instance Show (List Entry s) where
  show x = show (toList x)
--------

--iempty :: Result Empty
--iempty = Just Nil

--zero :: Result Empty
--zero = Nothing

mark :: forall s p. KnownSymbol s => p s -> String -> Result (One s)
mark s t = Just (Cons (Entry s [t]) Nil)

-- this is odd. why is this Nothing instead of
-- Just (Cons (Entry s []) Nil)?
-- Needed to be this way to make the 
nomark :: forall s p. KnownSymbol s => p s -> Result (One s)
nomark s = Nothing

-- Is there a way we can work "top-down" instead of bottom up?
-- i.e. if we know the set to begin with, we should be able to
-- just combine elementwise  (seems difficult)
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

star :: R s -> Result s -> Result s
star r1 x = maxr Rempty r1 (Just Nil) x



nullresult :: R s -> List Entry s 
nullresult Rempty       = Nil
nullresult Rvoid        = Nil
nullresult (Rchar c)    = Nil
nullresult (Rseq r1 r2) = combine (nullresult r1) (nullresult r2)
nullresult (Ralt r1 r2) = combine (nullresult r1) (nullresult r2)
nullresult (Rstar r)    = nullresult r
nullresult (Rmark (ps :: p s) s r) =
  combine (Cons (Entry ps []) Nil) (nullresult r)

-- coerce a term to include extra entries for missing labels
maxr :: R s1 -> R s2 -> Result s1 -> Result s2 -> Result (Merge s1 s2)
maxr r1 r2 Nothing y = fmap (combine (nullresult r1)) y
maxr r1 r2 x  _      = fmap (\x -> combine x (nullresult r2)) x
         
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

-- Using a closed type family to implement the partial function
type family Find (s :: Symbol) (m :: U) (m2 :: U) :: Index s m where
  Find s (s: m) m2 = DH
  Find s (t: m) m2 = DT (Find s m m2)
  Find s '[] m2 = TypeError (Text s :<>: Text " not found in " :$$:
                             Text "    " :<>: ShowU m2)

class Get (p :: Index s m) where
  getp :: List Entry m -> [String]

instance Get DH where
  getp (Cons (Entry _ v) _ ) = v

instance (Get l) => Get (DT l) where
  getp    (Cons _ xs) = getp @_ @_ @l xs

-- Instance for the result
instance (HasField s (List Entry m) [String]) => 
     HasField s (Result m) (Maybe [String]) where
  getField x = fmap (getField @s) x

-- Instance for a list of entries
instance (p ~ (Find s m m :: Index s m), Get p) =>
     HasField s (List Entry m) [String] where
  getField x = getp @_ @_ @p x




-------------------------------------------------------------------------
-- smart constructors
-- we might as well optimize the regular expression whenever we
-- build it.  

-- smart constructor -- optimizes on construction
-- reduces: r + void, void + r, and r + r to just r
ralt :: forall s1 s2. (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
ralt Rvoid r = r
ralt r Rvoid = r
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
rseq r1 r2    = Rseq r1 r2

rmark :: forall sym s proxy. (KnownSymbol sym, WfSet s) =>
     R s -> R (Merge (One sym) s)
rmark r = Rmark (sym @sym) "" r

rchar :: Char -> R Empty
rchar s = Rchar (Set.singleton s)

-- r** = r*
rstar :: (WfSet s) => R s -> R s
rstar (Rstar s) = Rstar s
rstar s = Rstar s

-- for completeness, not necessary
rempty :: R Empty
rempty = Rempty

-- Our GADT, indexed by the set of pattern variables
-- Note that we require all sets to be Wf. (Empty is known to be.)
data R (ss :: U) where
  Rempty :: R Empty
  Rvoid  :: R Empty
  Rseq   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (WfSet s1, WfSet s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Rstar  :: (WfSet s) => R s  -> R s
  Rchar  :: (Set.Set Char) -> R Empty
  Rmark  :: (KnownSymbol sym, WfSet s) =>
     proxy sym -> String -> R s -> R (Merge (One sym) s)

-- We can compare two regular exprssions for equality, see above
-- if they are equal then their index sets are equal
instance TestEquality R where
  Rempty     `testEquality` Rempty     = Just Refl
  Rvoid      `testEquality` Rvoid      = Just Refl
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
  _          `testEquality` _          = Nothing
  

-- displaying regular expressions  
instance Show (R n) where
  show Rempty = "ε"
  show Rvoid  = "∅"   
  show (Rseq r1 r2)   = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = show c
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: WfSet s => R s -> String -> Result s
match r w = extract (deriveWord r w)

deriveWord :: WfSet n => R n -> String -> R n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 

extract :: WfSet s => R s -> Result s
extract Rempty       = Just Nil
extract Rvoid        = Nothing 
extract (Rchar c)    = Just Nil
extract (Rseq r1 r2) = join (extract r1) (extract r2)
extract (Ralt r1 r2) = maxr r1 r2 (extract r1) (extract r2)
extract (Rstar r)    = star r (extract r)
extract (Rmark (ps :: p s) s r) =
  if nullable r
    then join (mark ps s) (extract r)
    else join (Nothing :: Result (One s))(extract r)

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rempty         = True
nullable (Rchar cs)     = Set.empty == cs
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
markEmpty (Rmark p w r) | nullable r = (Rmark p w (markEmpty r))
markEmpty (Rmark p w r) = Rmark p w (markVoid r)
markEmpty (Ralt r1 r2)  = Ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = Rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = Rstar (markEmpty r)
markEmpty r             = r

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

-- regular expression derivative function
deriv :: forall n. WfSet n => R n -> Char -> R n
deriv (Rchar s)    c   = if Set.member c s then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) (rseq (markEmpty r1) (deriv r2 c))
deriv (Rstar (r :: R s)) c = 
     (rseq (deriv r c) (rstar r))
deriv (Rseq r1 r2) c   = rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)

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

digit = Rchar (Set.fromList (map (head . show) [0 .. 9]))
dash  = Rchar (Set.fromList ['-','.',' '])

opt_dash = ralt rempty dash

phone = rmark @"phone"
   (digit `rseq` digit `rseq` digit `rseq` opt_dash `rseq`
    digit `rseq` digit `rseq` digit `rseq` digit)

alpha = Rchar (Set.fromList ['a' .. 'z' ])
name  = rmark @"name" alpha

entry = name `rseq` (rstar opt_dash) `rseq` phone



