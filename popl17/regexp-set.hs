{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs, FunctionalDependencies #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

{-# LANGUAGE TemplateHaskell #-}
import Language.Haskell.TH hiding (Type, match)

-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using (Partial) Derivatives

-- This version doesn't use partial derivatives. 

import Data.Kind (Type)
import Data.Type.Equality hiding (sym)

import qualified Data.Char as Char
import GHC.TypeLits
import Data.Singletons.TH 
import Data.Singletons.Prelude
import Data.Singletons.TypeLits


import Data.Set (Set)
import qualified Data.Set as Set

import Unsafe.Coerce

axiomCompareId :: forall (a :: Symbol). Compare a a :~: EQ
axiomCompareId = unsafeCoerce Refl

-- Singleton symbol
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s


-------------------------------------------------------------------------
-- Type system keeps track of a list of all possible
-- labels that *could* appear in the output

type U = [Symbol]

-- Type-level set operation

type Empty = '[]

type One s = '[ s ]

-- Union of two sets
type family Merge (a :: U) (b :: U) :: U where
    Merge '[] '[] = '[]
    Merge (s1:t1)(s2:t2) = MergeHelper (Compare s1 s2) s1 t1 s2 t2
    Merge m '[] = m
    Merge '[] m = m
type family MergeHelper (ord :: Ordering) s1 t1 s2 t2 :: U  where
    MergeHelper EQ s  t1 s  t2   = s : Merge t1 t2
    MergeHelper LT s1 t1 s2 t2 = s1 : Merge t1 (s2:t2)
    MergeHelper GT s1 t1 s2 t2 = s2 : Merge (s1:t1) t2

-------------------------------------------------------------------------

-- A data structure indexed by a type-level set
-- Keeps the keys in sorted order

-- Can we replace this with a (read-only) array?
-- Do we need to store the symbols in the entries?

type Result (s :: U) = Maybe (List Entry s)

data Entry (sym ::Symbol) where
   Entry :: KnownSymbol s => proxy s -> [String] -> Entry s                                                                          
data List sa (s :: [Symbol]) where
   Nil  :: List sa '[]
   Cons :: sa a -> List sa tl -> List sa (a : tl)

data EEntry = EEntry String [String]
instance Show EEntry where
  show (EEntry s ss) = s ++ ":" ++ show ss

toList :: List Entry s -> [ EEntry ]
toList Nil = []
toList (Cons (Entry ps ss) xs) = (EEntry (symbolVal ps) ss) : toList xs
             

instance Show (List Entry s) where
  show x = show (toList x)

empty :: Result Empty
empty = Just Nil

zero :: Result Empty
zero = Nothing

mark :: forall s p. KnownSymbol s => p s -> String -> Result (One s)
mark s t = Just (Cons (Entry s [t]) Nil)

-- this is odd. why is this Nothing instead of
-- Just (Cons (Entry s []) Nil)?
-- Needed to be this way to make the 
nomark :: forall s p. KnownSymbol s => p s -> Result (One s)
nomark s = Nothing

-- Is there a way we can work "top-down" instead of bottom up?
-- i.e. if we know the set to begin with, we should be able to
-- just combine elementwise
-- TODO: get rid of axiomCompareId
combine :: List Entry s1 -> List Entry s2 -> List Entry (Merge s1 s2)
combine Nil Nil = Nil
combine Nil b = b
combine b Nil = b
combine (Cons e1@(Entry (ps :: p s) ss) t1) (Cons e2@(Entry (pt :: p2 t) ts) t2) =
  case (testEquality (sym @s) (sym @t)) of
   Just Refl -> case axiomCompareId @s of
     Refl -> Cons (Entry ps (ss ++ ts)) (combine t1 t2)
   Nothing -> case (sCompare (sym @s) (sym @t)) of
     SLT -> Cons e1 (combine t1 (Cons e2 t2))
     SGT -> Cons e2 (combine (Cons e1 t1) t2)

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
nullresult (Rmark (ps :: p s) s r) = Cons (Entry ps []) Nil

                                     
-- coerce a term to include extra entries for missing labels
maxr :: R s1 -> R s2 -> Result s1 -> Result s2 -> Result (Merge s1 s2)
maxr r1 r2 Nothing y = fmap (combine (nullresult r1)) y
maxr r1 r2 x  _      = fmap (\x -> combine x (nullresult r2)) x

class (m ~ Merge m m) => Axiom (m :: U) where

instance Axiom '[] where


instance Axiom s => Axiom (a : s) where
--  axiomStar = case axiomStar @s of
--    Refl -> Refl
         
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

-- Functional dependency between the kinds!
-- But we need this dependency to satify the functional dependendency
-- in the HasField class  | s m -> a
class Get (p :: Index s m) where
  getp :: List Entry m -> [String]

instance Get DH where
  getp (Cons (Entry _ v) _ ) = v

instance (Get l) => Get (DT l) where
  getp    (Cons _ xs) = getp @_ @_ @l xs

  
-- Instance for symbols and Dicts
instance (p ~ (Find s m m :: Index s m), Get p) =>
     HasField s (Result m) [String] where
  getField (Just x) = getp @_ @_ @p x
  getField Nothing  = []




-------------------------------------------------------------------------

data R (ss :: U) where
  Rempty :: R Empty
  Rvoid  :: R Empty
  Rseq   :: (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Rstar  :: Axiom s => R s  -> R s
  Rchar  :: (Set.Set Char) -> R Empty
  Rmark  :: (KnownSymbol sym) =>
     proxy sym -> String -> R Empty -> R (Merge (One sym) Empty)

instance TestEquality R where
  Rempty `testEquality` Rempty = Just Refl
  Rvoid  `testEquality` Rvoid  = Just Refl
  Rseq t1 t2 `testEquality` Rseq u1 u2 | Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2 = Just Refl
  Ralt t1 t2 `testEquality` Ralt u1 u2 | Just Refl <- testEquality t1 u1,
    Just Refl <- testEquality t2 u2 = Just Refl
  Rstar t1 `testEquality` Rstar u1 | Just Refl <- testEquality t1 u1 = 
    Just Refl
  Rchar s1 `testEquality` Rchar s2 | s1 == s2 = Just Refl
  Rmark (_ :: p1 s) s1 r1 `testEquality` Rmark (_ :: p2 t) s2 r2 |
    s1 == s2,
    Just Refl <- testEquality (sym @s) (sym @t),
    Just Refl <- r1 `testEquality` r2 = Just Refl
  _ `testEquality` _ = Nothing
  
  
instance Show (R n) where
  show Rempty = "ε"
  show Rvoid  = "∅"   
  show (Rseq r1 r2)   = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = show c
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

char c = Rchar (Set.singleton c)
------------------------------------------------------


r1 = Ralt (char 'a') (char 'b')

r2 = Rmark (sym @"a") "" r1

r4 = Rstar (Rmark (sym @"b") "" (Rseq r1 r1))

r5 = Ralt (Rmark (sym @"b") "" (char 'a')) (Rmark (sym @"b") "" (char 'b'))

r6 = Ralt (Rmark (sym @"a") "" (char 'a')) (Rmark (sym @"b") "" (char 'b'))

r7 = Ralt (Rmark (sym @"b") "" (char 'b')) (Rmark (sym @"b") "" (char 'b'))

r8 = Rmark (sym @"x") "" (Rstar (char 'a'))

-------------------------------------------------------------------------

digit = Rchar (Set.fromList (map (head . show) [0 .. 9]))
dash  = Rchar (Set.fromList ['-','.',' '])

opt_dash = Ralt Rempty dash

phone = Rmark (sym @"phone") ""
   (digit `Rseq` digit `Rseq` digit `Rseq` opt_dash `Rseq`
    digit `Rseq` digit `Rseq` digit `Rseq` digit)

alpha = Rchar (Set.fromList ['a' .. 'z' ])
name  = Rmark (sym @"name") "" alpha

entry = name `Rseq` (Rstar opt_dash) `Rseq` phone

-------------------------------------------------------------------------

match :: Axiom s => R s -> String -> Result s
match r w = extract (deriveWord r w)

deriveWord :: Axiom n => R n -> String -> R n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 


extract :: Axiom s => R s -> Result s
extract Rempty       = empty
extract Rvoid        = zero
extract (Rchar c)    = empty
extract (Rseq r1 r2) = join (extract r1) (extract r2)
extract (Ralt r1 r2) = maxr r1 r2 (extract r1) (extract r2)
extract (Rstar r)    = star r (extract r)
extract (Rmark (ps :: p s) s r) = if nullable r then
  (mark ps s) else (nomark ps)



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
markEmpty (Rmark p w r) | nullable r = (Rmark p w Rempty)
markEmpty (Rmark p w r) = Rmark p w Rvoid
markEmpty (Ralt r1 r2)  = Ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = Rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = Rstar (markEmpty r)
markEmpty r             = r  

deriv :: forall n. Axiom n => R n -> Char -> R n
deriv (Rchar s)    c   = if Set.member c s then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1 =
     ralt (rseq (deriv r1 c) r2) (rseq (markEmpty r1) (deriv r2 c))
deriv (Rstar (r :: R s)) c = 
     (rseq (deriv r c) (Rstar r))
deriv (Rseq r1 r2) c   = rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)

-- smart constructor -- optimizes on construction
-- ignoring r + void, void + r, and r + r
ralt :: forall s1 s2. (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Merge s1 s2)
ralt Rvoid r = r
ralt r Rvoid = r
ralt r1 r2 | Just Refl <- r1 `testEquality` r2 = r1 
ralt r1 r2 = Ralt r1 r2

rseq :: forall s1 s2. (Axiom s1, Axiom s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq Rempty r = r
rseq r Rempty = r
rseq r1 r2    = Rseq r1 r2

----------------------------------------------------
-- Non-indexed regular expression
