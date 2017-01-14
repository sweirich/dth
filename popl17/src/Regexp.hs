{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, 
    PolyKinds #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- Based on:
-- Sulzmann & Lu
-- "Regular Expression SubMatching Using (Partial) Derivatives"
-- Note: For simplicity, this implementation uses the Brzowozki
-- derivatives, which are Posix based and backtracking.

-- See RegexpExample.hs for this library in action.

module Regexp where

import Data.Proxy
import GHC.TypeLits

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

import Data.List(foldl')

type Result = Maybe Dict

data Entry where
   Entry :: String -> [String] -> Entry

-- A list of entries, where each entry is an association
-- between a name, and the list of strings for that submatch.   
data Dict where
   Nil  :: Dict 
   (:>) :: Entry -> Dict -> Dict

infixr 5 :>


------

combine :: Dict -> Dict -> Dict
combine Nil Nil = Nil
combine Nil b   = b
combine b   Nil = b
combine (e1@(Entry n1 ss1) :> t1) (e2@(Entry n2 ss2) :> t2) =
  case (n1 == n2) of
   True ->  Entry n1 (ss1 ++ ss2) :> combine t1 t2     
   False -> case n1 <= n2 of
     True  -> e1 :> combine t1 (e2 :> t2)
     False ->  e2 :> combine (e1 :> t1) t2 

-- A "default" Dict.
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
nils :: Dict
nils = Nil

-- | Combine two results together, combining their lists (if present)
-- If either result fails, return Nothing
both :: Result -> Result -> Result 
both (Just xs) (Just ys) = Just $ combine xs ys
both _         _         = Nothing


-- | Combine two results together, taking the first successful one
first ::  Result -> Result -> Result 
first Nothing  Nothing  = Nothing                      
first Nothing  (Just y) = Just $ nils `combine` y
first (Just x) _        = Just $ x `combine` nils



-------------------------------------------------------------------------

-- access a name from the dictionary.
-- If the name is not present, return the empty list

getFieldD :: forall a. KnownSymbol a => Dict -> [String]
getFieldD (Entry t ss :> r) | symbolVal (Proxy :: Proxy a) == t    = ss
                           | otherwise = getFieldD @a r
getFieldD Nil                          = []

getField ::  forall a. KnownSymbol a => Maybe Dict -> [String]
getField (Just d) = getFieldD @a d
getField Nothing  = []
------------------------------------------------------
-- Our ADT for regular expressions
data R where
  Rempty :: R   
  Rvoid  :: R          -- always fails, set can be anything 
  Rseq   :: R -> R -> R
  Ralt   :: R -> R -> R
  Rstar  :: R -> R
  Rchar  :: Set Char -> R  -- must be nonempty set
  Rany   :: R
  Rnot   :: Set Char -> R
  Rmark  :: String -> String -> R -> R


-------------------------------------------------------------------------
-- Smart constructors for regular expressions
--
-- We optimize the regular expression whenever we build it. These
-- optimizations are necessary for efficient execution of the regular
-- expression matcher.

-- reduces (r,epsilon) (epsilon,r) to r
-- (r,void) and (void,r) to void
rseq :: R -> R -> R
rseq r1 r2 | isEmpty r1 = r2
rseq r1 r2 | isEmpty r2 = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2

-- Construct an alternative
ralt :: R -> R -> R
ralt r1 r2 | isVoid r1 = r2  
ralt r1 r2 | isVoid r2 = r1
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2                 = Ralt r1 r2

-- convenience function for marks
rmark :: forall a. KnownSymbol (a :: Symbol) => R -> R
rmark = rmarkSing (Proxy :: Proxy a)
      
rmarkSing :: forall n proxy. KnownSymbol (n :: Symbol) => proxy n -> R -> R 
rmarkSing n r = rmarkInternal (symbolVal n) "" r

rmarkInternal :: String -> String -> R -> R 
rmarkInternal n w r | isVoid r = Rvoid
rmarkInternal n w r = Rmark n w r

-- r** ~> r*
-- empty* ~> empty
rstar :: R -> R
rstar (Rstar s) = Rstar s
rstar r | isEmpty r = rempty
rstar s = Rstar s

-- this needs to have this type to make inference work
rvoid :: R 
rvoid = Rvoid

-- convenience function for empty string
rempty :: R
rempty = Rempty

-- convenience function for single characters
rchar :: Char -> R 
rchar c = Rchar (Set.singleton c)

-- completeness
rchars :: [Char] -> R
rchars = Rchar . Set.fromList

rnot :: [Char] -> R 
rnot = Rnot . Set.fromList

ropt :: R -> R
ropt = ralt rempty

rplus :: R -> R 
rplus r = r `rseq` rstar r

rany :: R
rany = Rany


------------------------------------------------------
-- is this the regexp that always fails?
isVoid :: R -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rstar r)      = False
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- is this the regexp that accepts only the empty string?
-- and DOES NOT include any marks?
isEmpty :: R -> Bool
isEmpty Rempty         = True
isEmpty (Rseq r1 r2)   = isEmpty r1 && isEmpty r2
isEmpty (Ralt r1 r2)   = isEmpty r1 && isEmpty r2
isEmpty (Rstar r)      = isEmpty r
isEmpty _ = False

------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: R -> String -> Result 
match r w = extract (foldl' deriv r w)

-- | Extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: R -> Result
extract Rempty         = Just Nil
extract (Rchar cs)     = Nothing
extract (Rseq r1 r2)   = both  (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = Just $ nils
extract (Rmark n s r)  = both mark (extract r) where
      mark = Just (Entry n [reverse s] :> Nil)
extract _              = Nothing

-- Can the regexp match the empty string? 
nullable :: R -> Bool
nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = False
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable (Rany)         = False
nullable (Rnot cs)      = False

-- regular expression derivative function
deriv :: R -> Char -> R
deriv Rempty        c = Rvoid
deriv (Rseq r1 r2)  c =
     ralt (rseq (deriv r1 c) r2) 
          (rseq (markEmpty r1) (deriv r2 c))
deriv (Ralt r1 r2)  c = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)     c = rseq (deriv r c) (rstar r)
deriv Rvoid         c = Rvoid
deriv (Rmark n w r) c = Rmark n (c : w) (deriv r c)
deriv (Rchar s)     c = if Set.member c s then rempty else Rvoid
deriv Rany  c         = rempty
deriv (Rnot s)      c = if Set.member c s then Rvoid else rempty

-- Create a regexp that *only* matches the empty string
-- (if it matches anything), but retains all captured strings
markEmpty :: R -> R 
markEmpty (Rmark p w r) = Rmark p w (markEmpty r)
markEmpty (Ralt r1 r2)  = ralt (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = rseq (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = rstar (markEmpty r)
markEmpty Rempty        = rempty
markEmpty Rvoid         = Rvoid
markEmpty (Rchar s)     = Rvoid
markEmpty Rany          = Rvoid
markEmpty (Rnot cs)     = Rvoid


-------------------------------------------------------------------------
-- Show instances

instance Show Entry where
  show (Entry sn ss) = show sn ++ "=" ++ show ss where

instance Show Dict  where
  show xs = "{" ++ show' xs where
    show' :: Dict -> String
    show' Nil = "}"
    show' (e :> Nil) = show e ++ "}"
    show' (e :> xs)  = show e ++ "," ++ show' xs

instance Show R  where
  show Rempty = "ε"                                            
  show Rvoid  = "∅"   
  show (Rseq r1 r2) = show r1 ++ show r2
  show (Ralt r1 r2) = show r1 ++ "|" ++ show r2
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar cs) = if (Set.size cs == 1) then (Set.toList cs)
                   else if cs == (Set.fromList ['0' .. '9']) then "\\d"
                   else if cs == (Set.fromList [' ', '-', '.']) then "\\w"
                   else "[" ++ Set.toList cs ++ "]"
  show (Rmark n w r)  = "(?P<" ++ n ++ ":" ++ w ++ ">" ++ show r ++ ")"
  show (Rany) = "."
  show (Rnot cs) = "[^" ++ show cs ++ "]"

-------------------------------------------------------------------------
instance Monoid Dict where
  mempty  = Nil
  mappend = combine 
 

----------------------------------------------------------------
-- | Given r, return the result from the first part 
-- of the string that matches m (greedily... consume as much
-- of the string as possible)
matchInit :: R -> String -> (Result, String)
matchInit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then (extract r, x:xs)
                 else matchInit r' xs
matchInit r "" = (match r "", "")


pextract :: R -> String -> (Result, String)
pextract r "" = (match r "", "")
pextract r t  = case matchInit r t of
 (Just r,s)  -> (Just r, s)
 (Nothing,_) -> pextract r (tail t)

-- | Extract groups from the first match of regular expression pat.
extractOne :: R -> String -> Result 
extractOne r s = fst (pextract r s)

-- | Extract groups from all matches of regular expression pat.
extractAll :: R -> String -> [Dict]
extractAll r s = case pextract r s of
      (Just dict, "")   -> [dict]
      (Just dict, rest) -> dict : extractAll r rest
      (Nothing, _)      -> []

contains :: R -> String -> Bool
contains r s = case (pextract r s) of
   (Just r,_)  -> True
   (Nothing,_) -> False
