{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs,
    ScopedTypeVariables, InstanceSigs, TypeApplications,
    TypeFamilyDependencies,
    TemplateHaskell, AllowAmbiguousTypes,
    FlexibleContexts, TypeSynonymInstances, FlexibleInstances,
    MultiParamTypeClasses, FunctionalDependencies #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fprint-expanded-synonyms #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module implements the regular expression type and several operations
-- for matching regular expressions against strings
module RegexpDependent(

  -- regexp type
  RE(..),

  -- functions to construct regexps
  rempty, rvoid,rseq,ralt,ropt,rstar,rplus,rchar,rchars,
  rany,rnot,rmark,rmarkSing,

  -- occurrence dictionary
  module OccDict,

  -- regexp matching functions
  match, matchInit, extractOne, extractAll, contains)  where

import Data.Kind(Type)
import Data.Type.Equality(TestEquality(..),(:~:)(..))
import GHC.Records
import GHC.TypeLits
import Data.Singletons.Prelude

import Data.List(foldl')
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char
import Data.DList (DList)
import qualified Data.DList as DList

import Data.Monoid((<>))

import OccDict

-------------------------------------------------------------------------

-- Our GADT, indexed by the set of pattern variables Note that we require all
-- sets, except for the index of Rvoid, to be Wf. (Empty is known to be.)

-- | Regular expressions, indexed by a symbol occurrence map that describes
-- potential capture groups
data RE (s :: OccMap) where
  Rempty :: RE Empty
  Rvoid  :: RE s
  Rseq   :: (Wf s1, Wf s2) => RE s1 -> RE s2 -> RE (Merge s1 s2)
  Ralt   :: (Wf s1, Wf s2) => RE s1 -> RE s2 -> RE (Alt   s1 s2)
  Rstar  :: Wf s => RE s  -> RE (Repeat s)
  Rchar  :: Set Char -> RE Empty
  Rany   :: RE Empty
  Rnot   :: Set Char -> RE Empty
  Rmark  :: (Wf s) => Sing n -> DList Char -> RE s -> RE (Merge (One n) s)

-------------------------------------------------------------------------
-- smart constructors
-- we optimize the regular expression whenever we build it.


-- | Sequence (r1 r2)
rseq :: (Wf s1, Wf s2) => RE s1 -> RE s2 -> RE (Merge s1 s2)
rseq Rempty r2 = r2               -- reduces (r,epsilon) (epsilon,r) to just r
rseq r1 Rempty = r1
rseq r1 r2 | isVoid r1 = Rvoid    -- (r,void) and (void,r) to void
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2


-- a special case for alternations when both sides capture the
-- same groups. In this case it is cheap to remove voids
-- reduces void|r and r|void to r
raltSame :: Wf s => RE s -> RE s -> RE (Alt s s)
raltSame r1 r2 | isVoid r1 = r2
raltSame r1 r2 | isVoid r2 = r1
raltSame r1 r2 = ralt r1 r2

-- | Alternation (r1|r2)
ralt :: forall s1 s2. (Wf s1, Wf s2) => RE s1 -> RE s2 -> RE (Alt s1 s2)
-- we can remove a void on either side if the captured groups are equal
ralt r1 r2 | isVoid r1, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r2
ralt r1 r2 | isVoid r2, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r1
-- some character class simplifications
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2 = Ralt r1 r2



-- | Kleene star  r*
rstar :: forall s. Wf s => RE s -> RE (Repeat s)
rstar (Rstar r) = Rstar r   -- r** = r*
rstar Rempty    = Rempty    -- empty* = empty
rstar r1 | isVoid r1,       -- void*  = empty
           Just Refl <- testEquality (sing :: Sing s) SNil = Rempty
rstar r         = Rstar r


-- convenience function for marks
-- | Capture group marking (?P<n> r)
-- MUST use explicit type application for 'n' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) => RE s -> RE (Merge (One n) s)
rmark = rmarkSing (sing :: Sing n)

-- Another version, use a proxy instead of explicit type application
-- | Capture group marking (?P<n> r)
-- Can specify n via proxy or singleton
rmarkSing :: (KnownSymbol n, Wf s) => proxy n -> RE s -> RE (Merge (One n) s)
rmarkSing n = Rmark (singByProxy n) DList.empty

-- Not the most general type. However, if rvoid appears in a static
-- regexp, it should have index 'Empty'
-- | Matches nothing (and captures nothing)
rvoid :: RE Empty
rvoid = Rvoid

-- | Only matches the empty string (ε)
rempty :: RE Empty
rempty = Rempty

-- | Matches a specific character
rchar :: Char -> RE Empty
rchar = Rchar . Set.singleton

-- | Matches any single character (.)
rany :: RE Empty
rany = Rany

-- | Matches any character in a set [a-z]
rchars :: [Char] -> RE Empty
rchars = Rchar . Set.fromList

-- | Matches any character not in the set  [^a]
rnot :: [Char] -> RE Empty
rnot = Rnot . Set.fromList

-- | Optional r?
ropt :: Wf s => RE s -> RE (Alt Empty s)
ropt = ralt rempty

-- | Matches one or more  r+
rplus :: (Wf (Repeat s),Wf s) => RE s -> RE (Merge s (Repeat s))
rplus r = r `rseq` rstar r


------------------------------------------------------
isVoid :: RE s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- is this the regexp that accepts only the empty string?
-- and doesn't capture any subgroups
isEmpty :: Wf s => RE s -> Maybe (s :~: Empty)
isEmpty Rempty        = Just Refl
isEmpty (Rstar r)     | Just Refl <- isEmpty r = Just Refl
isEmpty (Ralt r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty (Rseq r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty _             = Nothing

------------------------------------------------------
-- matching using derivatives

-- | Determine if the provided string matches the regular expression
-- If successful, return captured groups in dictionary
match :: Wf s => RE s -> String -> Maybe (Dict s)
match r w = extract (foldl' deriv r w)


-- We use a variant of Brzozowski derivatives for the implementation
-- of the match function.
-- This implementation is based on "Martin Sulzmann, Kenny Zhuo Ming Lu.
-- Regular expression sub-matching using partial derivatives."

-- The general idea is to compute the derivative for each letter, storing
-- capture groups in the regexp derivative. If the final derivative
-- matches, then extract the dictionary.

-- regular expression derivative function
deriv :: forall n. Wf n => RE n -> Char -> RE n
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c   =
      -- use raltSame instead of ralt for speed.
      -- We know the two sides capture the same groups
     raltSame (rseq (deriv r1 c) r2)
              (rseq (markEmpty r1) (deriv r2 c))
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)      c = rseq (deriv r c) (rstar r)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w <> (DList.singleton c)) (deriv r c)
deriv (Rchar s)    c   = if Set.member c s then rempty else Rvoid
deriv Rany         c   = rempty
deriv (Rnot s)     c   = if Set.member c s then Rvoid else rempty


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: forall n. Wf n => RE n -> RE n
markEmpty (Rmark p w r) = Rmark p w (markEmpty r)
markEmpty (Ralt r1 r2)  = ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = rstar (markEmpty r)
markEmpty Rempty        = rempty
markEmpty Rvoid         = Rvoid
markEmpty (Rchar c)     = Rvoid
markEmpty (Rnot  c)     = Rvoid
markEmpty Rany          = Rvoid




-- | Extract the result from the regular expression
-- NB: even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: forall s. Wf s => RE s -> Maybe (Dict s)
extract Rempty         = Just Nil
extract (Rchar cs)     = Nothing
extract (Rseq r1 r2)   = both  (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = Just $ nils @s
extract (Rmark n s r)  = withSingI n $ both (markResult n s) (extract r)
extract (Rnot cs)      = Nothing
extract _              = Nothing


------------------------------------------------------
-- helper functions for extract

-- combine the two results together, when they both are defined
both :: forall s1 s2. (SingI s1, SingI s2) => Maybe (Dict s1) -> Maybe (Dict s2) -> Maybe (Dict (Merge s1 s2))
both (Just xs) (Just ys) = Just $ combine (sing :: Sing s1) (sing :: Sing s2) xs ys
both _         _         = Nothing

-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
first :: forall s1 s2. (SingI s1, SingI s2) =>
                      Maybe (Dict s1) -> Maybe (Dict s2) -> Maybe (Dict (Alt s1 s2))
first Nothing Nothing  = Nothing
first Nothing (Just y) = Just (glueLeft (sing :: Sing s1) sing y)
first (Just x) _       = Just (glueRight sing x (sing :: Sing s2))

-- Capture a single value marked by `n`
markResult :: Sing n -> DList Char -> Maybe (Dict (One n))
markResult n s = Just (E (DList.toList s) :> Nil)

----------------------------------------------------------------
-- Additional library functions, more flexible than match

-- | Given r, return the result from the first part
-- of the string that matches m (greedily... consume as much
-- of the string as possible)
matchInit :: Wf s => RE s -> String -> (Maybe (Dict s), String)
matchInit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then (extract r, x:xs)
                 else matchInit r' xs
matchInit r "" = (match r "", "")

-- helper for below
pextract :: Wf s => RE s -> String -> (Maybe (Dict s), String)
pextract r "" = (match r "", "")
pextract r t  = case matchInit r t of
 (Just r,s)  -> (Just r, s)
 (Nothing,_) -> pextract r (tail t)

-- | Extract groups from the first match of regular expression
extractOne :: Wf s => RE s -> String -> Maybe (Dict s)
extractOne r s = fst (pextract r s)

-- | Extract groups from all matches of regular expression
extractAll :: Wf s => RE s -> String -> [Dict s]
extractAll r s = case pextract r s of
      (Just dict, "")   -> [dict]
      (Just dict, rest) -> dict : extractAll r rest
      (Nothing, _)      -> []

-- | Does this string contain the regular expression anywhere
contains :: Wf s => RE s -> String -> Bool
contains r s = case pextract r s of
   (Just r,_)  -> True
   (Nothing,_) -> False

-------------------------------------------------------------------------
-- Show instances for regular expressions

-- Repetition takes precedence over concatenation,
-- which in turn takes precedence over alternation.

-- top 10
-- r*+   7
-- r1r2  6
-- r1|r2 5

instance SingI n => Show (RE n) where
  showsPrec i Rvoid  = showString "ϕ"
  showsPrec i Rempty = showString "ε"
  showsPrec i (Rseq r1 (Rstar r2)) |
    show r1 == show r2 =
      showParen (i > 7) $ showsPrec 7 r1 . showString "+"
  showsPrec i (Rseq r1 r2)    =
    showParen (i > 6) $
    showsPrec 6 r1 . showsPrec 6 r2
  showsPrec i (Ralt Rempty r) =
    showParen (i > 7) $
    showsPrec 7 r . showString "?"
  showsPrec i (Ralt r1 r2) =
    showParen (i > 5) $
    showsPrec 5 r1 . showString "|" . showsPrec 5 r2
  showsPrec i (Rstar r)    =
    showParen (i > 7) $
    showsPrec 7 r . showString "*"
  showsPrec i (Rchar cs)   = showString $
    if (Set.size cs == 1) then (escape (head (Set.toList cs)))
    else if cs == (Set.fromList chars_digit) then "\\d"
    else if cs == (Set.fromList chars_whitespace) then "\\s"
    else if cs == (Set.fromList chars_word) then "\\w"
    else "[" ++ concatMap escape (Set.toList cs) ++ "]"
     where
       chars_whitespace = " \t\n\r\f\v"
       chars_digit      = ['0' .. '9']
       chars_word       = ('_':['a' .. 'z']++['A' .. 'Z']++['0' .. '9'])
  showsPrec i (Rmark pn w r)  =
    showString "(?P<" . showString (showSym pn) . showString ">" .
    showsPrec 0 r . showString ")"
  showsPrec i Rany = showString "."
  showsPrec i (Rnot cs) = showString $ "[^" ++ concatMap escape (Set.toList cs) ++ "]"

-- escape special characters
escape :: Char -> String
escape c  = if c `elem` specials then "\\" ++ [c] else [c] where
       specials         = ".[{}()\\*+?|^$"

{-
maybeParens :: SingI s => RE s -> String
maybeParens r = if needsParens r then "(" ++ show r ++ ")" else show r

needsParens :: RE s -> Bool
needsParens Rvoid = False
needsParens Rempty = False
needsParens (Rseq r1 r2) = True
needsParens (Ralt r1 r2) = True
needsParens (Rstar r)    = True
needsParens (Rchar cs)   = False
needsParens (Rany)       = False
needsParens (Rnot _)     = False
needsParens (Rmark _ _ _) = False
-}
