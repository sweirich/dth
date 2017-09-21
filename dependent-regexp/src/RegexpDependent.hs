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

module RegexpDependent(
  -- dictionaries & type safe access
  module OccDict,

  -- regexp type
  R(..),
  -- constructors for regexps
  rempty,rvoid,rseq,ralt,rstar,rchar,rany,rnot,rmark,
  rchars,ropt,rplus,rmarkSing,

  -- regexp matching functions
  Result(..),
  match, matchInit, extractOne, extractAll, contains)  where

import Data.Kind(Type)
import Data.Type.Equality(TestEquality(..),(:~:)(..))
import GHC.Records
import GHC.TypeLits
import Data.Singletons.Prelude
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char
import Data.List(foldl')

import OccDict

-------------------------------------------------------------------------

-- Our GADT, indexed by the set of pattern variables Note that we require all
-- sets, except for the index of Rvoid, to be Wf. (Empty is known to be.)

data R (s :: SM) where
  Rempty :: R Empty
  Rvoid  :: R s
  Rseq   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt   s1 s2)
  Rstar  :: Wf s => R s  -> R (Repeat s)
  Rchar  :: Set Char -> R Empty
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rmark  :: (Wf s) => Sing n -> String -> R s -> R (Merge (One n) s)

-------------------------------------------------------------------------
-- smart constructors
-- we optimize the regular expression whenever we
-- build it.

-- reduces (r,epsilon) (epsilon,r) to just r
-- (r,void) and (void,r) to void
rseq :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq Rempty r2 = r2
rseq r1 Rempty = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2


-- a special case for alternations when both sides capture the
-- same groups. In this case it is cheap to remove voids
-- reduces void|r and r|void to r
raltSame :: Wf s => R s -> R s -> R (Alt s s)
raltSame r1 r2 | isVoid r1 = r2
raltSame r1 r2 | isVoid r2 = r1
raltSame r1 r2 = ralt r1 r2

ralt :: forall s1 s2. (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt s1 s2)
-- we can remove a void on either side if the captured groups are equal
ralt r1 r2 | isVoid r1, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r2
ralt r1 r2 | isVoid r2, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r1
-- some character class combinations
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2 = Ralt r1 r2

-- r** = r*
-- empty* = empty
-- void*  = empty
rstar :: forall s. Wf s => R s -> R (Repeat s)
rstar (Rstar s) = Rstar s
rstar Rempty    = Rempty
rstar r1 | isVoid r1, Just Refl <- testEquality (sing :: Sing s) SNil = Rempty
rstar s         = Rstar s


-- convenience function for marks
-- MUST use explicit type application for 'n' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) => R s -> R (Merge (One n) s)
rmark = rmarkSing (sing :: Sing n)

rmarkSing :: forall n s proxy.
   (KnownSymbol n, Wf s) => proxy n -> R s -> R (Merge (One n) s)
rmarkSing n = Rmark (sing :: Sing n) ""

-- Not the most general type. However, if rvoid appears in a static
-- regexp, it should have index 'Empty'
rvoid :: R Empty
rvoid = Rvoid

rempty :: R Empty
rempty = Rempty

rchar :: Char -> R Empty
rchar = Rchar . Set.singleton

rchars :: [Char] -> R Empty
rchars = Rchar . Set.fromList

rnot :: [Char] -> R Empty
rnot = Rnot . Set.fromList

ropt :: Wf s => R s -> R (Alt Empty s)
ropt = ralt rempty

rplus :: (Wf (Repeat s),Wf s) => R s -> R (Merge s (Repeat s))
rplus r = r `rseq` rstar r

rany :: R Empty
rany = Rany

------------------------------------------------------
isVoid :: R s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- is this the regexp that accepts only the empty string?
-- and doesn't capture any subgroups
isEmpty :: Wf s => R s -> Maybe (s :~: Empty)
isEmpty Rempty        = Just Refl
isEmpty (Rstar r)     | Just Refl <- isEmpty r = Just Refl
isEmpty (Ralt r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty (Rseq r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty _             = Nothing


markResult :: Sing n -> String -> Result (One n)
markResult n s = Just (E s :> Nil)



------------------------------------------------------

type Result (s :: SM) = Maybe (Dict s)

-- combine the two results together, when they both are defined
both :: forall s1 s2. (SingI s1, SingI s2) => Result s1 -> Result s2 -> Result (Merge s1 s2)
both (Just xs) (Just ys) = Just $ combine (sing :: Sing s1) (sing :: Sing s2) xs ys
both _         _         = Nothing

-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
first :: forall s1 s2. (SingI s1, SingI s2) =>
                      Result s1 -> Result s2 -> Result (Alt s1 s2)
first Nothing Nothing  = Nothing
first Nothing (Just y) = Just (glueLeft (sing :: Sing s1) sing y)
first (Just x) _       = Just (glueRight sing x (sing :: Sing s2))


------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: Wf s => R s -> String -> Result s
match r w = extract (foldl' deriv r w)

-- Can the regexp match the empty string?
nullable :: R n -> Bool
nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = False
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable Rany           = False
nullable (Rnot cs)      = False

-- regular expression derivative function
deriv :: forall n. Wf n => R n -> Char -> R n
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c   =
      -- use raltSame instead of ralt for
      -- speed. We know the two sides
      -- capture the same groups here
     raltSame (rseq (deriv r1 c) r2)
              (rseq (markEmpty r1) (deriv r2 c))
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)      c = rseq (deriv r c) (rstar r)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)
deriv (Rchar s)    c   = if Set.member c s then rempty else Rvoid
deriv Rany         c   = rempty
deriv (Rnot s)     c   = if Set.member c s then Rvoid else rempty


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: forall n. Wf n => R n -> R n
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
extract :: forall s. Wf s => R s -> Result s
extract Rempty         = Just Nil
extract (Rchar cs)     = Nothing
extract (Rseq r1 r2)   = both  (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = Just $ nils @s
extract (Rmark n s r)  = withSingI n $ both (markResult n s) (extract r)
extract (Rnot cs)      = Nothing
extract _              = Nothing

----------------------------------------------------------------
-- Additional library functions, more flexible than match


-- | Given r, return the result from the first part
-- of the string that matches m (greedily... consume as much
-- of the string as possible)
matchInit :: Wf s => R s -> String -> (Result s, String)
matchInit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then (extract r, x:xs)
                 else matchInit r' xs
matchInit r "" = (match r "", "")

-- helper for below
pextract :: Wf s => R s -> String -> (Result s, String)
pextract r "" = (match r "", "")
pextract r t  = case matchInit r t of
 (Just r,s)  -> (Just r, s)
 (Nothing,_) -> pextract r (tail t)

-- | Extract groups from the first match of regular expression pat.
extractOne :: Wf s => R s -> String -> Result s
extractOne r s = fst (pextract r s)

-- | Extract groups from all matches of regular expression pat.
extractAll :: Wf s => R s -> String -> [Dict s]
extractAll r s = case pextract r s of
      (Just dict, "")   -> [dict]
      (Just dict, rest) -> dict : extractAll r rest
      (Nothing, _)      -> []

-- | Does this string contain the regular expression anywhere
contains :: Wf s => R s -> String -> Bool
contains r s = case pextract r s of
   (Just r,_)  -> True
   (Nothing,_) -> False

-------------------------------------------------------------------------
-- Show instances for regular expressions

instance Show (Sing (s :: SM)) where
  show r = "[" ++ show' r where
    show' :: Sing (ss :: SM) -> String
    show' SNil = "]"
    show' (SCons (STuple2 sn so) ss) = show sn ++ "," ++ show' ss
instance SingI n => Show (R n) where
  show Rvoid  = "ϕ"
  show Rempty = "ε"
  show (Rseq r1 (Rstar r2)) | show r1 == show r2 = maybeParens r1 ++ "+"
  show (Rseq r1 r2)    = show r1 ++ show r2
  show (Ralt Rempty r) = maybeParens r ++ "?"
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = maybeParens r ++ "*"
  show (Rchar cs)   = if (Set.size cs == 1) then (escape (head (Set.toList cs)))
                   else if cs == (Set.fromList chars_digit) then "\\d"
                   else if cs == (Set.fromList chars_whitespace) then "\\s"
                   else if cs == (Set.fromList chars_word) then "\\w"
                   else "[" ++ concatMap escape (Set.toList cs) ++ "]"
     where
       chars_whitespace = " \t\n\r\f\v"
       chars_digit      = ['0' .. '9']
       chars_word       = ('_':['a' .. 'z']++['A' .. 'Z']++['0' .. '9'])
  show (Rmark pn w r)  = "(?P<" ++ show pn ++ ">" ++ show r ++ ")"
  show Rany = "."
  show (Rnot cs) = "[^" ++ concatMap escape (Set.toList cs) ++ "]"

-- escape special characters
escape :: Char -> String
escape c  = if c `elem` specials then "\\" ++ [c] else [c] where
       specials         = ".[{}()\\*+?|^$"

maybeParens :: SingI s => R s -> String
maybeParens r = if needsParens r then "(" ++ show r ++ ")" else show r

needsParens :: R s -> Bool
needsParens Rvoid = False
needsParens Rempty = False
needsParens (Rseq r1 r2) = True
needsParens (Ralt r1 r2) = True
needsParens (Rstar r)    = True
needsParens (Rchar cs)   = False
needsParens (Rany)       = False
needsParens (Rnot _)     = False
needsParens (Rmark _ _ _) = False
