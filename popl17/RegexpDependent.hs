{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables, InstanceSigs, TypeApplications #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses, ConstraintKinds #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fprint-expanded-synonyms #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module RegexpDependent (module Regexp, match, deriv, extract,
                        extractOne, extractAll, contains) where

import RegexpOcc as Regexp

import Data.Type.Equality(TestEquality(..),(:~:)(..))
import Data.Singletons.Prelude(SingI(..),Sing(SNil,SCons,STuple2))
import Data.Singletons.TypeLits (Sing(SSym),Symbol(..),KnownSymbol(..),symbolVal)


import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

import Data.List(foldl')

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
--deriv (Rseq r1 r2) c | onlyEmpty r1 =
--     rseq r1 (deriv r2 c)
deriv (Rseq r1 r2) c   = 
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
markEmpty (Rstar r)     = rstar (markEmpty r) -- different!
markEmpty Rempty        = rempty
markEmpty Rvoid         = Rvoid
markEmpty (Rchar c)     = Rvoid
markEmpty (Rnot  c)     = Rvoid
markEmpty Rany          = Rvoid

-- note: if r is nullable then markEmpty returns rempty


-- | Extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: forall s. Wf s => R s -> Result s
extract Rempty         = Just Nil
extract (Rchar cs)     = Nothing
extract (Rseq r1 r2)   = both  (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = Just $ nils @s
extract (Rmark n s r)  = both (markResult n s) (extract r) 
extract (Rnot cs)      = Nothing
extract _              = Nothing

----------------------------------------------------------------
-- | Given r, return the result from the first part 
-- of the string that matches m (greedily... consume as much
-- of the string as possible)
matchInit :: Wf s => R s -> String -> (Result s, String)
matchInit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then (extract r, x:xs)
                 else matchInit r' xs
matchInit r "" = (match r "", "")


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

contains :: Wf s => R s -> String -> Bool
contains r s = case pextract r s of
   (Just r,_)  -> True
   (Nothing,_) -> False

-------------------------------------------------------------------------
-- Show instances

instance Show (Sing (s :: U)) where
  show r = "[" ++ show' r where
    show' :: Sing (ss :: U) -> String
    show' SNil = "]"
    show' (SCons (STuple2 sn so) ss) = show sn ++ "," ++ show' ss
instance SingI n => Show (R n) where
  show Rvoid  = "∅:" ++ show (sing :: Sing n)
  show Rempty = "ε"
  show (Rseq r1 (Rstar r2)) | show r1 == show r2 = maybeParens r1 ++ "+"
  show (Rseq r1 r2)    = show r1 ++ show r2
  show (Ralt Rempty r) = maybeParens r ++ "?"
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = maybeParens r ++ "*"
  show (Rchar cs) | Set.size cs == 1 = (Set.toList cs)
                  | cs == Set.fromList ['0' .. '9']  = "\\d"
                  | cs == Set.fromList " \t\n\r\f\v" = "\\s"
                  | otherwise = "[" ++ Set.toList cs ++ "]"
  show (Rmark pn w r)  = "(?P<" ++ show pn ++ ">" ++ show r ++ ")"
  show Rany = "."
  show (Rnot cs) = "[^" ++ Set.toList cs ++ "]"

-- TODO: escape special characters

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

   
