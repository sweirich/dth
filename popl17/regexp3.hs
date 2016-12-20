{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses #-}

{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}

{-# LANGUAGE TemplateHaskell #-}
import Language.Haskell.TH hiding (Type, match)

-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using Partial Derivatives

-- So far, inefficient version only
-- Type system keeps track of the named matches that can be
-- produced by the regexp
-- Doesn't allow marking inside of Kleene-*

import Data.Kind (Type)

import qualified Data.Char as Char
import GHC.TypeLits
import Data.Singletons.TH 
import Data.Singletons.Prelude
import Data.Singletons.TypeLits

import Data.Typeable

import Unsafe.Coerce

-- For FinList
import qualified Data.Set as Set

import Kleene


-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- Singleton symbol
sym :: forall s. KnownSymbol s => Sing (s :: Symbol)
sym = sing @Symbol @s

data R k (ss :: k) where
  Rempty :: R k (Empty k)
  Rvoid  :: R k (Empty k)
  Rseq   :: (Axiom s1, Axiom s2) => R k s1 -> R k s2 -> R k (Sequ s1 s2)
  Ralt   :: (Axiom s1, Axiom s2) => R k s1 -> R k s2 -> R k (Alt s1 s2)
  Rstar  :: (Axiom s) => R k s  -> R k (Star s)
  Rchar  :: (Set.Set Char) -> R k (Empty k)
  Rmark  :: (Axiom (Mark k s)), KnownSymbol s) =>
     proxy s -> String -> R k (Empty k) -> R k (Mark s)

{-
instance IKleene R where
  type Data R = String
  iempty = Rempty
  ivoid  = Rvoid
  isequ  = Rseq
  ialt   = Ralt
  istar  = Rstar
  imark  = Rmark
-}

                                    
instance Show (R k n) where
  show Rempty = "ε"
  show Rvoid  = "∅"   
  show (Rseq r1 r2)   = show r1 ++ show r2
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = "(" ++ show r  ++ ")*"
  show (Rchar c) = show c
  show (Rmark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

char :: Char -> R k (Empty k)
char c = Rchar (Set.singleton c)

r1 :: R k (Empty k)
r1 = Ralt (char 'a') (char 'b')

r2 :: R k (Mark "a")
r2 = Rmark (sym @"a") "" r1

--r4 :: R '[ '("b", [String]) ]
r4 = Rstar (Rmark (sym @"b") "" (Rseq r1 r1))

--r5 :: R S '[ '("b", 'Fin 1) ]
r5 = Ralt (Rmark (sym @"b") "" (char 'a')) (Rmark (sym @"b") "" (char 'b'))

-- r6 :: R S ('[ '("a", Fin 1), '("b", Fin 1) ])
r6 = Ralt (Rmark (sym @"a") "" (char 'a')) (Rmark (sym @"b") "" (char 'b'))

-- r7 :: R '[ '("b", 'Fin 1) ]
r7 = Ralt (Rmark (sym @"b") "" (char 'b')) (Rmark (sym @"b") "" (char 'b'))

-------------------------------------------------------------------------

digit = Rchar (Set.fromList (map (head . show) [0 .. 9]))
dash  = Rchar (Set.fromList ['-','.',' '])
opt_dash :: R k (Empty k)
opt_dash = Ralt Rempty dash

phone :: R k (Mark "phone")
phone = Rmark (sym @"phone") ""
   (digit `Rseq` digit `Rseq` digit `Rseq` opt_dash `Rseq`
    digit `Rseq` digit `Rseq` digit `Rseq` digit)

alpha = Rchar (Set.fromList ['a' .. 'z' ])
name  = Rmark (sym @"name") "" alpha

entry = name `Rseq` (Rstar opt_dash) `Rseq` phone

-------------------------------------------------------------------------
-------------------------------------------------------------------------

match :: (Axiom (m :: k), IKleene t) => R k m -> String -> t m
match r w = extract (deriveWord r w)

deriveWord :: Axiom n => R k n -> String -> R k n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 


extract :: forall k t m . (Axiom k, IKleene t) => R k m -> t m
extract Rempty       = iempty
extract Rvoid        = izero
extract (Rchar c)    = iempty
extract (Rseq r1 r2) = isequ (extract r1) (extract r2)
extract (Ralt r1 r2) = ialt (extract r1) (extract r2)
extract (Rstar r)      = istar r
extract (Rmark (ps :: p s) s r) = if nullable r then
  (imark ps s) else
     case axiomAltIdLeft @k @(Mark s) of
        Refl -> iweak @_ @t @_ @(Mark s) izero


-- Can the regexp match the empty string? 
nullable :: R k n -> Bool
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
markEmpty :: R k n -> R k n
markEmpty (Rmark p w r) | nullable r = (Rmark p w Rempty)
markEmpty (Rmark p w r) = Rmark p w Rvoid
markEmpty (Ralt r1 r2)  = Ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = Rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = Rstar (markEmpty r)
markEmpty r             = r  

deriv :: forall k n. (Axiom (n :: k)) => R k n -> Char -> R k n
deriv (Rchar s)    c   = if Set.member c s then Rempty else Rvoid
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c | nullable r1, Refl <- axiomAltIdem @k @n = 
     Ralt (Rseq (deriv r1 c) r2) (Rseq (markEmpty r1) (deriv r2 c))
deriv (Rstar (r :: R k s)) c | Refl <- axiomStar @k @s =
     (Rseq (deriv r c) (Rstar r))
deriv (Rseq r1 r2) c   = Rseq (deriv r1 c) r2
deriv (Ralt r1 r2) c   = Ralt (deriv r1 c) (deriv r2 c)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv @k r c)


----------------------------------------------------
-- Non-indexed regular expression
{-
instance Lift a => Lift (Set a) where
  lift set = appE (varE `Set.fromList ) (lift (Set.toList set))
 
instance Lift RegExp where
  -- lift :: RegExp -> Q Exp
  lift (Char cs)     = apply `Char  [lift cs]
  lift (Alt r1 r2)   = apply `Alt   (map lift [r1, r2])
  lift (Seq r1 r2)   = apply `Seq   (map lift [r1, r2])
  lift (Star r1)     = apply `Star  (map lift [r1])
  lift Empty         = apply `Empty []
  lift Zero          = apply `Zero  []
  lift (Var vars)    = foldl1 appE $ map (varE . mkName) (words vars)
 
apply :: Name -> [Q Exp] -> Q Exp
apply n = foldl appE (conE n)

regex :: QuasiQuoter
regex = QuasiQuoter {
    quoteExp  = compile
  , quotePat  = notHandled "patterns"
  , quoteType = notHandled "types"
  , quoteDec  = notHandled "declarations"
  }
  where notHandled things = error $
          things ++ " are not handled by the regex quasiquoter."
 
compile :: String -> Q Exp
compile s =
  case P.parse regexParser "" s of
    Left  err    -> fail (show err)
    Right regexp -> [e| regexp |]

-}
