-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Definition of natural numbers and operations on them.             --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Basics.Nat where

import Basics.Bool
import Basics.Sing

-- Nat represents natural numbers (starting with 0)
data Nat :: * where
  Zero :: Nat
  Succ :: Nat -> Nat

-- a singletonized Nat data type. You could generate this using the `singletons`
-- package:
--   $(genSingletons [ ''Nat ])
data instance Sing (n :: Nat) where
    SZero :: Sing Zero
    SSucc :: Sing n -> Sing (Succ n)

-- and a convenient type synonym
type SNat (n :: Nat) = Sing n

-- turning a singleton Nat into a normal Nat
fromSing :: SNat n -> Nat
fromSing SZero     = Zero
fromSing (SSucc n) = Succ (fromSing n)

-- We define some natural numbers as they will be useful later on
zero, one, two, three, four, five :: Nat
zero  = Zero
one   = Succ zero
two   = Succ one
three = Succ two
four  = Succ three
five  = Succ four

-- We also want the above numbers to be available at the type level and as
-- singletons. Normally we could use the singletons library to generate all of
-- that but here I'm just writing all these definitions by hand.
type One   = Succ Zero
type Two   = Succ One
type Three = Succ Two
type Four  = Succ Three
type Five  = Succ Four

sZero :: SNat Zero
sZero = SZero

sOne :: SNat One
sOne  = SSucc sZero

sTwo :: SNat Two
sTwo  = SSucc sOne

sThree :: SNat Three
sThree = SSucc sTwo

sFour :: SNat Four
sFour  = SSucc sThree

sFive :: SNat Five
sFive  = SSucc sFour

-- Finally, we need the + operator to add natural numbers. Again, we have to
-- write three definitions.

-- term-level addition
(+) :: Nat -> Nat -> Nat
Zero     + m = m
(Succ n) + m = Succ (n + m)

-- type-level addition
type family (a :: Nat) :+ (b :: Nat) :: Nat
type instance Zero   :+ n = n
type instance Succ n :+ m = Succ (n :+ m)
-- alternatively, we could use a closed type family:
--
--  type family (a :: Nat) :+ (b :: Nat) :: Nat where
--     Zero   :+ n = n
--     Succ n :+ m = Succ (n :+ m)
--
-- but that would be incompatible with GHC 7.6

-- singletons addition
(%:+) :: SNat a -> SNat b -> SNat (a :+ b)
SZero     %:+ m = m
(SSucc n) %:+ m = SSucc (n %:+ m)

infix 6 +, %:+

-- Comparisons
(<) :: Nat -> Nat -> Bool
_      < Zero   = False
Zero   < Succ _ = True
Succ n < Succ m = n < m

(>=) :: Nat -> Nat -> Bool
_      >= Zero   = True
Zero   >= Succ _ = False
Succ m >= Succ n = m >= n

infixl 4 <, >=
