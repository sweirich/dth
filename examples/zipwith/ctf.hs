{-# LANGUAGE TypeFamilies, ExplicitForAll, DataKinds, GADTs, MultiParamTypeClasses,
             FlexibleInstances, FlexibleContexts, ScopedTypeVariables, 
             FunctionalDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- Example of zipWith from closed type families paper
-- Richard A. Eisenberg, Dimitrios Vytiniotis, Simon Peyton Jones, and Stephanie Weirich. 
-- Closed type families with overlapping equations. POPL 2014

{-

The tricky part of this problem is that we need to generate functions following the pattern

(a -> b ) -> [a] -> [b] 
(a -> b -> c) -> [a] -> [b] -> [c]
(a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]

How do we unify these types? 

-}


module Zip4 where

import Prelude hiding (zipWith)

import Control.Applicative

data Nat = Zero | Succ Nat

zap :: [a -> b] -> [a] -> [b]
zap [] [] = []
zap (f:fs)(x:xs) = f x : zap fs xs
zap _ [] = []
zap [] _ = []

-- Evidence that a function has at least a certain number of arguments
data NumArgs :: Nat -> * -> * where
  NAZero :: NumArgs Zero a
  NASucc :: NumArgs n b -> NumArgs (Succ n) (a -> b)

-- Map the type constructor [] over the types of arguments and return value of
-- a function
type family Listify (n :: Nat) (arrows :: *) :: * where
  Listify (Succ n) (a -> b) = [a] -> Listify n b
  Listify Zero a = [a]


-- Variable arity application of a list of functions to lists of arguments
-- with explicit evidence that the number of arguments is valid
appN :: NumArgs n a -> [a] -> Listify n a
appN NAZero fs = fs
appN (NASucc na) fs = \x -> appN na (fs `zap` x)

zipWithN :: NumArgs n a -> a -> Listify n a
zipWithN n f = appN n (pure f)


example1 = zipWithN (NASucc NAZero)          not [False,True]
example2 = zipWithN (NASucc (NASucc NAZero)) (+) [1,3] [4,5]

---------------------------------------------------------
---------------------------------------------------------

-- Count the number of arguments of a function
type family CountArgs (f :: *) :: Nat where
  CountArgs (a -> b) = Succ (CountArgs b)
  CountArgs result = Zero

-- Use type classes to automatically infer that evidence
class CNumArgs (numArgs :: Nat) (arrows :: *) where
  getNA :: NumArgs numArgs arrows
instance CNumArgs Zero a where
  getNA = NAZero
instance CNumArgs n b => CNumArgs (Succ n) (a -> b) where
  getNA = NASucc getNA

-- Variable arity zipWith, inferring the number of arguments and using
-- implicit evidence of the argument count.
-- Calling this requires having a concrete return type of the function to
-- be applied; if it's abstract, we can't know how many arguments the function
-- has. So, zipWith (+) ... won't work unless (+) is specialized.
zipWith :: forall f. CNumArgs (CountArgs f) f => f -> Listify (CountArgs f) f
zipWith f = zipWithN (getNA :: NumArgs (CountArgs f) f) f

example3 = zipWith (&&) [False, True, False] [True, True, False]
example4 = zipWith ((+) :: Int -> Int -> Int) [1,2,3] [4,5,6]

-- note: adding a return type annotation doesn't help
-- example4 :: [Int]
-- example4 = zipWith (+) [1,2,3] [4,5,6]

splotch :: Int -> Char -> Double -> String
splotch a b c = (show a) ++ (show b) ++ (show c)

example5 = zipWith splotch [1,2,3] ['a','b','c'] [3.14, 2.1728, 1.01001]

-----------------------------------------------------
-- Backwards version, no nats necessary

type family Delistify (arrows :: *) :: * where
  Delistify [a] = a
  Delistify ([a] -> b) = a -> Delistify b

appN' :: DNumArgs a -> [Delistify a] -> a
appN' DZero      fs = fs
appN' (DSucc dn) fs = \x -> (appN' dn (fs `zap` x))

data DNumArgs a where
  DZero :: DNumArgs [a]
  DSucc :: DNumArgs b -> DNumArgs ([a] -> b)
  
zipWithN' :: DNumArgs a -> Delistify a -> a 
zipWithN' n f = appN' n (repeat f)

class CDNumArgs a where
  na :: DNumArgs a 
instance CDNumArgs [a] where
  na = DZero
instance CDNumArgs b => CDNumArgs ([a] -> b) where
  na = DSucc na

zipWith' :: CDNumArgs a => Delistify a -> a 
zipWith' f = zipWithN' na f

-- This version can work with (+) but must be annotated with its
-- return type. Otherwise the result type is ambiguous

example7 :: [Bool]
example7 = zipWith' (&&) [False, True, False] [True, True, False]

example8 :: [Int]
example8 = zipWith' (+) [1,2,3] [4,5,6]

-----------------------------------------------------------------
-- trying to feed information both directions


data D n a b where
  DZ :: D Zero a [a]
  DS :: D n b1 b2 -> D (Succ n) (a -> b1) ([a] -> b2)
  
appN'' :: D n a b -> [a] -> b
appN'' DZ      fs = fs
appN'' (DS dn) fs = \x -> (appN'' dn (fs `zap` x))


zipWithN'' :: D n a b -> a -> b
zipWithN'' n f = appN'' n (repeat f)

class C n a b | b -> a, n a -> b where
  nat :: D n a b 
instance C Zero a [a] where
  nat = DZ
instance C n b1 b2 => C (Succ n) (a -> b1) ([a] -> b2)  where
  nat = DS nat

zipWith'' :: forall a b . C (CountArgs a) a b => a -> b
zipWith'' f = zipWithN'' (nat :: D (CountArgs a) a b) f

-- This version works with *either* annotation for example10
-- but must have one of them.

-- example9 :: [Bool]
example9 = zipWith'' (&&) [False, True, False] [True, True, False]

-- still needs either a result type, or a type annotation on plus
-- example10 :: [Int]
example10 = zipWith'' ((+) :: Int -> Int -> Int) [1,2,3] [4,5,6]

