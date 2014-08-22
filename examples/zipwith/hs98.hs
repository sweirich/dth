{-# LANGUAGE TypeFamilies, ExplicitForAll, DataKinds, GADTs, MultiParamTypeClasses,
             FlexibleInstances, FlexibleContexts, ScopedTypeVariables #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- n-ary zipWith, from
-- Do we Need Dependent Types?
-- Daniel Fridlender, Mia Indrika


{- There are two challenges here. 

   The first is to define the various versions of zipWith with a single
   definition. This definition takes as its first argument the arity of the
   function.

   The second is to automatically supply this argument through type inference.

   These two challenges interfere with eachother, because the the type of the 
   first argument is different. However, it is possible to adapt solutions to  
   the second challenge among the various versions.
   
-}


import Prelude hiding (zipWith)

zap :: [a -> b] -> [a] -> [b]
zap [] [] = []
zap (f:fs)(x:xs) = f x : zap fs xs
zap _ [] = []
zap [] _ = []


-- basic pattern 
-- zipWith is   \f x1 ... xn -> repeat f `zap` x1 `zap` ... `zap` xn

-- z :: a -> a
z = id

-- s :: ([b] -> c) -> [a -> b] -> [a] -> c
s = \n fs as -> n (fs `zap` as)

-- zipWith :: ([a] -> b) -> a -> b
zipWithN n f = n (repeat f)

-- one ::  [a -> b] -> [a] -> [b]
one = s z

-- two :: [a -> a1 -> b] -> [a] -> [a1] -> [b]
two = s (s z)

-- three :: [a -> a1 -> a2 -> b] -> [a] -> [a1] -> [a2] -> [b]
three = s (s (s z))


-- it just works, but we need to supply the arity

example1 = zipWithN (s z)     not [False,True]
example2 = zipWithN (s (s z)) (+) [1,3] [4,5]


---------------------------------------------------------
---------------------------------------------------------

data Nat = Zero | Succ Nat

data Proxy (p :: Nat) = P

-- Map the type constructor [] over the types of arguments and return value of
-- a function
type family Listify (n :: Nat) (arrows :: *) :: * where
  Listify (Succ n) (a -> b) = [a] -> Listify n b
  Listify Zero a = [a]
  
-- Count the number of arguments of a function
type family CountArgs (f :: *) where
  CountArgs (a -> b) = Succ (CountArgs b)
  CountArgs result   = Zero

-- Use type classes to automatically infer that evidence
class CNumArgs (numArgs :: Nat) (arrows :: *) where
  getNA :: Proxy numArgs -> [arrows] -> Listify numArgs arrows
instance CNumArgs Zero a where
  getNA _ = z
instance CNumArgs n b => CNumArgs (Succ n) (a -> b) where
  getNA _ = s (getNA  (P :: Proxy n))

-- Variable arity zipWith, inferring the number of arguments and using
-- implicit evidence of the argument count.
  
zipWith :: forall f n. (CountArgs f ~ n) => CNumArgs n f => f -> Listify n f
zipWith f = zipWithN (getNA (P :: Proxy n)) f

-- Calling this requires having a concrete return type of the function to
-- be applied; if it's abstract, we can't know how many arguments the function
-- has. So, zipWith (+) ... won't work unless (+) is specialized.

example3 = zipWith (&&) [False, True, False] [True, True, False]
example4 = zipWith ((+) :: Int -> Int -> Int) [1,2,3] [4,5,6]

---------------------------------------------------------

{-
-- Backwards version

type family Delistify (a :: *) :: * where
  Delistify [a] = a
  Delistify ([a] -> b) = a -> Delistify b


-- Use type classes to automatically infer that evidence
class C (arrows :: *) where
  c :: [Delistify arrows] -> arrows
instance C [a] where
  c = z
instance C b => C ([a] -> b) where
  c = s c
  
zipWith' :: C a => Delistify a -> a 
zipWith' = zipWithN c

-- type annotations are required to eliminate ambiguity

example3' :: [Bool]
example3' = zipWith' (&&) [False, True, False] [True, True, False]

example4' :: [Int]
example4' = zipWith' ((+) :: Int -> Int -> Int) [1,2,3] [4,5,6]

-}


