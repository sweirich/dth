title:   Dependent Types
author:  Stephanie Weirich
address: University of Pennsylvania
event:   PLMW 2018
date:    September 23, 2018
url:     https://github.com/sweirich/dth
========================================

contents: An introductory talk about the role of dependent types in
programming language research, using the "hello world" example of
length-indexed vectors in the Haskell programming language.

caveat:









===================================================================================

> {-# LANGUAGE TypeInType, TypeApplications, TypeFamilies, ScopedTypeVariables,
>     DataKinds, GADTs, UndecidableInstances, TypeOperators, AllowAmbiguousTypes,
>     TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts,
>     FlexibleInstances, StandaloneDeriving #-}
>
> {-# OPTIONS_GHC -fwarn-incomplete-patterns #-}
> 
> module Vector where
> import System.Random
> import Prelude hiding (max, reverse, replicate, (!!), Ordering, GT, LT, EQ, compare)
> import qualified Prelude

What is a dependently typed programming language?
=================================================









Feature: Constrained data
-------------------------

Natural numbers

> data Nat = Z | S Nat   

Here are some natural numbers that we can use in types.

> type Zero  = Z
> type One   = S Z
> type Two   = S One
> type Three = S (S (S Z)) -- either this or S Two works
> type Four  = S Three
> type Five  = S Four






Natural numbers are good for counting, so we will use them to count the number
of elements stored in a list.  The `Vec` datatype below is isomorphic to
lists, bit its type is more information. The first type argument to `Vec` is
`n`, the length of the vector.

> data Vec (n :: Nat) a where
>   Nil  :: Vec Z a
>   (:>) :: a -> Vec n a -> Vec (S n) a 
>
> infixr :>




> stl :: Vec Three Char
> stl = 'S' :> 'T' :> 'L' :> Nil

If we try to give it a different type, we will get a type error. The vector
is *constrained* by the type to be a certain length.

But, the type is not always constraining. We can also work with vectors
of any length.


> instance Foldable (Vec n) where
>   foldr f b Nil  = b
>   foldr f b (x :> xs) = x `f` (foldr f b xs)








What is so useful about length indexed vectors?
-----------------------------------------------
Feature: control-sensitive typing


Consider 'maximum'....

> safeMax :: (Ord a) => Vec (S n) a -> a
> --safeMax (x :> Nil) = x
> safeMax (x :> ys) = maximum (x :> ys)
> --safeMax Nil = error "a"
> --safeMax = maximum

















Historical interlude on GADTs
-----------------------------



















BINGO
=====
Bingo is a game played with cards of random numbers. Every player has a
different card. The columns are labeled so that players can find their numbers
quickly. The first column contains numbers from 1-15, the second from 16-30,
etc.
         B     I       N      G      O   
      +-----+------+------+------+------+
      | 14  |  28  |  35  |  57  |  68  |
      +-----+------+------+------+------+
      |  5  |  21  |  34  |  46  |  71  |
      +-----+------+------+------+------+
      |  4  |  24  | FREE |  54  |  72  |
      +-----+------+------+------+------+
      | 12  |  27  |  38  |  47  |  62  |
      +-----+------+------+------+------+
      | 11  |  23  |  43  |  53  |  61  |
      +-----+------+------+------+------+

The game is played by having a caller read out numbers. The first player to
mark a complete column, row or diagonal on the card wins.









Here's one way we might represent a player's card, capturing the invariant that
we have five columns, but the middle one only has four numbers.

> data Bingo a = Card { b :: Vec Five a,
>                       i :: Vec Five a,
>                       n :: Vec Four a,  -- NOTE only 4 here b/c free space
>                       g :: Vec Five a,
>                       o :: Vec Five a }


> card :: Bingo Int
> card = Card { b = 14 :> 5  :> 4  :> 12 :> 11 :> Nil,   -- Columns
>               i = 28 :> 21 :> 24 :> 27 :> 23 :> Nil, 
>               n = 35 :> 34 :>       38 :> 43 :> Nil,
>               g = 57 :> 46 :> 54 :> 47 :> 53 :> Nil,
>               o = 68 :> 71 :> 72 :> 62 :> 61 :> Nil }











   
DTP Feature: Pi types
---------------------

Let's make some random bingo cards!

First step, generate random vectors.

We want a function that looks like this:

     randomVec range n = case n of
        Z     -> return Nil                   -- empty vector for 0
        (S m) -> do xs <- randomVec range m   -- generate vec of length m
                    x  <- fresh range xs      -- get a random # that is unused
                    return $ x :> xs          -- produce a vec of length m+1

What is the type of this function? The type of the vector that we
produce *depends* on the argument, n.

   <<< randomVec :: (Int,Int) -> Pi n:Nat -> Vec n Int >>>

The difficulty is that we need to use the number 'n' as both
a value (how many numbers to generate) and in the type
(to describe the length of the list that we generated).










Singletons
----------

> data SNat a where
>   SZ :: SNat Z                  -- an exact copy of a natural number
>   SS :: SNat n -> SNat (S n)

We have the numbers again, this time as terms with constrained types

> sOne :: SNat One    -- each type has exactly one value
> sOne = SS SZ

> sTwo :: SNat Two    -- SS (SS SZ) is only value of type SNat Two
> sTwo = SS sOne





So we can write the code we want, with this type

> randomVec :: (Int,Int) -> SNat n -> IO (Vec n Int)
> randomVec range n = case n of
>        SZ     -> return Nil                   -- empty vector for 0
>        (SS m) -> do xs <- randomVec range m   -- generate vec of length m
>                     x  <- fresh range xs      -- get a random # that is unused
>                     return $ x :> xs








which gives us a way to generate random cards.

> randomCard :: IO (Bingo Int)
> randomCard = do
>   Card  <$> randomVec (1,15)  sFive
>         <*> randomVec (16,30) sFive
>         <*> randomVec (31,45) sFour  -- only four numbers in the middle column!
>         <*> randomVec (46,60) sFive
>         <*> randomVec (61,75) sFive








DTP feature: verified programming, Haskell-style
------------------------------------------------


> class LessThan m n where
>   (!!) :: Vec n a -> SNat m ->  a
>
> -- Z is less than any non-zero number
> instance LessThan Z (S n) where
>   (!!) = undefined
>
> -- if m < n then their sucessors are also <
> instance LessThan m n => LessThan (S m) (S n) where
>   (!!) = undefined

  
For example, we have

> x :: Char
> x = stl !! sTwo

> -- This should *not* type check
> --y :: Char
> --y = stl !! sFive

Let's use this code to write accessor functions for the rows of our bingo
cards.

           B     I       N      G      O   
        +-----+------+------+------+------+
   0    | 14  |  28  |  35  |  57  |  68  |
        +-----+------+------+------+------+
   1    |  5  |  21  |  34  |  46  |  71  |
        +-----+------+------+------+------+
   2    |  4  |  24  | FREE |  54  |  72  |
        +-----+------+------+------+------+
   3    | 12  |  27  |  38  |  47  |  62  |
        +-----+------+------+------+------+
   4    | 11  |  23  |  43  |  53  |  61  |
        +-----+------+------+------+------+

`get0` should give us the first row

       14 :> 28 :> 35 :> 57 :> 68 :> Nil

`get2` should give us the third row

        4 :> 24 :> 54 :> 72 :> Nil 



> get0 :: Bingo a -> Vec Five a
> get0 c = error "get0 is unimplemented"


> get1 :: Bingo a -> Vec Five a
> get1 c = error "get1 is unimplemented"
   






> get2 :: Bingo a -> Vec Four a   -- middle row has a free space
> get2 c = undefined
>   where m = SS (SS SZ)

> get3 :: Bingo a -> Vec Five a
> get3 c = undefined
>   where m = SS (SS (SS SZ))

> get4 :: Bingo a -> Vec Five a
> get4 c = undefined
>   where m = SS (SS (SS (SS SZ)))


Extra challenge:  check if we have a winner!!  

> ldiag :: Bingo a -> Vec Four a
> ldiag c = undefined

> rdiag :: Bingo a -> Vec Four a
> rdiag c = undefined

> won :: Bingo Int -> [Int] -> Bool
> won card numbers =
>   -- columns
>      all called (b card)
>   || all called (i card)
>   || all called (n card)
>   || all called (g card)
>   || all called (o card)
>   -- rows
>   || all called (get0 card)
>   || all called (get1 card)
>   || all called (get2 card)
>   || all called (get3 card)
>   || all called (get4 card)
>   -- diagonals
>   || all called (ldiag card)
>   || all called (rdiag card)  where
>  called x = x `elem` numbers


How does this relate to FP research?
-----------------------------------

Open questions:

 - What is the expressiveness of dependently typed languages? What sort of
   programs can we write? What classes of programs are difficult to write?

 - Can we extend DT languages with features in support of metaprogramming?
   (i.e. programs that manipulate other programs, like compilers)

 - How do dependent types integrate with other features in programming languages?

 - Can we make the definition of equality more expressive?
   (e.g. Univalence: isomorphic types are equal types)

 - Can we make proofs more automatic?

 - Tool support?

  
DEPENDENT TYPES at ICFP 2018
----------------------------

ICFP 2018
  - A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
  - Handling Delimited Continuations with Dependent Types
  - [*] Equivalences for Free: Univalent Parametricity for Effective Transport 
  - Elaborating Dependent (Co)pattern Matching
  - Generic Zero-Cost Reuse for Dependent Types
  - Mtac2: Typed Tactics for Backwards Reasoning in Coq
  - Ready, Set, Verify! Applying hs-to-coq to
         Real-World Haskell Code (Experience Report)



TyDe 2018
  - Authdenticated Modular Maps in Haskell
  - Extensible Type Directed Editing
  - Implementing Resource-Aware Safe Assembly for Kernel Probes
    as a Dependently-Typed DSL
  - Improving Error Messages for Dependent Types

NPFL 
  - APLicative Programming with Naperian Functors

Tutorial 
  - T01: Introduction to Programming and Proving in Cedille
  - T04: Beluga: Programming Proofs About Formal Systems

Haskell (Not actually DT, but related)
  - The Thoralf plugin: for your fancy type needs
  - Suggesting Valid Hole Fits for Typed-Holes (Experience Report)
  - Ghosts of Departed Proofs (Functional Pearl)
  - Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)


More 
----

To really get into dependent types, try it out.

 - [Coq](https://coq.inria.fr/)
 - [Agda](http://wiki.portal.chalmers.se/agda/pmwiki.php)
 - [Idris](https://www.idris-lang.org/)
 - [Cedille](https://cedille.github.io/)
 - [Beluga](http://complogic.cs.mcgill.ca/beluga/)
 - [LiquidHaskell](https://ucsd-progsys.github.io/liquidhaskell-blog/)



Coda
----

Some challenge problems for length-indexed vectors:

- Show that map preserves the length of its input

> map :: (a -> b) -> Vec n a -> Vec n b
> map = undefined

- Show that insertion sort preserves the length of its input

> isort :: Ord a => Vec n a -> Vec n a
> isort = undefined

- Show that reverse preserves the length of its input
(This one is challenging for Haskell.) 

You'll need a function that can appear in types, such as this one.
(Or maybe a variant of this one.)

> type family Plus (m :: Nat) (n ::  Nat) :: Nat where
>    Plus Z     n = n
>    Plus (S m) n = Plus m (S n)
> 
> reverse :: Vec m a -> Vec m a
> reverse xs = undefined

Appendix
--------

-- Additional definitions

-- operations on vectors

> instance Show a => Show (Vec n a) where
>   show Nil = "Nil"
>   show (x :> xs) = show x ++ " :> " ++ show xs

-- Singleton Nats!

> sThree :: SNat Three
> sThree = SS sTwo
> sFour :: SNat Four
> sFour = SS sThree
> sFive :: SNat Five
> sFive = SS sFour

> sub1 :: SNat (S n) -> SNat n
> sub1 (SS n) = n


-- Random numbers that are fresh for lists

> fresh :: (Random a, Eq a, Foldable f) => (a,a) -> f a -> IO a
> fresh range vec = do
>   x <- randomRIO range
>   if x `elem` vec then
>     fresh range vec
>     else return x

-- trusty left-pad

> padL :: Int -> String -> String
> padL n s
>    | length s < n  = Prelude.replicate (n - length s) ' ' ++ s
>    | otherwise     = s


> deriving instance Show a => Show (Bingo a)


To print out a bingo card, we need to be able to access it row-by-row.
-- How to show a vector as a row on a bingo card
-- Four-element rows have a free space
-- Five-element rows do not.

> class ShowRow n where
>    showRow :: Show a => Vec n a -> String
> 
> instance ShowRow Four where
>    showRow (a :> b :> c :> d :> Nil) = "|" ++
>      padL 3 (show a) ++ "  | " ++
>      padL 3 (show b) ++ "  | " ++
>              "FREE"  ++ " | " ++
>      padL 3 (show c) ++ "  | " ++
>      padL 3 (show d) ++ "  |"
> 
> instance ShowRow Five where
>    showRow (a :> b :> c :> d :> e :> Nil) = "|" ++
>      padL 3 (show a) ++ "  | " ++
>      padL 3 (show b) ++ "  | " ++
>      padL 3 (show c) ++ "  | " ++
>      padL 3 (show d) ++ "  | " ++
>      padL 3 (show e) ++ "  |"

> {-
> instance Show a => Show (Bingo a) where
>   show bingo =
>               "   B     I       N      G      O   "
>    ++ "\n" ++ "+-----+------+------+------+------+"
>    ++ "\n" ++ showRow (get0 bingo)
>    ++ "\n" ++ "+-----+------+------+------+------+"
>    ++ "\n" ++ showRow (get1 bingo)
>    ++ "\n" ++ "+-----+------+------+------+------+"
>    ++ "\n" ++ showRow (get2 bingo)
>    ++ "\n" ++ "+-----+------+------+------+------+"
>    ++ "\n" ++ showRow (get3 bingo)
>    ++ "\n" ++ "+-----+------+------+------+------+"
>    ++ "\n" ++ showRow (get4 bingo)
>    ++ "\n" ++ "+-----+------+------+------+------+"
> -}
