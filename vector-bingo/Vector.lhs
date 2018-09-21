
title: What are Dependent Types?
author: Stephanie Weirich
address: University of Pennsylvania
event: PLMW 2018
date: Sepember 23, 2018

contents: An introductory talk about the role of dependent types in
programming language research, using the "hello world" example of
length-indexed vectors in the Haskell programming language.

topics:
  - What *are* dependent types? What are they good for?
  - What are the important research problems?
  - How do you get started in dependent types research?

caveat: I almost never use length-indexed vectors when I'm programming in
Haskell, for reasons that I discuss below. However, they still make a really
nice example because they hit all of the points. And, almost any tutorial on
dependent types starts with them, so if you haven't seen them before you will
soon. But most of the actual code here should probably be written in
LiquidHaskell.  (See Niki and Joachim's Haskell Symposium talk on Friday.)

note: this this international conference on functional PROGRAMMING. Sometimes
it is easy to forget that with all the math. But the math is there for a
reason, to make us understand programming and programming languages
better. So, for this talk, I'm going to focus more on programming, even though
that is the motivation of the research program, not the methodology.


> {-# LANGUAGE TypeInType, TypeApplications, TypeFamilies, ScopedTypeVariables,
>     DataKinds, GADTs, UndecidableInstances, TypeOperators, AllowAmbiguousTypes,
>     TypeSynonymInstances, MultiParamTypeClasses, FlexibleContexts,
>     FlexibleInstances #-}
> 
> module Vector where
> import System.Random
> import Prelude hiding (max, reverse, replicate, (!!), Ordering, GT, LT, EQ, compare)
> import qualified Prelude

What is a dependently typed programming language?
------------------------------------------------

It turns out, not Haskell. But Haskell has enough type system features that it
can encode dependently-typed programming.

  ## Feature: Constrained data and control-sensitive typing

We can define Peano numbers (i.e. natural numbers in Haskell)

> data Nat = Z | S Nat   

> type One   = S Z
> type Two   = S One
> type Three = S (S (S Z))
> type Four  = S Three
> type Five  = S Four

and then use them to define a length-indexed vector:

> data Vec n a where
>   Nil  :: Vec Z a
>   (:>) :: a -> Vec n a -> Vec (S n) a 
>
> infixr :>

For example,

> stl :: Vec Three Char
> stl = 'S' :> 'T' :> 'L' :> Nil

What is so useful about length indexed vectors?
-----------------------------------------------

ghci> :t maximum stl
ghci> :t maximum Nil


We can use the length to give a better type to the max function

> max :: Ord a => Vec (S n) a -> a
> max (x :> Nil) = x
> max (x :> y :> xs) =
>   if x > y then max (x :> xs) else max (y :> xs)
>

 ## Historical interlude on GADTs:

  GADTs were introduced into GHC in the mid-2000's.
  I worked with Simon PJ, Geoff Washburn and Dimitrios Vytiniotis
  We were not working in a vacuum: prior work by
     James Cheney, Ralf Hinze, Francois Pottier, Hongwei Xi and Karl Crary
     (also unpublished draft by Lennart Augustsson)
  Main question we faced: how to incorporate into HM type inference
  It took several drafts for the paper to be published
     (first TR draft 2004, appeared in ICFP 2006).
  And even then, that version was superceded by OutsideIn.
  I did not see all the uses then -- I just wanted them for generic programming.
  Note: this is a survivor story.  My other paper from ICFP 2006 has
  (rightly!) faded into obscurity.


BINGO
-----

       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |          |          |          |
       |    B     |    I     |    N     |    G     |    O     |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+
       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |  Free    |          |          |
       |          |          |  Space   |          |          |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       |          |          |          |          |          |
       +----------+----------+----------+----------+----------+




We can also constrain a bingo card so that it is
five columns

> data Bingo a = Card { b :: Vec Five a,
>                       i :: Vec Five a,
>                       n :: Vec Four a,  -- NOTE only 4 here b/c free space
>                       g :: Vec Five a,
>                       o :: Vec Five a }

   
DTP Feature: Pi types
---------------------

Let's make some random bingo cards!

First step, random vectors.

We want code that looks like this:


   randomVec range Z     = return Nil    -- empty vector for 0
   randomVec range (S n) = do
     xs <- randomVec range n    -- generate vec of length n
     x  <- fresh range xs       -- get random # that is unused
     return $ x :> xs           -- produce a vec of length n+1

What is the type of this function???

   randomVec :: (Int,Int) -> Pi (n : Nat) -> IO (Vec n Int)

The difficulty is that we need to use the number 'n' as both
a value (how many numbers to generate) and in the type
(to describe the length of the list that we generated).

We can't do this in Haskell.

Instead, we need to use the 'Singleton' trick because Haskell does not
allow terms to be used both at runtime and in types.

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
> randomVec range SZ     = return Nil
> randomVec range (SS n) = do
>   xs <- randomVec range n
>   x  <- fresh range xs     -- get a random element that is unused
>   return $ x :> xs


> randomCard :: IO (Bingo Int)
> randomCard = do
>   Card  <$> randomVec (0,15)  sFive
>         <*> randomVec (15,30) sFive
>         <*> randomVec (30,45) sFour  -- must only pick four in the middle column!
>         <*> randomVec (45,60) sFive
>         <*> randomVec (60,75) sFive

 ## Haskell is not really dependently-typed

Note that we had to use the clumst SNat type and its values sFour and
sFive. In languages like Agda/Idris, with *full-spectrum dependency* this
approach is not necessary. (Richard Eisenberg and I have a current research
project on adding this feature to Haskell. For more information, two talks in
parallel session to this one that talk about recent advances.)

 ## DTP feature: verified programming, Haskell-style

Here's a type class that declares which indices (m) are safe to access which
columns (n).  In general, the type class asks Haskell to prove (at compile
time) that m is less than n. If this proof succeeds, then the result is a
safe accessor function for vectors.

> class LessThan m n where
>   (!!) :: Vec n a -> SNat m ->  a
>
> -- Z is less than any non-zero peano number
> instance LessThan Z (S n) where
>   (x :> xs) !! SZ = x
>
> -- if m < n then their sucessors are also <
> instance LessThan m n => LessThan (S m) (S n) where
>   (_ :> xs) !! (SS sm) = xs !! sm

In the code below, Haskell is doing a proof for us. For example, in each case
it proves that 0 is less than 4 or 5, so that we know it is safe to access the
'0th' element of each of our columns.

> get0 :: Bingo a -> Vec Five a
> get0 c = (b c !! m) :> (i c !! m) :> (n c !! m) :> (g c !! m) :> (o c !! m) :> Nil
>   where m = SZ

> get1 :: Bingo a -> Vec Five a
> get1 c = (b c !! m) :> (i c !! m) :> (n c !! m) :> (g c !! m) :> (o c !! m) :> Nil
>   where m = SS SZ

The middle row has a free space. Make sure its type tells us that...

> get2 :: Bingo a -> Vec Four a
> get2 c = (b c !! m) :> (i c !! m) :> {-- FREE  --} (g c !! m) :> (o c !! m) :> Nil
>   where m = SS (SS SZ)

> get3 :: Bingo a -> Vec Five a
> get3 c = (b c !! m) :> (i c !! m) :> (n c !! sub1 m) :> (g c !! m) :> (o c !! m) :> Nil
>   where m = SS (SS (SS SZ))

Watch what happens if we forget the 'sub1' for the 'n' column...

> get4 :: Bingo a -> Vec Five a
> get4 c = (b c !! m) :> (i c !! m) :> (n c !! sub1 m) :> (g c !! m) :> (o c !! m) :> Nil
>   where m = SS (SS (SS (SS SZ)))


Let's check if we have a winner!!

> ldiag :: Bingo a -> Vec Four a
> ldiag c = (b c !! SZ) :> (i c !! sOne) :> {- FREE -} (g c !! sThree) :> (o c !! sFour) :> Nil

> rdiag :: Bingo a -> Vec Four a
> rdiag c = (b c !! sFour) :> (i c !! sThree) :> {- FREE -} (g c !! sOne) :> (o c !! SZ) :> Nil



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


How does this relate to PL research?
-----------------------------------

 - What is the expressiveness of dependently typed languages? What sort of
   programs can we write? What classes of programs are difficult to write?

 - Can we extend DT languages with features in support of metaprogramming?
   (i.e. programs that manipulate other programs, like compilers)

 - How do dependent types integrate with other features in programming languages?

 - Can we make the definition of equality more expressive?
   (Univalence: isomorphic types are equal types)

 - What is the semantics of dependently-typed languages?

  
DEPENDENT TYPES at ICFP 2018
----------------------------

ICFP 2018
  - A Type and Scope Safe Universe of Syntaxes with Binding: Their Semantics and Proofs
  - Handling Delimited Continuations with Dependent Types
  - Equivalences for Free: Univalent Parametricity for Effective Transport 
  - Elaborating Dependent (Co)pattern Matching
  - Generic Zero-Cost Reuse for Dependent Types
  - Ready, Set, Verify! Applying hs-to-coq to Real-World Haskell Code (Experience Report)

TyDe 2018
  - Authdenticated Modular Maps in Haskell
  - Extensible Type Directed Editing
  - Implementing Resource-Aware Safe Assembly for Kernel Probes as a Dependently-Typed DSL
  - Improving Error Messages for Dependent Types

NPFL 
  - APLicative Programming with Naperian Functors

Tutorial 
  - T01: Introduction to Programming and Proving in Cedille
  - T04: Beluga: Programming Proofs About Formal Systems

Haskell (Not actually DT)
  - The Thoralf plugin: for your fancy type needs
  - Ghosts of Departed Proofs (Functional Pearl)
  - Theorem Proving for All: Equational Reasoning in Liquid Haskell (Functional Pearl)


More information
----------------

 Coq
 Agda
 Idris
 Cedille
 Beluga
 .. and Haskell


Coda
----

Some challenge problems for length-indexed vectors:

- Show that map preserves the length of its input

> map :: (a -> b) -> Vec n a -> Vec n b
> map = undefined

- Show that insertion sort preserves the length of its input

> insert :: Ord a => a -> Vec n a -> Vec (S n) a
> insert x Nil = x :> Nil
> insert x (y :> ys) =
>   if x < y then x :> y :> ys
>            else y :> insert x ys

> isort :: Ord a => Vec n a -> Vec n a
> isort Nil = Nil
> isort (x :> xs) = insert x (isort xs)

- Show that reverse preserves the length of its input

This one requires a function that can appear in types.  


> type family Plus (m :: Nat) (n ::  Nat) :: Nat where
>    Plus Z     n = n
>    Plus (S m) n = Plus m (S n)
> 
> -- tail recursive version of reverse
> revappend :: Vec m a -> Vec n a -> Vec (Plus m n) a
> revappend Nil       ys = ys
> revappend (x :> xs) ys = revappend xs (x :> ys)
> 
> {- And many times a system for doing proofs. -}
> {-
> reverse :: forall m a. Vec m a -> Vec m a
> reverse xs = case (lemma1 @m) of
>                Refl -> revappend xs Nil
> 
> append :: forall m n a. Vec m a -> Vec n a -> Vec (Plus m n) a
> append Nil       vn = vn
> append (x :> (xs :: Vec n1 a)) vn =
>   case lemma2 @n1 @n of
>     Refl -> x :> append xs vn
> 
> 
> lemma1 :: forall m. Plus m Z :~: m
> lemma1 = trustme
> 
> lemma2 :: forall n1 n. Plus n1 ('S n) :~: 'S (Plus n1 n)
> lemma2 = trustme
> -}

Appendix
--------

-- Additional definitions

-- operations on vectors

> instance Show a => Show (Vec n a) where
>   show Nil = "Nil"
>   show (x :> xs) = show x ++ " :> " ++ show xs

> instance Functor (Vec n) where
>   fmap f Nil = Nil
>   fmap f (x :> xs) = f x :> fmap f xs

> instance Foldable (Vec n) where
>   foldr f b Nil       = b
>   foldr f b (x :> xs) = f x (foldr f b xs)



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


To print out a bingo card, we need to be able to access it row-by-row.

-- How to show a vector as a row on a bingo card
-- Four-element rows have a free space
-- Five-element rows do not.

> class ShowRow n where
>    showRow :: Show a => Vec n a -> String
> instance ShowRow Four where
>    showRow (a :> b :> c :> d :> Nil) =
>      padL 3 (show a) ++ " | " ++
>      padL 3 (show b) ++ " | " ++
>              " FR"   ++ " | " ++
>      padL 3 (show c) ++ " | " ++
>      padL 3 (show d)
> instance ShowRow Five where
>    showRow (a :> b :> c :> d :> e :> Nil) =
>      padL 3 (show a) ++ " | " ++
>      padL 3 (show b) ++ " | " ++
>      padL 3 (show c) ++ " | " ++
>      padL 3 (show d) ++ " | " ++
>      padL 3 (show e)


> instance Show a => Show (Bingo a) where
>   show bingo =
>               "  B |  I  |  N  |  G  |  O "
>    ++ "\n" ++ "---------------------------"
>    ++ "\n" ++ showRow (get0 bingo)
>    ++ "\n" ++ showRow (get1 bingo)
>    ++ "\n" ++ showRow (get2 bingo)
>    ++ "\n" ++ showRow (get3 bingo)
>    ++ "\n" ++ showRow (get4 bingo)
