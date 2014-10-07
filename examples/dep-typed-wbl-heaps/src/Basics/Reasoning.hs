-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Refl datatype and functions required for equational reasoning.    --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE TypeOperators       #-}
module Basics.Reasoning where

import Basics.Nat
import Basics.Ordering
import Basics.Sing
import Basics.Unreachable

-- Definitions of :~:, sym, trans and gcastWith are taken from
-- Data.Type.Equality module in base package distributed with GHC 7.8.

-- The basic definition we will need in our proofs is propositional
-- equality (known as Refl). This datatype allows to express equality
-- between two types.
data a :~: b where
  Refl :: a :~: a

-- Below we prove basic properties of Refl: symmetry, transitivity,
-- congruence and substitution. If these proofs are not familiar I
-- encourage to take a look at Agda tutorials on Agda Wiki. The most useful
-- source in my opinion are the online lecture notes for the Computer
-- Aided Formal Reasoning course by Thorsten Altenkirch:
--
-- http://www.cs.nott.ac.uk/~txa/g53cfr/
sym :: (a :~: b) -> (b :~: a)
sym Refl = Refl

trans :: (a :~: b) -> (b :~: c) -> (a :~: c)
trans Refl Refl = Refl

-- congruence is defined for a function working on singleton
-- types. Agda's definition is more general because Agda has a common
-- language for terms and types.
cong :: (Sing a -> Sing b) -> (a :~: c) -> (f a :~: f c)
cong _ Refl = Refl

-- Agda's equivalent of gcastWith is subst, used for type-safe casts
-- when we have a proof of equality of two types. gcast with is more
-- convenient to use than Agda's subst because it doesn't require the
-- type constructor to be passed in. (See my Agda implementation if
-- this doesn't make sense).
gcastWith :: (a :~: b) -> ((a ~ b) => r) -> r
gcastWith Refl x = x

-- Now let's prove some basic properties of addition that we will need
-- later in more complex proofs. I assume that you had previous
-- exposure to these basic proofs, but nevertheless I provide
-- extensive explanations. Make sure you understand how these proofs
-- work before proceeding with rest.

-- Note [0 is right identity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- The fact that 0 is left identity of addition (ie. 0 + a :~: a)
-- follows directly from our definition of +:
--
--   (+) :: Nat -> Nat -> Nat
--   Zero     + m = m
--   (Succ n) + m = Succ (n + m)
--
-- But we need a separate proof that 0 is also right identity of
-- addition, ie. a + 0 :~: a. Proof proceeds by induction on a. If a
-- is 0 then we have:
--
--   0 + 0 = 0
--
-- And the proof follows from the definition of addition - hence we
-- use Refl. In a recursive case we have:
--
--   (Succ a) + Zero :~: (Succ a)
--
-- Applying definition of addition to LHS we have:
--
--   Succ (a + Zero) :~: Succ a
--
-- Since we have Succ on both sides of the equality, we use
-- congruence. This leaves us with a proof that equality holds for the
-- parameters of Suc:
--
--   a + Zero :~: a
--
-- But that happens to be the equality we are proving at the
-- moment. We therefore make a recursive call to (plusZero a), which is
-- equivalent of applying inductive hypothesis in an inductive proof.
--
-- QED

-- See Note [0 is right identity of addition]
plusZero :: SNat a -> ((a :+ Zero) :~: a)
plusZero  SZero    = Refl
plusZero (SSucc a) = cong SSucc (plusZero a)


-- Note [1 + (a + b) equals a + (1 + b)]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We will need this property surprisingly often. We proceed by
-- inductive proof on a. In the base case, when a = 0, we have:
--
--   Succ (Zero + b) :~: Zero + (Succ b)
--
-- Applying definition of + to both sides of equality we get:
--
--   Succ b :~: Succ b
--
-- Which is true by definition, hence we use Refl. In the recursive
-- case we have:
--
--   Succ ((Succ a) + b) :~: (Succ a) + (Succ b)
--
-- We apply definition of + to both sides and get:
--
--   Succ (Succ (a + b)) :~: Succ (a + (Succ b))
--
-- Again, since we have Succ on both sides we use congruence and are
-- left with a proof:
--
--   Succ (a + b) :~: a + (Succ b)
--
-- which again is the equality we are proving. We appeal to inductive
-- hypothesis by making a recursive call.
--
-- QED

plusSucc :: SNat a -> SNat b -> ((Succ (a :+ b)) :~: (a :+ (Succ b)))
plusSucc  SZero    _ = Refl
plusSucc (SSucc a) b = cong SSucc (plusSucc a b)


-- Note [Commutativity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Everyone knows that a + b :~: b + a. But Haskell won't take our
-- word and requires a formal proof. Let's proceed by induction on b.
-- In the base case we have:
--
--   a + 0 :~: 0 + a
--
-- Right side reduces by the definition of + which leaves us with
--
--   a + 0 :~: a
--
-- We proved that earlier so we appeal to already existing proof. In
-- the inductive case we have:
--
--   a + Succ b :~: (Succ b) + a      [1]
--
-- Right hand side reduces by definition of + giving us:
--
--   a + Succ b :~: Succ (b + a)      [2]
--
-- [2] is therefore the equality we have to prove. From plusSucc we know
-- that
--
--   Succ (a + b) :~: a + (Succ b)    [3]
--
-- And we can use that to transform left hand side of [1]. Note
-- however that in order to apply [3] to left hand side of [1] we need
-- to reverse sides of the equality [3]:
--
--   a + (Succ b) :~: Succ (a + b)    [4]
--
-- We achieve this by using symmetry.
--
-- Looking at right hand sides of [2] and [4] we see they differ by
-- the order of arguments to +. We can prove them equal by using
-- congruence on Succ and appealing to our inductive hypothesis of
-- commutativity of addition. This means we have proven two things:
--
--   a + (Succ b) :~: Succ (a + b)   [4, repeated], from symmetry
--                                                  of plusSucc
--   Succ (a + b) :~: Succ (b + a)   [5], from congruence on Succ and
--                                        inductive hypothesis
--
-- Combining [4] and [5] using transitivity yields the proof of [2].
--
-- QED
--
-- Here is a diagram, showing how code relates to the proof:
--
--                                       a + b :~: b + a
--                                          ____|____
--                                         /         \
-- trans (sym (plusSucc a b)) (cong SSucc (plusComm a b))
--        ̲\________________/   \_______________________/
--                |                        |
--  a + (Succ b) :~: Succ (a + b)          |
--                           Succ (a + b) :~: Succ (b + a)

plusComm :: SNat a -> SNat b -> (a :+ b) :~: (b :+ a)
plusComm a   SZero   = plusZero a
plusComm a (SSucc b) = trans (sym (plusSucc a b))
                             (cong SSucc (plusComm a b ))


-- Note [Associativity of addition]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- To prove a + (b + c) :~: (a + b) + c we proceed by induction on a.
-- In the base case we have a = 0:
--
--   0 + (b + c) :~: (0 + b) + c
--
-- Both sides can be normalized using the definition of + giving us
--
--   b + c :~: b + c
--
-- Since this is true by definition we use Refl. In the inductive case
-- we have to prove:
--
--   Succ a + (b + c) :~: (Succ a + b) + c
--
-- Again, both sides are normalized using definition of + :
--
--   LHS: Succ a + (b + c) :~: Succ (a + (b + c))
--   RHS: (Succ a + b) + c :~: Succ (a + b) + c :~: Succ ((a + b) + c)
--
-- This means we have to prove:
--
--   Succ (a + (b + c)) :~: Succ ((a + b) + c)
--
-- We can use congruence to remove the outer Succ on both sides which
-- leaves us with a proof of:
--
--   a + (b + c) ̄:~: (a + b) + c
--
-- Which happens to be our inductive hypothesis - hence a recursive
-- call to plusAssoc.
--
-- QED

plusAssoc :: SNat a -> SNat b -> SNat c -> (a :+ (b :+ c)) :~: ((a :+ b) :+ c)
plusAssoc  SZero    _ _ = Refl
plusAssoc (SSucc a) b c = cong SSucc (plusAssoc a b c)


-- Note [If numbers are equal they are in the greater-equal relation]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Finally, we need a proof that if a = b then a >= b. This property is
-- specific to our task, so you most likely haven't seen it other
-- tutorials. There are some interesting things in this proof:
--
--  1) a value of type (GEq m n) proves that m is greater-equal than n. We
--     therefore need to construct the value of this type.
--
--  2) since Refl is the only constructor of type :~: we always use Refl
--     when pattern matching on a value of :~:. We also always pass Refl
--     as a value of :~: in calls.
--
--  3) In Agda we could make the first two parameters implicit
--     (ie. deducible from the type a :~: b). We can't do that in
--     Haskell, so they are explicit. This is only slightly
--     inconvenient. What is more inconvenient is that Haskell can't
--     recognize that only two of four equations are actually
--     accessible. We need to write the inaccessible equation or GHC
--     will complain about non-exhaustive pattern matching. See
--     documentation of Basics.Unreachable for more details. The
--     requirement that the two SNat parameters are equal comes from
--     the (a :~: b) type which says that a and b are equal.
--
-- In the base case we need to construct a proof that 0 >= 0, which we
-- do by using GeZ. Inductive case simply applies GeZ to result of
-- recursive call to geqSym.

geqSym :: SNat a -> SNat b -> a :~: b -> GEq a b
geqSym  SZero     SZero    Refl = GeZ
geqSym (SSucc a) (SSucc b) Refl = GeS (geqSym a b Refl)
geqSym  SZero    (SSucc _) _    = unreachable
geqSym (SSucc _)  SZero    _    = unreachable
