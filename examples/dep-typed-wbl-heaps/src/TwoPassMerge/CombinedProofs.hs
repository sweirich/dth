-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist tree that proves both priority and rank     --
-- invariants. Uses a two-pass merging algorithm.                    --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module TwoPassMerge.CombinedProofs where

import Basics
import TwoPassMerge.RankProof     ( makeTlemma, proof1, proof2 )
import TwoPassMerge.PriorityProof ( geqTrans )

-- Now that we have separate proofs of priority and rank invariants we
-- can combine them into one proof. We index Heap with two indices:
-- one for Priority and one for Rank.
-- Priority -> Rank -> *
data Heap :: Nat -> Nat -> * where
  Empty :: Heap b Zero
  Node  :: SNat p -> GEq p b -> GEq l r -> Heap p l -> Heap p r -> Heap b (Succ (l :+ r))

rank :: Heap b l -> Sing l
rank Empty            = SZero
rank (Node _ _ _ l r) = SSucc (rank l %:+ rank r)

-- Now we will combine functions that prove priority invariant and
-- functions that prove rank invariant into functions that prove both
-- invariants.

-- Let's begin with singleton. Note the type of created Heap. We set
-- first index to zero, because it proves the priority invariant and
-- second index to one because it proves rank invariant. The node now
-- needs two GeZ evidence.
singleton :: forall (p :: Nat). Sing p -> Heap Zero One
singleton p = Node p GeZ GeZ Empty Empty

-- makeT function requires that we supply evidence that priority
-- invariant holds (value of type `GEq p b`), guarantee that resulting
-- heap has correct size and maintains rank invariant by using Order
-- type to supply evidence of rank correctness to node constructor.
makeT :: SNat l -> SNat r -> SNat p -> GEq p b ->
         Heap p l -> Heap p r -> Heap b (Succ (l :+ r))
makeT lRank rRank p pgen l r = case order lRank rRank of
  Ge lger -> Node p pgen lger l r
  Le rgel -> gcastWith (makeTlemma rRank lRank) (Node p pgen rgel r l)

-- merge combines previous proofs:
--
--  1) it enforces priority invariant by comparing priorities using
--     order function. Recall that this function returns value of
--     Order datatype that not only gives a result of comparison but
--     also supplies evidence that result is true. That evidence is
--     given to makeT which uses it to construct a new node.
--
--  2) it proves size invariant of merge by reusing proofs from
--     TwoPassMerge.RankProof
--
--  3) it delegates the proof of rank invariant to makeT
merge :: forall (l :: Nat) (r :: Nat) (b :: Nat).
         Heap b l -> Heap b r -> Heap b (l :+ r)
merge Empty h2 = h2 -- See [merge, proof 0a]
merge h1 Empty =
    gcastWith (sym (plusZero (SSucc (rank h1)))) h1 -- See [merge, proof 0b]
merge h1@(Node p1 p1geb l1ger1 l1 r1)
      h2@(Node p2 p2geb l2ger2 l2 r2) = case order p1 p2 of
          Le p1lep2 -> gcastWith
               (proof1 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 1]
               (makeT l1Rank (r1Rank %:+ h2Rank) p1 p1geb l1
                      (merge r1 (Node p2 p1lep2 l2ger2 l2 r2)))
          Ge p1gep2 -> gcastWith
               (proof2 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 2]
               (makeT l2Rank (r2Rank %:+ h1Rank) p2 p2geb l2
                      (merge r2 (Node p1 p1gep2 l1ger1 l1 r1)))
      where l1Rank = rank l1
            r1Rank = rank r1
            l2Rank = rank l2
            r2Rank = rank r2
            h1Rank = rank h1
            h2Rank = rank h2

-- Implementations of insert and findMin are the same as
-- previously. We only need to update the type signature accordingly.
insert :: SNat p -> Heap Zero r -> Heap Zero (Succ r)
insert p h = merge (singleton p) h

findMin :: Heap b p -> Nat
findMin Empty            = undefined
findMin (Node p _ _ _ _) = fromSing p


-- To define deleteMin we will need to update definition of
-- liftBound to deal with the new definition of Heap.

liftBound :: GEq b p -> Heap b r -> Heap p r
liftBound _      Empty                = Empty
liftBound bgen (Node p pgeb lger l r) = Node p (geqTrans pgeb bgen) lger l r

-- With the new definition of liftBound we can now define deleteMin.
-- Implementation is a combination of earlier implementations. It uses
-- liftBound (like the PriorityProof implmentation) and is total (like
-- RankProof implementation).
deleteMin :: Heap b (Succ r) -> Heap b r
deleteMin (Node _ pgeb _ l r) = merge (liftBound pgeb l) (liftBound pgeb r)
