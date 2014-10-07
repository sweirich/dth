-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist tree that proves both priority and rank     --
-- invariants and uses single-pass merging algorithm.                --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module SinglePassMerge.CombinedProofs where

import Basics
import SinglePassMerge.RankProof ( proof1a, proof1b, proof2a, proof2b )

data Heap :: Nat -> Nat -> * where
  Empty :: Heap b Zero
  Node  :: SNat p -> GEq p b -> GEq l r -> Heap p l -> Heap p r
        -> Heap b (Succ (l :+ r))

rank :: Heap b l -> Sing l
rank Empty            = SZero
rank (Node _ _ _ l r) = SSucc (rank l %:+ rank r)

-- Here we combine previously conducted proofs of rank and priority
-- invariants in the same way we did it for two-pass merging algorithm
-- in TwoPassMerge.CombinedProofs. The most important thing here is
-- that we use order function both when comparing priorities and ranks
-- of new subtrees. This gives us evidence that required invariants
-- hold.
merge :: forall (l :: Nat) (r :: Nat) (b :: Nat).
         Heap b l -> Heap b r -> Heap b (l :+ r)
merge Empty h2 = h2
merge h1 Empty = gcastWith (sym (plusZero (SSucc (rank h1))))
                           h1 -- See [merge, proof 0b]
merge h1@(Node p1 p1geb l1ger1 l1 r1) h2@(Node p2 p2geb l2ger2 l2 r2) =
  case (order p1 p2, order l1Rank (r1Rank %:+ h2Rank),
                     order l2Rank (r2Rank %:+ h1Rank) ) of
    (Le p1lep2, Ge l1ger1ph2, _) ->
       gcastWith
        (proof1a l1Rank r1Rank l2Rank r2Rank)
        (Node p1 p1geb l1ger1ph2 l1 (merge r1 (Node p2 p1lep2 l2ger2 l2 r2)))
    (Le p1lep2, Le l1ler1ph2, _) ->
       gcastWith
        (proof1b l1Rank r1Rank l2Rank r2Rank)
        (Node p1 p1geb l1ler1ph2 (merge r1 (Node p2 p1lep2 l2ger2 l2 r2)) l1)
    (Ge p1gep2, _, Ge l2ger2ph1) ->
       gcastWith
        (proof2a l1Rank r1Rank l2Rank r2Rank)
        (Node p2 p2geb l2ger2ph1 l2 (merge r2 (Node p1 p1gep2 l1ger1 l1 r1)))
    (Ge p1gep2, _, Le l2ler2ph1) ->
       gcastWith
        (proof2b l1Rank r1Rank l2Rank r2Rank)
        (Node p2 p2geb l2ler2ph1 (merge r2 (Node p1 p1gep2 l1ger1 l1 r1)) l2)
   where l1Rank = rank l1
         r1Rank = rank r1
         l2Rank = rank l2
         r2Rank = rank r2
         h1Rank = rank h1
         h2Rank = rank h2
