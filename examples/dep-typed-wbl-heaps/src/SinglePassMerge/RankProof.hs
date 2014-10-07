-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist heap that proves rank invariant and uses    --
-- a single-pass merging algorithm.                                  --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module SinglePassMerge.RankProof where

import Basics
-- We import rank proofs conducted earlier - they will be re-used.
import TwoPassMerge.RankProof ( makeTlemma )
import qualified TwoPassMerge.RankProof as RP ( proof1, proof2 )

data Heap :: Nat -> * where
  Empty :: Heap Zero
  Node  :: Priority -> GEq l r -> Heap l -> Heap r -> Heap (Succ (l :+ r))

rank :: Heap l -> Sing l
rank Empty          = SZero
rank (Node _ _ l r) = SSucc (rank l %:+ rank r)

-- Note [Proving rank invariant in single-pass merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Recall that in TwoPassMerge.RankProof we need to prove that:
--
--  1) makeT constructs node of correct size. There were two cases:
--
--     a) constructing a node without swapping l and r subtrees passed
--        to makeT. No extra proof was required as everything followed
--        from definitions.
--
--     b) constructing a node by swapping l and r subtrees (when rank
--        of r was greater than rank of l). We had to prove that:
--
--                    Succ (a + b) :~: Succ (b + a)
--
--        This proof is supplied by function makeTlemma.
--
--  2) resulting heap produced by merge has correct size. Merge has 4
--     cases (see [Two-pass merging algorithm]):
--
--     a) h1 is empty. No extra proof required (everything follows
--        from definition of +). See [merge, proof 0a].
--
--     b) h2 is empty. We had to prove that:
--
--                 h1 :~: h1 + 0
--
--        This proof is supplied by plusZero (in Basics.Reasoning) and is
--        called in the definition of merge. See [merge, proof 0b].
--
--     c) priority p1 is higher than p2. We had to prove:
--
--            Succ (l1 + (r1 + Succ (l2 + r2)))
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
--        This proof is supplied by proof1 (renamed to proof1a in
--        this module). See [merge, proof 1] for details.
--
--     d) priority p2 is higher than p1. We had to prove:
--
--            Succ (l2 + (r2  + Succ (l1 + r1)))
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
--        This proof is supplied by proof2 (renamed to proof2a in
--        this module). See [merge, proof 2] for details.
--
-- Now that we inline makeT into merge and we will have to construct
-- new proofs of merge that take into account the fact that makeT has
-- been inlinined. Let's take a detailed look into the problem and
-- analyze possible solutions.
--
-- First of all let us note that we only made calls to makeT in
-- inductive cases of merge (points 2c and 2d above). This means that
-- implementation of base cases of merge (2a and 2b above) remains
-- unchanged. Let's take a look at proofs we need to supply for each
-- of four inductive cases of merge (see [Single-pass merging
-- algorithm] for description of each case):
--
--   1) case c described in [Single-pass merging algorithm]. Call to
--      makeT would not swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            Succ (l1 + (r1 + Succ (l2 + r2)))
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
--   2) case d described in [Single-pass merging algorithm]. Call to
--      makeT would swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            Succ ((r1 + Succ (l2 + r2)) + l1)
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
--   3) case e described in [Single-pass merging algorithm]. Call to
--      makeT would not swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            Succ (l2 + (r2  + Succ (l1 + r1)))
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
--   4) case f described in [Single-pass merging algorithm]. Call to
--      makeT would swap left and right when creating a node from
--      parameters passed to it. Required proof is:
--
--            Succ ((r2 + Succ (l1 + r1)) + l2)
--                           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
-- First of all we must note that proofs required in cases 1 and 3 are
-- exactly the same as in the two-pass merging algorithm. This allows
-- us to re-use the old proofs (renamed to proof1a and proof2a
-- here). What about proofs of cases 2 and 4? One thing we could do is
-- construct proofs of these properties using technique described in
-- Note [Constructing equality proofs using transitivity]. This is
-- left as an exercise to the reader. Here we will proceed in a
-- different way. Notice that properties we have to prove in cases for
-- 2 and 4 are very similar to properties 1 and 3 (we omit the RHS
-- since it is always the same):
--
--  1: Succ (l1 + (r1 + Succ (l2 + r2)))
--  2: Succ ((r1 + Succ (l2 + r2)) + l1)
--
--  3: Succ (l2 + (r2  + Succ (l1 + r1)))
--  4: Succ ((r2 + Succ (l1 + r1)) + l2)
--
-- The only difference between 1 and 2 and between 3 and 4 is the
-- order of parameters inside the outer Succ. This is expected: in
-- cases 2 and 4 we swap left and right subtree passed to node and
-- this is reflected in the types. Now, if we could prove that:
--
--            Succ ((r1 + Succ (l2 + r2)) + l1)
--                           :~: Succ (l1 + (r1 + Succ (l2 + r2)))
--
-- and
--
--            Succ ((r2 + Succ (l1 + r1)) + l2)
--                           :~: Succ (l2 + (r2  + Succ (l1 + r1)))
--
-- then we could use transitivity to combine these new proofs with old
-- proof1a and proof2a. If we abstract the parameters in the above
-- equalities we see that the property we need to prove is:
--
--                    Succ (a + b) :~: Succ (b + a)
--
-- And that happens to be makeTlemma! New version of merge was
-- created by inlining calls to make and now it turns out we can
-- construct proofs of that implementation by using proofs of
-- makeT. This leads us to very elegant solutions presented below.


proof1a :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
           (Succ ( l1 :+ (r1 :+ Succ (l2 :+ r2)))
                     :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof1a = RP.proof1

proof1b :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
           (Succ ((r1 :+ Succ (l2 :+ r2)) :+ l1)
                     :~: (Succ ((l1 :+ r1) :+ Succ (l2 :+ r2))))
proof1b l1 r1 l2 r2 = trans (makeTlemma (r1 %:+ SSucc (l2 %:+ r2)) l1)
                            (proof1a l1 r1 l2 r2)

proof2a :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
           (Succ (l2 :+ (r2  :+ Succ (l1 :+ r1))))
                     :~: (Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof2a = RP.proof2

proof2b :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
           (Succ ((r2 :+ Succ (l1 :+ r1)) :+ l2)
                     :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof2b l1 r1 l2 r2 = trans (makeTlemma (r2 %:+ SSucc (l1 %:+ r1)) l2)
                            (proof2a l1 r1 l2 r2)

-- We can now use proof1a, proof1b, proof2a and proof2b in
-- definition of merge.
merge :: Heap l -> Heap r -> Heap (l :+ r)
merge Empty h2 = h2
merge h1 Empty = gcastWith (sym (plusZero (rank h1))) h1
merge h1@(Node p1 _ l1 r1) h2@(Node p2 _ l2 r2)
 = case (p1 < p2, order l1Rank (r1Rank %:+ h2Rank)
                , order l2Rank (r2Rank %:+ h1Rank)) of
     (True, Ge l1ger1ph2, _)  -> gcastWith
                                  (proof1a l1Rank r1Rank l2Rank r2Rank)
                                  (Node p1 l1ger1ph2 l1 (merge r1 h2))
     (True, Le l1ler1ph2, _)  -> gcastWith
                                  (proof1b l1Rank r1Rank l2Rank r2Rank)
                                  (Node p1 l1ler1ph2 (merge r1 h2) l1)
     (False, _, Ge l2ger2ph1) -> gcastWith
                                  (proof2a l1Rank r1Rank l2Rank r2Rank)
                                  (Node p2 l2ger2ph1 l2 (merge r2 h1))
     (False, _, Le l2ler2ph1) -> gcastWith
                                  (proof2b l1Rank r1Rank l2Rank r2Rank)
                                  (Node p2 l2ler2ph1 (merge r2 h1) l2)
   where l1Rank = rank l1
         r1Rank = rank r1
         l2Rank = rank l2
         r2Rank = rank r2
         h1Rank = rank h1
         h2Rank = rank h2
