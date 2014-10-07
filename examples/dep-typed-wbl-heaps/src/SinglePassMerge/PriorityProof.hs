-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist heap that proves to maintain priority       --
-- invariant and uses a single-pass merging algorithm.               --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module SinglePassMerge.PriorityProof where

import Basics

data Heap :: Nat -> * where
  Empty :: Heap n
  Node  :: SNat p -> Rank -> GEq p n -> Heap p -> Heap p -> Heap n

rank :: Heap b -> Rank
rank Empty            = Zero
rank (Node _ r _ _ _) = r

-- This implementation is derived in the same way as merge in
-- SinglePassMerge.NoProofs: depending on the size of new children we
-- swap parameters passed to Node. We also use `order` function to
-- supply evidence that the rank invariant holds, just as we did in
-- the two-pass merge algorithm.
merge :: Heap p -> Heap p -> Heap p
merge Empty h2 = h2
merge h1 Empty = h1
merge (Node p1 lRank p1gep l1 r1) (Node p2 rRank p2gep l2 r2) =
  case (order p1 p2, rank l1 >= rank r1 + rRank, rank l2 >= rank r2 + lRank ) of
    (Le p1lep2, True , _) -> Node p1 (lRank + rRank) p1gep
                                  l1 (merge r1 (Node p2 rRank p1lep2 l2 r2))
    (Le p1lep2, False, _) -> Node p1 (lRank + rRank) p1gep
                                  (merge r1 (Node p2 rRank p1lep2 l2 r2)) l1
    (Ge p2lep1, _, True ) -> Node p2 (lRank + rRank) p2gep
                                  l2 (merge (Node p1 lRank p2lep1 l1 r1) r2)
    (Ge p2lep1, _, False) -> Node p2 (lRank + rRank) p2gep
                                  (merge (Node p1 lRank p2lep1 l1 r1) r2) l2

