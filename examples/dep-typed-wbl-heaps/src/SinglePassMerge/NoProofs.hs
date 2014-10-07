-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Basic implementation of weight-biased leftist heap. No proofs     --
-- and no dependent types. Uses a single-pass merging algorithm.     --
--                                                                   --
-- Now we will modify our implementation by turning a two-pass       --
-- merging algorithm into a single-pass one. We will do this by      --
-- inlining makeT into merge. See [Single-pass merging algorithm]    --
-- for a detailed description of new algorithm. Since merge          --
-- function will be the only thing that changes we will not repeat   --
-- singleton, findMin and deleteMin functions - they are exactly the --
-- same as they were in case of two-pass merging algorithm. All      --
-- data declaration also remain the same. We will focus our          --
-- attention on merging.                                        --
-----------------------------------------------------------------------

{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
module SinglePassMerge.NoProofs where

import Basics

data Heap :: * where
  Empty :: Heap
  Node  :: Priority -> Rank -> Heap -> Heap -> Heap

-- Note [Single-pass merging algorithm]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- New single-pass merging algorithm is a straightfowrward derivation
-- from two-pass merge. We obtain this new algorithm by inlining calls
-- to makeT. This means that merge creates a new node instead of
-- delegating this task to makeT. The consequence of this is that
-- merge has two more cases now (a total of six). Base cases remain
-- unchanged (we use the same notation as in [Two-pass merging
-- algorithm]:
--
--    a) h1 is empty - return h2
--
--    b) h2 is empty - return h1
--
-- There are two more cases in the inductive part of merge definition:
--
--    c) priority p1 is higher than p2 AND rank of l1 is not smaller
--       than rank of r1 + h2 - p1 becomes the root, l1 becomes the
--       left child and result of merging r1 with h2 becomes the right
--       child child.
--
--               p1
--              /  \
--             /    \
--            l1  r1+h2
--
--    d) priority p1 is higher than p2 AND rank of r1 + h2 is not
--       smaller than rank of l1 - p1 becomes the root, result of
--       merging r1 with h2 becomes the left child and l1 becomes the
--       right child child.
--
--               p1
--              /  \
--             /    \
--           r1+h2  l1
--
--    e) priority p2 is higher than p1 AND rank of l2 is not smaller
--       rank of r2 + h1 - p2 becomes the root, l2 becomes the left
--       child and result of merging r2 with h1 becomes the right
--       child child.
--
--               p2
--              /  \
--             /    \
--            l2  r2+h1
--
--    f) priority p2 is higher than p1 AND rank of r2 + h1 is not
--       smaller than rank of l2 - p2 becomes the root, result of
--       merging r2 with h1 becomes the left child and l2 becomes the
--       right child child.
--
--               p2
--              /  \
--             /    \
--           r2+h1  l2

-- We still use a helper function to get rank of a node
rank :: Heap -> Nat
rank Empty          = Zero
rank (Node _ r _ _) = r

-- Note [Compacting merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~
--
-- To make implementation of merge slighty shorter we check which
-- priority is higher and at the same time we compute relation between
-- ranks of new possible subtrees (l1, r1 + h2 and l2, r2 + h1).
-- Depending on result of comparing p1 with p2 we will only need to
-- know one of this relations:
--
--   1) if priority p1 is higher than p2 then we need to know whether
--      l1 >= r1 + h2
--
--   2) if priority p2 is higher than p1 then we need to know whether
--      l2 >= r2 + h1

merge :: Heap -> Heap -> Heap
merge Empty h2 = h2 -- See [Single-pass merging algorithm]
merge h1 Empty = h1
merge h1@(Node p1 w1 l1 r1) h2@(Node p2 w2 l2 r2) =
    case (p1 < p2, rank l1 >= rank r1 + w2, rank l2 >= rank r2 + w1) of
         (True , True , _    ) -> Node p1 (w1 + w2) l1 (merge r1 h2)
         (True , False, _    ) -> Node p1 (w1 + w2) (merge r1 h2) l1
         (False, _    , True ) -> Node p2 (w1 + w2) l2 (merge r2 h1)
         (False, _    , False) -> Node p2 (w1 + w2) (merge r2 h1) l2
