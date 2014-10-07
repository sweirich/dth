-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Basic implementation of weight-biased leftist heap. No proofs     --
-- and no dependent types. Uses a two-pass merging algorithm.        --
-----------------------------------------------------------------------

{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE NoImplicitPrelude    #-}
module TwoPassMerge.NoProofs where

import Basics.Nat
import Basics

data Heap :: * where
  Empty :: Heap
  Node  :: Priority -> Rank -> Heap -> Heap -> Heap

-- Returns rank of node.
rank :: Heap -> Nat
rank Empty          = Zero
rank (Node _ r _ _) = r

-- Creates heap containing a single element with a given Priority
singleton :: Priority -> Heap
singleton p = Node p one Empty Empty

-- Note [Two-pass merging algorithm]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- We use a two-pass implementation of merging algorithm. One pass,
-- implemented by merge, performs merging in a top-down manner. Second
-- one, implemented by makeT, ensures that rank invariant of weight
-- biased leftist tree is not violated after merging.
--
-- Notation:
--
--  h1, h2 - heaps being merged
--  p1, p2 - priority of root element in h1 and h2
--  l1     - left  subtree in the first  heap
--  r1     - right subtree in the first  heap
--  l2     - left  subtree in the second heap
--  r2     - right subtree in the second heap
--
-- Merge function analyzes four cases. Two of them are base cases:
--
--    a) h1 is empty - return h2
--
--    b) h2 is empty - return h1
--
-- The other two cases form the inductive definition of merge:
--
--    c) priority p1 is higher than p2 - p1 becomes new root, l1
--       becomes its one child and result of merging r1 with h2
--       becomes the other child:
--
--               p1
--              /  \
--             /    \
--            l1  r1+h2 -- here "+" denotes merging
--
--    d) priority p2 is higher than p2 - p2 becomes new root, l2
--       becomes its one child and result of merging r2 with h1
--       becomes the other child.
--
--               p2
--              /  \
--             /    \
--            l2  r2+h1
--
-- Note that there is no guarantee that rank of r1+h2 (or r2+h1) will
-- be smaller than rank of l1 (or l2). To ensure that merged heap
-- maintains the rank invariant we pass both childred - ie. either l1
-- and r1+h2 or l2 and r2+h1 - to makeT, which creates a new node by
-- inspecting sizes of children and swapping them if necessary.

-- makeT takes an element (Priority) and two heaps (trees). It
-- constructs a new heap with element at the root and two heaps as
-- children. makeT ensures that WBL heap rank invariant is maintained
-- in the newly created tree by reversing left and right subtrees when
-- necessary (note the inversed r and l in the False alternative of
-- case expression).
makeT :: Priority -> Heap -> Heap -> Heap
makeT p l r = case rank l >= rank r of
                True  -> Node p (Succ (rank l + rank r)) l r
                False -> Node p (Succ (rank l + rank r)) r l

-- merge combines two heaps into one. There are two base cases and two
-- recursive cases - see [Two-pass Merging algorithm]. Recursive cases
-- call makeT to ensure that rank invariant is maintained after
-- merging.
merge :: Heap -> Heap -> Heap
merge Empty h2 = h2
merge h1 Empty = h1
merge h1@(Node p1 _ l1 r1) h2@(Node p2 _ l2 r2) = case p1 < p2 of
  True  -> makeT p1 l1 (merge r1 h2)
  False -> makeT p2 l2 (merge h1 r2)

-- Inserting into a heap is performed by merging that heap with newly
-- created singleton heap.
insert :: Priority -> Heap -> Heap
insert p h = merge (singleton p) h

-- findMin returns element with highest priority, ie. root
-- element. Here we encounter first serious problem: we can't return
-- anything sensible for empty node.
findMin :: Heap -> Priority
findMin Empty          = undefined
findMin (Node p _ _ _) = p

-- alternatively, we can invent Maybe
data Maybe (a :: *) :: * where
  Nothing :: Maybe a
  Just    :: a -> Maybe a

-- and write a safer version of findMinM
findMinM :: Heap -> Maybe Priority
findMinM Empty          = Nothing
findMinM (Node p _ _ _) = Just p

-- deleteMin removes the element with the highest priority by merging
-- subtrees of a root element. Again the case of empty heap is
-- problematic. We could give it semantics by returning Empty, but
-- this just doesn't feel right. Why should we be able to remove
-- elements from an empty heap?
deleteMin :: Heap -> Heap
deleteMin Empty          = undefined -- should we insert empty?
deleteMin (Node _ _ l r) = merge l r

-- As a quick sanity check let's construct some examples. Here's a
-- heap constructed by inserting following priorities into an empty
-- heap: 3, 0, 1, 2.
heap :: Heap
heap = insert two
      (insert one
      (insert zero
      (insert three Empty)))

-- Example usage of findMin
findMinInHeap :: Priority
findMinInHeap = findMin heap

-- Example usage of deleteMin
deleteMinFromHeap :: Heap
deleteMinFromHeap = deleteMin heap
