-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- All the Basics/* modules are used to reinvent the wheel: booleans,--
-- natural numbers, ordering opeartors and primitives for reasoning. --
-- This module re-exports all Basics/* modules for convenience.  It  --
-- also defines two type synonyms that will be helpful when working  --
-- on heaps: Rank and Priority.                                      --
-----------------------------------------------------------------------

module Basics (
   module Basics.Bool
 , module Basics.Nat
 , module Basics.Ordering
 , module Basics.Reasoning
 , module Basics.Sing
 , module Basics.Unreachable
 , Rank, Priority
 , undefined
 ) where

import Basics.Bool
import Basics.Nat
import Basics.Ordering
import Basics.Reasoning
import Basics.Sing
import Basics.Unreachable
import Prelude (undefined)

-- Rank of a weight biased leftist heap is defined as number of nodes
-- in a heap. In other words it is size of a tree used to represent a
-- heap.
type Rank = Nat

-- Priority assigned to elements stored in a Heap.
--
-- CONVENTION: Lower number means higher Priority. Therefore the
-- highest Priority is zero. It will sometimes be more convenient not
-- to use this inversed terminology. I will then use terms "smaller"
-- and "greater" (in contrast to "lower" and "higher"). Example:
-- Priority 3 is higher than 5, but 3 is smaller than 5.
type Priority = Nat

-- Unfortunately in Haskell these synonyms are not as useful as they
-- are in Agda. The reason is that they can only be used as type
-- synonyms, but not as kind synonyms. So it is invalid to write:
--
--   data Heap :: Rank -> * where
--
-- although it is legal to do something like that in Agda.
-- See #9632 and #7961

