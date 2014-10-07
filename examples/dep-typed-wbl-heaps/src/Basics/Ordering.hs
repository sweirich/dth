-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Definition of datatypes that represent ordering and functions     --
-- that operate on them. These datatypes are based on ideas          --
-- introduced in "Why Dependent Types Matter".                       --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
module Basics.Ordering where

import Basics.Nat

-- The GEq type is a proof of greater-equal relation between two
-- natural numbers. It proves that: a) any natural number is greater
-- or equal to zero and b) any two natural numbers are in
-- greater-equal relation if their predecessors are also in that
-- relation.
data GEq :: Nat -> Nat -> * where
  GeZ :: GEq y Zero
  GeS :: GEq x y -> GEq (Succ x) (Succ y)

-- Order datatype tells whether two numbers are in greater-equal
-- relation or not. In that sense it is an equivalent of a Bool
-- datatype. Unlike Bool however, Order supplies a proof of WHY the
-- numbers are (or are not) in the relation.
data Order :: Nat -> Nat -> * where
  Ge :: GEq x y -> Order x y
  Le :: GEq y x -> Order x y

-- order function takes two natural numbers and compares them,
-- returning the result of comparison together with a proof of the
-- result encoded by Order datatype.  This function operates on
-- singletonized Nats because we want to relate things happening at
-- the term level with the type level.
order :: SNat a -> SNat b -> Order a b
order  _         SZero    = Ge GeZ
order  SZero    (SSucc _) = Le GeZ
order (SSucc a) (SSucc b) = case order a b of
                              Ge ageb -> Ge (GeS ageb)
                              Le bgea -> Le (GeS bgea)
