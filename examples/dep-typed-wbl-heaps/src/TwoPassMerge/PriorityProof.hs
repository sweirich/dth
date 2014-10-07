-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist heap that proves to maintain priority       --
-- invariant: priority at the node is not lower than priorities of   --
-- its two children. Uses a two-pass merging algorithm.              --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module TwoPassMerge.PriorityProof where

import Basics
import qualified Basics.Nat as Nat ((>=))

-- Priority invariant says that for any node in the tree priority in
-- that node is not lower than priority stored by its children. This
-- means that any path from root to leaf is ordered (highest priority
-- at the root, lowest at the leaf). This property allows us to
-- construct an efficient merging operation (see Okasaki for more
-- details).
--
-- To prove this invariant we will index nodes using Priority. Index
-- of value n says that "this heap can store elements with priorities
-- n or lower" (remember that lower priority means larger Nat). In
-- other words Heap indexed with 0 can store any Priority, while Heap
-- indexed with 3 can store priorities 3, 4 and lower, but can't store
-- 0, 1 and 2.
--
-- As previously, Heap has two constructors:
--
--  1) Empty returns Heap n, where index n is not constrained in any
--     way. This means that empty heap can be given any restriction on
--     priorities of stored elements.
--
--  2) Node also creates Heap n, but this time n is constrained. If we
--     store priority p in a node then:
--
--       a) the resulting heap can only be restricted to store
--          priorities at least as high as p. For example, if we
--          create a node that stores priority 3 we cannot restrict
--          the resulting heap to store priorities 4 and lower,
--          because the fact that we store 3 in that node violates the
--          restriction. This restriction is expressed by the "GEq p n"
--          parameter: if we can construct a value of type (GEq p n)
--          then existence of such a value becomes a proof that p is
--          greater-equal to n. We must supply such proof to every
--          node.

--       b) children of a node can only be restricted to store
--          priorities that are not higher than p. Example: if we
--          restrict a node to store priorities 4 and lower we cannot
--          restrict its children to store priorities 3 and
--          higher. This restriction is expressed by index "p" in the
--          subheaps passed to node constructor.

data Heap :: Nat -> * where
  Empty :: Heap n
  Node  :: SNat p -- priority
        -> Rank -> GEq p n -> Heap p -> Heap p -> Heap n

-- Let's demonstrate that priority invariant cannot be broken. Imagine
-- we want to construct a heap like this:
--
--      ?
--     / \
--    /   \
--   E     0
--
-- where E means empty node and 0 means node storing Priority 0 (yes,
-- this heap violates the rank invariant!). We left out the root
-- element. The only value that can be supplied there is zero (try
-- giving one and see that typechecker will not accept it). This is
-- beacuse the value n with which 0 node can be index must obey the
-- restriction 0 >= n. This means that 0 node can only be indexed with
-- 0. When we try to construct the "?" root node we are thus only
-- allowed to insert priority 0.

-- This heap does not typecheck:
--heapBroken :: Heap Zero
--heapBroken = Node sOne two GeZ Empty (Node sZero one GeZ Empty Empty)

-- Here is a correct heap. It stores one at the leaf and 0 at the
-- root. It still violates the rank invariant - we deal with that in
-- TwoPassMerge.CombinedProofs.
heapCorrect :: Heap Zero
heapCorrect = Node sZero two GeZ Empty (Node sOne one GeZ Empty Empty)

-- Again, we need a function to extract rank from a node. Since we're
-- not verifying the rank invariant here this function is not type
-- safe in any way.
rank :: Heap b -> Rank
rank Empty            = Zero
rank (Node _ r _ _ _) = r

-- The first question is how to create a singleton heap, ie. a Heap
-- storing one element. The question we need to answer is "what
-- Priorities can we later store in a singleton Heap?". "Any" seems to
-- be a reasonable answer. This means the resulting Heap will be
-- indexed with Zero, meaning "Priorities lower or equal to zero can
-- be stored in this Heap" (remember that any priority is lower or
-- equal to zero). This leads us to following definition:
singleton :: SNat p -> Heap Zero
singleton p = Node p one GeZ Empty Empty

-- We can imagine we would like to limit the range of priorities we
-- can insert into a singleton Heap. This means the resulting Heap
-- would be index with some b (the bound on allowed Priority
-- values). In such case however we are required to supply a proof
-- that p >= b. This would lead us to a definition like this:
--
--  singletonB :: SNat p -> GEq p b -> Heap b
--  singletonB p pgeb = Node p one pgeb Empty Empty
--
-- We'll return to that idea soon.

-- makeT now returns indexed heaps, so it requires one more parameter:
-- a proof that priorities stored in resulting heap are not lower than
-- in the subheaps.
makeT :: SNat p -> GEq p b -> Heap p -> Heap p -> Heap b
makeT p pgeb l r = case rank l Nat.>= rank r of
                     True  -> Node p (Succ (rank l + rank r)) pgeb l r
                     False -> Node p (Succ (rank l + rank r)) pgeb r l

-- The important change in merge is that now we don't compare node
-- priorities using an operator that returns Bool. We compare them
-- using "order" function that not only returns result of comparison,
-- but also supplies a proof of the result. This proof tells us
-- something important about the relationship between p1, p2 and
-- priority bound of the merged Heap. Note that we use the new proof
-- to reconstruct one of the heaps that is passed in recursive call to
-- merge. We must do this because by comparing priorities p1 and p2 we
-- learned something new about restriction placed on priorities in one
-- of the heaps and we can now be more precise in expressing these
-- restrictions.
merge :: Heap p -> Heap p -> Heap p
merge Empty h2 = h2
merge h1 Empty = h1
merge (Node p1 lRank p1gep l1 r1)
      (Node p2 rRank p2gep l2 r2) = case order p1 p2 of
          Le p1lep2 -> makeT p1 p1gep l1 (merge r1 (Node p2 rRank p1lep2 l2 r2))
          Ge p1gep2 -> makeT p2 p2gep l2 (merge (Node p1 lRank p1gep2 l1 r1) r2)

-- When writing indexed insert function we once again have to answer a
-- question of how to index input and output Heap. The easiest
-- solution is to be liberal: let us require that the input and output
-- Heap have no limitations on Priorities they can store. In other
-- words, let them be indexed by Zero:
insert :: SNat p -> Heap Zero -> Heap Zero
insert p h = merge (singleton p) h

-- Now we can create an example heap. The only difference between this
-- heap and the heap without any proofs is that we are inserting
-- singletonized nat values rather than plain nats..
heap :: Heap Zero
heap = insert sTwo
      (insert sOne
      (insert sZero
      (insert sThree Empty)))

-- But what if we want to insert into a heap that is not indexed with
-- 0? One solution is to be liberal and ``promote'' that heap so that
-- after insertion it can store elements with any priorities:
toZero :: Heap b -> Heap Zero
toZero Empty              = Empty
toZero (Node p rnk _ l r) = Node p rnk GeZ l r

insert0 :: SNat p -> Heap b -> Heap Zero
insert0 p h = merge (singleton p) (toZero h)

-- But what if we actaully want to maintain bounds imposed on the heap
-- by its index? To achieve that we need a new singleton function that
-- constructs a singleton Heap with a bound equal to priority of a
-- single element stored by the heap. To construct a proof required by
-- node we use geqSym, which proves that if p :~: p then GEq p p.
singletonB :: SNat p -> Heap p
singletonB p = Node p one (geqSym p p Refl) Empty Empty

-- We can now write new insert function that uses singletonB function:
insertB :: SNat p -> Heap p -> Heap p
insertB p h = merge (singletonB p) h

-- However, that function is pretty much useless - it can insert
-- element with priority p only to a heap that has p as its bound. In
-- other words if we have Heap Zero - ie. a heap that can store any
-- possible priority -- the only thing that we can insert into it
-- using insertB function is zero. That's clearly not what we want. We
-- need a way to manipulate resulting priority bound.

-- Let's try again. This time we will write functions with signatures:
--
--  singletonB' :: SNat p -> GEq p b -> Heap b
--  insertB' :: SNat p -> GEq p b -> Heap p -> Heap b
--
-- singletonB' allows to construct Heap containing priority p but
-- bounded by b. This of course requires evidence that p >= b, ie. that
-- priority p can actually be stored in Heap b. insertB' is similar -
-- it can insert element of priority p into Heap bounded by p but the
-- resulting Heap can be bounded by b (provided that p >= b, for which
-- we must supply evidence). Let's implement that.

-- Implementing singletonB' is straightforward:
singletonB' :: SNat p -> GEq p b -> Heap b
singletonB' p pgeb = Node p one pgeb Empty Empty

-- To implement insertB' we need two additional functions. Firstly, we
-- need a proof of transitivity of GEq (>=). We proceed by induction on
-- c. Our base case is:
--
--   (GEq a b) and (GEq b 0) then (GEq a 0)
--
-- In other words if c is 0 then GeZ proves the property. If c is not
-- zero, then b is also not zero (by definitions of data constructors
-- of GEq) and hence a is also not zero. This gives us second equation
-- that is a recursive proof on geqTrans.
geqTrans :: forall a b c. GEq a b -> GEq b c -> GEq a c
geqTrans _          GeZ        = GeZ
geqTrans (GeS ageb) (GeS bgec) = GeS (geqTrans ageb bgec)
geqTrans _          _          = unreachable

-- Having proved the transitivity of GEq we can construct a function
-- that loosens the bound we put on a heap. If we have a heap with a
-- bound p - meaning that all priorities in a heap are guaranteed to
-- be lower than or equal to p - and we also have evidence than n is a
-- priority higher than p then we can change the restriction on the
-- heap so that it accepts higher priorites. For example if we have
-- Heap 5, ie. all elements in the heap are 5 or greater, and we have
-- evidence that 5 >= 3, then we can convert Heap 5 to Heap 3. Note how
-- we are prevented from writing wrong code: if we have Heap 3 we
-- cannot convert it to Heap 5. This is not possible from theoretical
-- point of viee: Heap 3 may contain 4, but Heap 5 is expected to
-- contain elements not smaller than 5. It is also not possible
-- practically: thanks to our definition of GEq we can't proivide
-- evidence that 3 >= 5 because we cannot construct value of that type.
liftBound :: GEq b p -> Heap b -> Heap p
liftBound _     Empty                = Empty
liftBound bgen (Node p rnk pgeb l r) = Node p rnk (geqTrans pgeb bgen) l r

-- With singletonB' and liftBound we can construct insertB' function
-- that allows to insert element with priority p into a Heap bound by
-- b, but only if we can supply evidence that p >= b, ie. we need
-- evidence that p can actually be stored in the heap.
insertB' :: SNat p -> GEq p b -> Heap p -> Heap b
insertB' p pgeb h = merge (singletonB' p pgeb) (liftBound pgeb h)

-- But if we try to create an example Heap as we did previously we
-- quickly discover that this function isn't of much use either:

--heap' :: Heap Zero
--heap' = insertB' sTwo GeZ
--       (insertB' sOne GeZ
--       (insertB' sZero undefined
--       (insertB' sThree GeZ Empty)))

-- In the third hole we are required to supply evidence that 0 >= 1 and
-- that is not possible. The reason is that our insertB' function
-- allows us only to insert elements into a heap in decreasing order:
heap'' :: Heap Zero
heap'' = insertB' sZero   GeZ
        (insertB' sOne    GeZ
        (insertB' sTwo   (GeS GeZ)
        (insertB' sThree (GeS (GeS GeZ)) Empty)))
-- This is a direct consequence of our requirement that priority of
-- element being inserted and bound on the Heap we insert into match.

-- Again, findMin and deletMin are incomplete
findMin :: Heap p -> Nat
findMin Empty            = undefined
findMin (Node p _ _ _ _) = fromSing p
-- We findMin however we also encounter a rather unexpected
-- obstacle. Heap stores singletonized Nats. It would be therefore
-- natural to expect that findMin function returns these singleton
-- values, for example so that we can later insert them into another
-- heap. In other words we might want to write:
--
--  findMin' :: Heap p -> SNat b
--  findMin' Empty            = undefined
--  findMin' (Node p _ _ _ _) = p
--
-- This innocently looking function would work perfectly fine in Agda
-- but will not work in Haskell. Look at the type of findMin':: Heap b -> SNat b
-- The return type is indexed with a type variable b which is
-- unrelated to the input type. It's a bit like saying:
--
--  f :: a -> b
--
-- Even though our findMin' function seems perfectly sane - after all
-- we might reasonably expect to be able to return a value stored by a
-- constructor - we are not allowed to write it. One solution would be
-- to introduce extra index to Heap only for the purpose of this
-- function, so that we could write:
--
--  findMin' :: Heap p b -> SNat b
--
-- Another apporach, taken here, is to turn a singletonized value into
-- a normal value, that is stripe it of its type information.  This
-- problem arises in Haskell because it does not have a common
-- language for types and terms.

-- deleteMin requires a bit more work than previously. First, notice
-- that the bound placed on the input and output heaps is the
-- same. This happens because relation between priorities in a node
-- and it's children is >=, not > (ie. equality is allowed). We cannot
-- therefore guearantee that bound on priority will increase after
-- removing highest-priority element from the Heap. When we merge
-- left and right subtrees we need to lift their bounds so they are
-- now both b (not p).
deleteMin :: Heap b -> Heap b
deleteMin Empty               = undefined
deleteMin (Node _ _ pgeb l r) = merge (liftBound pgeb l) (liftBound pgeb r)
