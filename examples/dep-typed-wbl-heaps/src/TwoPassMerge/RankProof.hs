-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Weight biased leftist heap that proves rank invariant: size of    --
-- left subtree of a node is not smaller than size of right          --
-- subtree. Uses a two-pass merging algorithm.                       --
-----------------------------------------------------------------------

{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE NoImplicitPrelude   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
module TwoPassMerge.RankProof where

import Basics

-- To prove the rank invariant we will index each Heap by its size,
-- (remember that size and rank of a heap are the same). Therefore
-- index of value n says that a Heap stores n elements. When merging
-- two heaps we will use the index to ensure that rank invariant is
-- maintained.
--
-- Again, Heap has two constructor:
--
--  1) Empty constructs a Heap containing no elements. Therefore the
--     index is 0.
--
--  2) Node takes two subtrees: one containing l elements, the other
--     containing r elements. The size of resulting heap is the sum of
--     l and r plus one for the element stored by the node itself. To
--     enforce the rank invariant node constructor expects a proof
--     that invariant holds: a value of type GEq l r. If we can
--     construct value of this type then it proves the invariant.
data Heap :: Nat -> * where
  Empty :: Heap Zero
  Node  :: Priority -> GEq l r -> Heap l -> Heap r -> Heap (Succ (l :+ r))

-- Returns rank of node. Here we have a significant difference between
-- Haskell and a fully-fledged dependently-typed languages. Heap is
-- indexed by a rank, which means that in a dependenty typed language
-- we could simply pattern-match on the index. In Haskell we need to
-- explicitly calculate the rank. Since the result is a singleton we
-- at least get the guarantee that the computed size is correct (note
-- how Heap and resulting SNat have the same type variable).
rank :: Heap l -> SNat l
rank Empty          = SZero
rank (Node _ _ l r) = SSucc (rank l %:+ rank r)

-- Singleton heap stores only one element. Therefore it has size of
-- one. To prove the rank invariant we must show that 0 >= 0. We
-- construct a value of this type using GeZ constructor.
singleton :: Priority -> Heap One
singleton p = Node p GeZ Empty Empty

-- Note [Proving rank invariant (merge using makeT)]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Proving the rank invariant itself is surprisingly simple. We just
-- need to supply evidence that rank of left subtree is not smaller
-- than rank of right subtree. We can easily obtain that evidence by
-- using order function which returns result of comparing two natural
-- numbers (which will be tree ranks in this case) together with a
-- proof of the result.
--
-- But there is a different difficulty here. Since we index heaps by
-- their size we now require that makeT and merge construct trees of
-- correct size. Prooving this requires some substantial work on our
-- side.
--
-- We need to prove that the size of merged heap is equal to the sum
-- of sizes of heaps being merged. Recall that our merging algorithm
-- is two pass: we use merge to actually do the merging and makeT to
-- restore the rank invariant if necessary (see Note [Two-pass merging
-- algorithm]). This means our proof will be two-stage. We need to
-- prove that:
--
--  1) makeT creates a node of required size, even if it swaps left
--     and right children.
--
--  2) recursive calls to merge produce heaps of required size.

-- Note [Proving makeT]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- makeT takes two subtrees of size l and r and produces a new tree of
-- size 1 + l + r. We must prove that each of two cases of makeT
-- returns tree of correct size:
--
--  1) size of l is >= than size of r: no extra proof is necessary as
--     everything follows from the definition of +.
--
--  2) size of r is >= than size of l: in this case we swap left and
--     right subtrees. This requires us to prove that:
--
--       Succ (r + l) :~: Succ (l + r)
--
--     That proof is done using congruence on SSucc function and
--     commutativity of addition. We will define that proof as
--     makeTlemma as we will be using in subsequent proofs.

makeTlemma :: SNat a -> SNat b -> (Succ (a :+ b)) :~: (Succ (b :+ a))
makeTlemma a b = cong SSucc (plusComm a b)

makeT :: SNat l -> SNat r -> Priority -> Heap l -> Heap r -> Heap (Succ (l :+ r))
makeT lRank rRank p l r = case order lRank rRank of
  Ge lger -> Node p lger l r
  Le rgel -> gcastWith (makeTlemma rRank lRank) (Node p rgel r l)


-- Note [Notation for proving heap merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- In the proofs of heap merge we will use following notation:
--
--  h1, h2 - rank of heaps being merged
--  p1, p2 - priority of root element
--  l1     - rank of left  subtree in the first  heap
--  r1     - rank of right subtree in the first  heap
--  l2     - rank of left  subtree in the second heap
--  r2     - rank of right subtree in the second heap
--
-- Note that:
--
--    h1 = Succ (l1 + r1)
--    h2 = Succ (l2 + r2)
--
--     h1         h2
--
--     p1         p2
--    /  \       /  \
--   /    \     /    \
--  l1    r1   l2    r2


-- Note [Proving merge]
-- ~~~~~~~~~~~~~~~~~~~~
--
-- We need to prove that all four cases of merge (see [Two-pass merging
-- algorithm]) produce heap of required size, which is h1 + h2. Since
-- in the proofs we will mostly operate on l1, r1, l2 and r2 we have:
--
--   h1 + h2 ̄:~: Succ (l1 + r1) + Succ (l2 + r2)
--           :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
-- (Second transformation comes from definition of +). This is the
-- size expected by the typechecker and therefore the final result we
-- must prove in every case that we analyze.

-- It is best to study the implementation of merge now and then read
-- the explanation of proofs.

-- Note [merge, proof 0a]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h1 :~: 0, therefore: h1 + h2 :~: 0 + h2 :~: h2
--
-- This is definitional equality based on +
--
-- QED

-- Note [merge, proof 0b]
-- ~~~~~~~~~~~~~~~~~~~~~~
--
-- h2 :~: 0, therefore expected size is h1 + h2 :~: h1 + 0. We need to
-- show that:
--
--    h1 :~: h1 + 0
--
-- This is a simple statement that 0 is right identity of addition. We
-- proved that as one of basic properties of addition in
-- Basics.Reasoning module, except that our proof had the sides of
-- equality reversed, ie. we proved a + 0 :~: a, not a :~: a + 0. We
-- use symmetry to construct a proof of latter from the former.
--
-- QED

-- Note [merge, proof 1]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p1 < p2. We keep p1 as the root and need to prove that
-- merging r1 with h2 gives correct size.  Here's how the term that
-- performs the merge corresponds to its type:
--
--   makeT l1Rank (r1Rank %:+ h2Rank) p1 l1 (merge r1 h2)
--    |                                   |         |  |
--    |   +-------------------------------+         |  |
--    |   |     +-----------------------------------+  |
--    |   |     |             +------------------------+
--    |   |     |     ________|__
--    |   |     |    /           \
--  Succ (l1 + (r1 + Succ (l2 + r2)))
--
-- Formally:
--
--   Succ (l1 + (r1 + Succ (l2 + r2))) :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
-- Recall that RHS of this equality comes from [Proving merge]. We
-- begin proof with congruence on Succ:
--
--   cong SSucc X
--
-- where X proves
--
--   l1 + (r1 + Succ (l2 + r2)) :~: (l1 + r1) + Succ (l2 + r2)
--
-- Substituting a = l1, b = r1 and c = Succ (l2 + r2) we have
--
--   a + (b + c) :~: (a + b) + c
--
-- Which is associativity of addition that we have already proved in
-- Basics.Reasoning. We thus refer to plusAssoc to finish our proof.
--
-- QED

proof1 :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
          (Succ ( l1 :+ (r1 :+ Succ (l2 :+ r2)))
                    :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2)))
proof1 l1 r1 l2 r2 = cong SSucc (plusAssoc l1 r1 (SSucc (l2 %:+ r2)))

-- Note [merge, proof 2]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- We have p2 < p1. We keep p2 as the root and need to prove that
-- merging r2 with h1 gives correct size. Again, here's the
-- corespondence between the term and its type:
--
--   makeT l2Rank (r2Rank %:+ h1Rank) p2 l2 (merge r2 h1)
--    |                                   |         |  |
--    |   +-------------------------------+         |  |
--    |   |     +-----------------------------------+  |
--    |   |     |             +------------------------+
--    |   |     |     ________|__
--    |   |     |    /           \
--  Succ (l2 + (r2 + Succ (l1 + r1)))
--
-- Formally:
--
--   Succ (l2 + (r2 + Succ (l1 + r1))) :~: Succ ((l1 + r1) + Succ (l2 + r2))
--
-- Again we use cong to deal with the outer calls to Succ and
-- substitute a = l2, b = r2 and c = l1 + r1. This leaves us with a
-- proof of lemma A:
--
--   a + (b + Succ c) :~: c + Succ (a + b)
--
-- From associativity we know that:
--
--   a + (b + Succ c) :~: (a + b) + Succ c
--
-- If we prove lemma B:
--
--  (a + b) + Succ c = c + Succ (a + b)
--
-- we can combine it with lemma A using transitivity to get the final
-- proof. We can rewrite lemma B as:
--
--   n + Succ m :~: m + Succ n
--
-- where n = a + b and m = c. From symmetry of plusSucc we have:
--
--   n + (Succ m) :~: Succ (n + m)
--
-- Using transitivity we combine it with congruence on commutativity
-- of addition to prove:
--
--   Succ (n + m) :~: Succ (m + n)
--
-- Again, using transitivity we combine it with plusSucc:
--
--   Succ (m + n) :~: m + Succ n
--
-- Which proves lemma B and therefore the whole proof is complete.
--
-- QED

lemmaB :: SNat n -> SNat m -> ((n :+ Succ m) :~: (m :+ Succ n))
lemmaB n m = trans (sym (plusSucc n m)) (trans (cong SSucc (plusComm n m))
                                               (plusSucc m n))

lemmaA :: SNat a -> SNat b -> SNat c ->
          ((a :+ (b :+ Succ c)) :~: (c :+ Succ (a :+ b)))
lemmaA a b c = trans (plusAssoc a b (SSucc c)) (lemmaB (a %:+ b) c)

proof2 :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
          Succ (l2 :+ (r2  :+ Succ (l1 :+ r1)))
                :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2))
proof2 l1 r1 l2 r2 = cong SSucc (lemmaA l2 r2 (l1 %:+ r1))

-- Note [Constructing equality proofs using transitivity]
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
--
-- Now that constructed two specific proofs we can focus on a more
-- general technique used in both cases. Let's rewrite proof2 in a
-- different fassion to see closely what is happening at each
-- step. Inlining lemmas A and B into proof2 gives:
--
--   proof2i :: SNat l1 -> SNat r1 -> SNat l2 -> SNat r2 ->
--          Succ (l2 :+ (r2  :+ Succ (l1 :+ r1)))
--                :~: Succ ((l1 :+ r1) :+ Succ (l2 :+ r2))
--   proof2i l1 r1 l2 r2 =
--     cong SSucc (trans (plusAssoc l2 r2 (SSucc (l1 :%+ r1)))
--                (trans (sym (plusSucc (l2 :%+ r2) (l1 :%+ r1)))
--                (trans (cong Succ (plusComm (l2 :%+ r2) (l1 :%+ r1)))
--                       (plusSucc (l1 :%+ r1) (l2 :%+ r2))))
--
-- We see a lot of properties combined using transitivity. In general,
-- if we have to prove:
--
--   a :~: e
--
-- and we can prove:
--
--   a :~: b, b :~: c, c :~: d, d :~: e
--
-- then we can combine these proofs using transitivity:
--
--   trans (a :~: b) (trans (b :~: c) (trans (c :~: d) (d :~: e)))
--
-- While simple to use, combining proofs with transitivity can be not
-- so obvious at first. Let's rewrite the proof we have conducted
-- using following notation:
--
--  a :~:[ proof 1 ]
--  b :~:[ proof 2 ]
--  c :~:[ proof 3 ]
--  d :~:[ proof 4 ]
--  e QED
--
-- Where proof 1 proves a :~: b, proof 2 proves b :~: c and so on. In our
-- particular case this will be:
--
--  Succ  (l2 + (r2 + Succ (l1 + r1))) :~:[ cong SSucc ]
-- [Succ]  l2 + (r2 + Succ (l1 + r1))  :~:[ plusAssoc l2 r2 (Succ (l1 :%+ r1))]
-- [Succ] (l2 + r2) + Succ (l1 + r1)   :~:[ sym (plusSucc (l2 :%+ r2) (l1 :%+ r1))]
-- [Succ] Succ ((l2 + r2) + (l1 + r1)) :~:[ cong SSucc (plusComm (l2 :%+ r2) (l1 :%+ r1)) ]
-- [Succ] Succ ((l1 + r1) + (l2 + r2)) :~:[ plusSucc (l1 :%+ r1) (l2 :%+ r2) ]
-- [Succ] (l1 + r1) + Succ (l2 + r2) QED
--
-- We use [Succ] to denote that everything happens under a call to Succ
-- (using congruence). Compare this notation with code of proof-2i.


-- Note [Notation in merge]
-- ~~~~~~~~~~~~~~~~~~~~~~~~
--
-- merge uses different notation than the proofs above. We use l1, r1, l2
-- and r2 to denote the respective subtrees and l1Rank, r1Rank,
-- l2Rank and r2Rank to denote their ranks. We use h1 and h2 to
-- denote heaps.
merge :: Heap l -> Heap r -> Heap (l :+ r)
merge  Empty h2 = h2 -- See [merge, proof 0a]
merge h1 Empty
  = gcastWith (sym (plusZero (rank h1))) h1 -- See [merge, proof 0b]
merge h1@(Node p1 _ l1 r1)
      h2@(Node p2 _ l2 r2) = case p1 < p2 of
         True -> gcastWith
             (proof1 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 1]
             (makeT l1Rank (r1Rank %:+ h2Rank) p1 l1 (merge r1 h2))
         False -> gcastWith
             (proof2 l1Rank r1Rank l2Rank r2Rank) -- See [merge, proof 2]
             (makeT l2Rank (r2Rank %:+ h1Rank) p2 l2 (merge r2 h1))
      where l1Rank = rank l1
            r1Rank = rank r1
            l2Rank = rank l2
            r2Rank = rank r2
            h1Rank = rank h1
            h2Rank = rank h2

-- We require that inserting an element into the heap increases its
-- size by one. As previously we define insert as merge with a
-- singleton heap. Size of singleton heap is (Succ Zero), while already
-- existing heap has size n. According to definition of merge the
-- resulting heap will therefore have size:
--
--   (Succ Sero) + n
--
-- By definition of + this can be normalized to:
--
--   Succ (Sero + n)
--
-- and finally to
--
--   Succ n
--
-- Which is the size we require in the type signature. This means we
-- don't need any additional proof because expected result follows
-- from definitions.
insert :: Priority -> Heap n -> Heap (Succ n)
insert p h = merge (singleton p) h

-- By indexing heap with its size we finally have means to ensure
-- that heap passed to findMin or deleteMin is not empty.
findMin :: Heap (Succ n) -> Priority
findMin (Node p _ _ _) = p


deleteMin :: Heap (Succ n) -> Heap n
deleteMin (Node _ _ l r) = merge l r
