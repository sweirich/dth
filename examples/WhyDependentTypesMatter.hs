----------------------------------------------------------------------
--                                                                  --
-- Author  : Jan Stolarek <jan.stolarek@p.lodz.pl>                  --
-- License : Public Domain                                          --
--                                                                  --
-- This module contains Haskell implementation of code presented in --
-- "Why Dependent Types Matter" paper by Thorsten Altenkirch, Conor --
-- McBride and James McKinna. Original code in the paper was        --
-- written in Epigram but with its official web page offline        --
-- Epigram seems to be dead. I initially rewrote that code in Agda, --
-- then in Idris and now in Haskell.  Original paper elides details --
-- of some proofs. I supplied the missing parts so that the code in --
-- this module is complete and self-contained.  I assume however    --
-- that you are familiar with "Why Dependent Types Matter" paper    --
-- and thus I don't comment most of the functions.                  --
--                                                                  --
-- Note that this code is intended to demonstrate how to do         --
-- dependently-typed programming in Haskell.  It reinvents some     --
-- functions and data types present in base package shipped with    --
-- GHC 7.8.  In real life you most likely want to use library       --
-- functions instead of writing everything from scratch.  All data  --
-- types use GADT syntax even if they are ordinary ADTs.            --
--                                                                  --
-- This code was written and tested in GHC 7.8.3. It does not work  --
-- with GHC 7.6                                                     --
--                                                                  --
----------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module WhyDependentTypesMatter where

import Prelude hiding ((+), (++))

-- Section 1 : Introduction
-- ~~~~~~~~~~~~~~~~~~~~~~~~
-- Standard implementation of merge sort with no dependent types. This
-- implements code shown in the paper in Figure 1.

data Nat where
  Zero :: Nat
  Succ :: Nat -> Nat

data Order where
  Le :: Order
  Ge :: Order

data List (a :: *) where
  Nil  :: List a
  Cons :: a -> List a -> List a

order :: Nat -> Nat -> Order
order Zero      _       = Le
order (Succ _)  Zero    = Ge
order (Succ x) (Succ y) = order x y

-- deal splits a list into a pair of lists. If the input list has even length
-- then the output lists have the same length. If input has odd length then
-- first output list is longer by one.
deal :: List a -> (List a, List a)
deal Nil         = (Nil, Nil)
deal (Cons x Nil) = (Cons x Nil, Nil)
deal (Cons y (Cons z xs)) = case deal xs of
                              (ys, zs) -> (Cons y ys, Cons z zs)

merge :: List Nat -> List Nat -> List Nat
merge Nil       ys             = ys
merge xs        Nil            = xs
merge (Cons x xs) (Cons y ys) = case order x y of
                                  Le -> Cons x (merge xs (Cons y ys))
                                  Ge -> Cons y (merge (Cons x xs) ys)

sort :: List Nat -> List Nat
sort xs = case deal xs of
            (ys, Nil) -> ys
            (ys, zs) -> merge (sort ys) (sort zs)

-- Section 3.1 : Totality is Good for more than the Soul
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Here we reinvent Refl from Data.Type.Equality

data a :~: b where
  Refl :: a :~: a

-- Section 3.2 : Defusing General Recursion
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Merge sort with explicit structure of recursion.

data Parity where
  P0 :: Parity
  P1 :: Parity

data DealT (a :: *) where
  EmpT  :: DealT a
  LeafT :: a -> DealT a
  NodeT :: Parity -> DealT a -> DealT a -> DealT a

insertT :: a -> DealT a -> DealT a
insertT x  EmpT          = LeafT x
insertT x (LeafT y)      = NodeT P0 (LeafT y) (LeafT x)
insertT x (NodeT P0 l r) = NodeT P1 (insertT x l) r
insertT x (NodeT P1 l r) = NodeT P0 l (insertT x r)

dealT :: List a -> DealT a
dealT Nil = EmpT
dealT (Cons x xs) = insertT x (dealT xs)

mergeT :: DealT Nat -> List Nat
mergeT EmpT          = Nil
mergeT (LeafT x)     = Cons x Nil
mergeT (NodeT _ l r) = merge (mergeT l) (mergeT r)

-- In the paper this function is called sort. Here and in other places I rename
-- functions to avoid name clashes.
sortT :: List Nat -> List Nat
sortT xs = mergeT (dealT xs)

-- Section 4 : Maintaining Invariants by Static Indexing
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- length-indexed vectors
data Vec (a :: *) :: Nat -> * where
  VNil  ::                 Vec a Zero
  VCons :: a -> Vec a n -> Vec a (Succ n)

vtail :: Vec a (Succ n) -> Vec a n
vtail (VCons _ xs) = xs

-- I'm using @@ to denote vectorized application. In the paper this is @
(@@) :: Vec (a -> b) n -> Vec a n -> Vec b n
VNil       @@ VNil       = VNil
VCons f fs @@ VCons s ss = VCons (f s) (fs @@ ss)

infixl 9 @@

-- since we defined new data type to represent natural numbers we also need to
-- define addition over it
(+) :: Nat -> Nat -> Nat
Zero   + n = n
Succ m + n = Succ (m + n)

infixl 4 +

-- we also need a type-level addition
type family (a :: Nat) :+ (b :: Nat) :: Nat where
   Zero   :+ n = n
   Succ n :+ m = Succ (n :+ m)

-- vector addition
(++) :: Vec a n -> Vec a m -> Vec a (n :+ m)
VNil       ++ ys = ys
VCons x xs ++ ys = VCons x (xs ++ ys)

-- a singletonized Nat data type. You could generate this using the `singletons`
-- package:
--   $(genSingletons [ ''Nat ])
data SNat :: Nat -> * where
    SZero :: SNat Zero
    SSucc :: SNat n -> SNat (Succ n)

-- Here the implementation differs slightly from Agda and Idris: Haskell needs
-- explicit SNat argument. Both Agda and Idris are able to infer that argument
-- and thus it can be implicit. This refers to most of the functions you will
-- see from now on so I won't mention this again.
vec :: SNat n -> a -> Vec a n
vec SZero     x = VNil
vec (SSucc n) x = VCons x (vec n x)

-- matrix transposition
xpose :: SNat n -> SNat m -> Vec (Vec a n) m -> Vec (Vec a m) n
xpose n  SZero     VNil          =  vec n VNil
xpose n (SSucc m) (VCons xj xij) = (vec n VCons @@ xj) @@ xpose n m xij

-- Section 4.1 :: Static Indexing and Proofs
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- This section of the paper is the one that is missing some of the proofs.

vrevacc :: SNat n -> SNat m -> Vec a n -> Vec a m -> Vec a (n :+ m)
vrevacc SZero     _  VNil        ys = ys
vrevacc (SSucc m) n (VCons x xs) ys = undefined -- vrevacc m (SSucc n) xs
                                                --         (VCons x ys)
-- We can't fill in the correct code, because Haskell does not know that
-- m + (1 + n) eqauls 1 + (m + n). We have to prove it.

-- To conduct a proof we need three properties:
-- a) symmetry: if a equals b then b equals a. sym can be found in
-- Data.Type.Equality
sym :: (a :~: b) -> (b :~: a)
sym Refl = Refl

-- b) congruence: if a equals b, then (f a) equals (f b).  For the sake of
-- simplicity Haskell implementation assumes that `f` is a function on singleton
-- Nats. In general it could work on any singleton types we would have to
-- abstract singletons using a data family (see singletons library).
cong :: (SNat a -> SNat b) -> (a :~: c) -> (f a :~: f c)
cong _ Refl = Refl

-- c) substitution: if we have a proposition that is true for a and a equals b,
-- then proposition is also true for b. In other words if we can prove equality
-- of two types `a` and `b` then subst performs a type-safe cast from type
-- mentioning `a` to type mentioning `b`.
-- subst can be found in Data.Type.Equality as gcastWith
subst :: (a :~: b) -> ((a ~ b) => r) -> r
subst Refl x = x


plusSucc :: SNat a -> SNat b -> ((Succ (a :+ b)) :~: (a :+ (Succ b)))
plusSucc  SZero    _ = Refl
plusSucc (SSucc a) b = cong SSucc (plusSucc a b)

-- now that we have a proof that m + (1 + n) eqauls 1 + (m + n) we
-- can write our vrevacc function:
vrevacc2 :: SNat m -> SNat n -> Vec a m -> Vec a n -> Vec a (m :+ n)
vrevacc2  SZero    _  VNil        ys = ys
vrevacc2 (SSucc m) n (VCons x xs) ys =
  subst (sym (plusSucc m n)) (vrevacc2 m (SSucc n) xs (VCons x ys))

-- Last line corresponds to
--
--    {[plusSucc m' n⟩} vrevacc2 xs (VCons x ys)
--
-- in the paper. Call to vrevacc2 produces Vec with index n :+ (Succ m). The
-- problem is we need index Succ (n :+ m) as a result.  We have to prove their
-- equality.  We already proved with plusSucc that Succ (n + m) equals n + (Succ
-- m). Since now we're proving something opposite we make use of symmetry: we
-- apply sym to plusSucc. Having a proof is not enough - we must apply it to
-- convert from the result produced by vrevacc2 to the result expected by the
-- typechecker. To do this we use subst function.

plusZero :: SNat a -> ((a :+ Zero) :~: a)
plusZero  SZero    = Refl
plusZero (SSucc a) = cong SSucc (plusZero a)

vrev :: SNat n -> Vec a n -> Vec a n
vrev n xs = subst (plusZero n) (vrevacc2 n SZero xs VNil)

-- Section 4.2 :: Sized Merge-Sort
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- note that mergeS is a renamed merge from the paper
mergeS :: SNat n -> SNat m -> Vec Nat n -> Vec Nat m -> Vec Nat (n :+ m)
mergeS SZero _ VNil         ys   = ys
mergeS (SSucc n) SZero ys VNil =
  subst (sym (plusZero (SSucc n))) ys
mergeS (SSucc n) (SSucc m) xv@(VCons x xs) yv@(VCons y ys) =
    case order x y of
      Le -> VCons x (mergeS n (SSucc m) xs yv)
      Ge -> subst (plusSucc (SSucc n) m) (VCons y (mergeS (SSucc n) m xv ys))


-- singleton parity
data SParity a where
    SP0 :: SParity P0
    SP1 :: SParity P1

-- converting parity to Nat - term level
p2n :: Parity -> Nat
p2n P0 = Zero
p2n P1 = Succ Zero

-- converting parity to Nat - type level
type family P2N (p :: Parity) :: Nat where
    P2N P0 = Zero
    P2N P1 = Succ Zero

-- Data types and functions below have S (mnemonic for Sized) appended to their
-- name to avoid name clash.
data DealTS a :: Nat -> * where
  EmpTS  :: DealTS a Zero
  LeafTS :: a -> DealTS a (Succ Zero)
  NodeTS :: SNat n -> SParity p -> DealTS a (P2N p :+ n) -> DealTS a n
         -> DealTS a ((P2N p :+ n) :+ n)

-- We already defined term-level and type-level addition for Nats. It turns out
-- we now need more boilerplate: term-level addition on singleton Nats. This
-- will be used below.
(%:+) :: SNat a -> SNat b -> SNat (a :+ b)
SZero     %:+ m = m
(SSucc n) %:+ m = SSucc (n %:+ m)

-- and while we're at it, we also need conversion from parity to nat on
-- singleton types.
sP2N :: SParity p -> SNat (P2N p)
sP2N SP0 = SZero
sP2N SP1 = SSucc SZero

mergeTS :: DealTS Nat n -> Vec Nat n
mergeTS EmpTS            = VNil
mergeTS (LeafTS x)       = VCons x VNil
mergeTS (NodeTS n p l r) = mergeS (sP2N p %:+ n) n (mergeTS l) (mergeTS r)

insertTS :: a -> DealTS a n -> DealTS a (Succ n)
insertTS x EmpTS              = LeafTS x
insertTS x (LeafTS y        ) = NodeTS (SSucc SZero) SP0 (LeafTS y) (LeafTS x)
insertTS x (NodeTS n SP0 l r) = NodeTS (sP2N SP0 %:+ n) SP1 (insertTS x l) r
insertTS x (NodeTS n SP1 l r) =
  subst (sym (cong SSucc (plusSucc n n))) (NodeTS (sP2N SP1 %:+ n) SP0 l
                                                  (insertTS x r))
--       |    |           |
--       |    |           +---- Succ (n + n) :~: n + Succ n
--       |    +---------------- Succ (Succ (n + n)) :~: Succ (n + Succ n))
--       +--------------------- Succ (n + Succ n))  :~: Succ (Succ (n + n))
--
-- It took me a while to figure out this proof (though in retrospect it is
-- simple). The expected size of the resulting vector is:
--
--   Succ (Succ (n + n))
--
-- First Succ comes from the type signature of insertTS, second Succ comes from
-- sP2N SP1 (which is Succ Zero), and n + n comes from NodeTS definition. The
-- actual size produced by recursive call to NodeTS is:
--
--   Succ (n + Succ n))
--
-- Outer Succ comes from type signature, n is size of l, Succ n is size of new r
-- (ie. r with x inserted into it).

dealTS :: Vec a n -> DealTS a n
dealTS VNil         = EmpTS
dealTS (VCons x xs) = insertTS x (dealTS xs)

sortTS :: Vec Nat n -> Vec Nat n
sortTS xs = mergeTS (dealTS xs)

-- Section 5.1 :: Evidence of Ordering
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

data LEq :: Nat -> Nat -> * where
  LeZ :: LEq Zero y
  LeS :: LEq x y -> LEq (Succ x) (Succ y)

data OrderD :: Nat -> Nat -> * where
  LeD :: LEq x y -> OrderD x y
  GeD :: LEq y x -> OrderD x y

orderD :: SNat x -> SNat y -> OrderD x y
orderD SZero      y        = LeD LeZ
orderD (SSucc x)  SZero    = GeD LeZ
orderD (SSucc x) (SSucc y) = case orderD x y of
                               LeD xley -> LeD (LeS xley)
                               GeD ylex -> GeD (LeS ylex)

leRefl :: SNat x -> LEq x x
leRefl SZero     = LeZ
leRefl (SSucc n) = LeS (leRefl n)

leTrans :: LEq x y -> LEq y z -> LEq x z
leTrans LeZ       yz      = LeZ
leTrans (LeS xy) (LeS yz) = LeS (leTrans xy yz)

leASym :: LEq x y -> LEq y x -> x :~: x
leASym  LeZ      LeZ     = Refl
leASym (LeS xy) (LeS yx) = Refl

-- Second equation for leASym is surprisingly simple. I admit I don't fully
-- understand why I could simply use refl here, without doing inductive proof.

-- Section 5.2 :: Locally Sorted Lists
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- LNat = Nat lifted with infinity
data LNat where
  LZero :: LNat
  LSucc :: LNat -> LNat
  LInf  :: LNat

type family Lift (a :: Nat) :: LNat where
    Lift  Zero    = LZero
    Lift (Succ x) = LSucc (Lift x)

-- In the paper ≤ is used for comparisons on lifted Nats. I'm using LLEq for
-- this.
data LLEq :: LNat -> LNat -> * where
  LLeZ :: LLEq LZero y
  LLeS :: LLEq x y -> LLEq (LSucc x) (LSucc y)
  LLeI :: LLEq x LInf

data CList :: LNat -> * where
  CNil  :: CList LInf
  CCons :: SNat x -> LLEq (Lift x) y -> CList y -> CList (Lift x)
--                   |
--              +----+
--              +--> Paper compares lifted and unlifted Nat using ≤.
--                   This seems incorrect or at least unprecise.

-- The problem with CList is that we can't create it if we don't know the least
-- element. That's why the paper says sort is bound by min.
clist :: CList LZero
clist = CCons SZero LLeZ (
        CCons (SSucc (SSucc SZero)) (LLeS (LLeS LLeZ)) (
        CCons (SSucc (SSucc SZero))  LLeI CNil))

data OList :: Nat -> * where
  ONil  :: OList b
  OCons :: SNat x -> LEq b x -> OList x -> OList b

-- With OList we can just create a list by saying it is bound by Zero.
olist :: OList Zero
olist = OCons (SSucc SZero) LeZ ONil

olist2 :: OList Zero
olist2 = OCons (SSucc SZero) LeZ (OCons (SSucc (SSucc SZero)) (LeS LeZ) ONil)

mergeO :: OList b -> OList b -> OList b
mergeO ONil ys = ys
mergeO (OCons x blex xs) ONil = OCons x blex xs
mergeO (OCons x blex xs) (OCons y bley ys) =
    case orderD x y of
      LeD xley -> OCons x blex (mergeO xs (OCons y xley ys))
      GeD ylex -> OCons y bley (mergeO (OCons x ylex xs) ys)

-- The important thing here is that both lists passed to mergeO must share their
-- lower bound. That's why we have to replace old evidence of ordering (bley in
-- the first case) with the new one (xley).

-- Note that both functions require that input data structure stores singleton
-- types. This does not seem very practical - in real life we would most likely
-- want the lists to store normal values. The problem is that we can't just
-- promote normal term-level values to singletons.
mergeTO :: DealT (SNat a) -> OList Zero
mergeTO EmpT          = ONil
mergeTO (LeafT x)     = OCons x LeZ ONil
mergeTO (NodeT p l r) = mergeO (mergeTO l) (mergeTO r)

sortO :: List (SNat a) -> OList Zero
sortO xs = mergeTO (dealT xs)
