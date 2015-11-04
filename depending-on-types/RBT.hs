{-# LANGUAGE GADTs, DataKinds, KindSignatures, ExistentialQuantification, 
    TypeFamilies, StandaloneDeriving #-}


-- This module is a Haskell transliteration of RBT.agda

-- 49 lines of code for insertion (counting type defs & signatures)


module RBT where
    
-- a fixed element type for simplicity, could generalize the definitions here
data A = A1 | A2 | A3 deriving (Eq, Ord, Show)

data Color :: * where
    R :: Color
    B :: Color
 deriving Show
    
data Nat = Z | S Nat
 deriving Show

data Tree :: Color -> Nat -> * where
  E  :: Tree B Z
  TR :: Tree B n  -> A -> Tree B n  -> Tree R n 
  TB :: Tree c1 n -> A -> Tree c2 n -> Tree B (S n)
deriving instance Show (Tree c n)

-- a well-formed red-black tree. Root is black, but height 
-- could be anything.
data RBT :: * where
  Root :: Tree B m -> RBT
deriving instance Show RBT

-- example: reverse the tree
rev :: Tree c n -> Tree c n 
rev E = E
rev (TR a x b) = TR (rev b) x (rev a)
rev (TB a x b) = TB (rev b) x (rev a)

-- example: find the maximum value stored in a non-empty tree
maxB :: Tree B (S n) -> A
maxB (TB _ x E)          = x
maxB (TB _ _ (TR a x b)) = maxR (TR a x b)
maxB (TB _ _ (TB a x b)) = maxB (TB a x b)

maxR :: Tree R n -> A
maxR (TR _ x E)          = x
maxR (TR _ _ (TB a x b)) = maxB (TB a x b)

-- singleton type
data Sing (c :: Color) :: * where    
    SR :: Sing R
    SB :: Sing B
deriving instance Show (Sing c)
    
-- for insertion, sometimes we need to break the invariant.
type family Incr (c :: Color) (x :: Nat) :: Nat where
    Incr R x = x
    Incr B x = S x

-- hide the color of a non-empty tree
data HiddenTree :: Nat -> * where
  HR :: Tree R n     -> HiddenTree n
  HB :: Tree B (S n) -> HiddenTree (S n)
deriving instance Show (HiddenTree n)

-- captures the height, but not the fact that red nodes have black children
data AlmostTree :: Nat -> * where
  AT :: Sing c -> (Tree c1 n) -> A -> (Tree c2 n) -> AlmostTree (Incr c n)
deriving instance Show (AlmostTree n)

-- input color is implicitly black 
balanceLB ::  AlmostTree n -> A -> Tree c n -> HiddenTree (S n)
-- these are the two rotation cases
balanceLB (AT SR (TR a x b) y c) z d = HR (TR (TB a x b) y (TB c z d))
balanceLB (AT SR a x (TR b y c)) z d = HR (TR (TB a x b) y (TB c z d))
-- need to expand the catch-all, because the *proof* is different in each case.  
balanceLB (AT SB a  x b) kv r = HB (TB (TB a x b) kv r)
balanceLB (AT SR E x E) kv r = HB (TB (TR E x E) kv r)
balanceLB (AT SR (TB a1 x1 a2) x (TB b1 y1 b2)) y c = HB (TB (TR (TB a1 x1 a2) x (TB b1 y1 b2)) y c)
balanceLB _ _ _ = error "balanceLB: this is impossible"

-- input color is implicitly black 
balanceRB :: Tree c n -> A -> AlmostTree n -> HiddenTree (S n)
-- these are the two rotation cases
balanceRB a x (AT SR (TR b y c)  z d) = HR (TR (TB a x b) y (TB c z d))
balanceRB a x (AT SR b y (TR c z d)) = HR (TR (TB a x b) y (TB c z d))
-- catch-all 
balanceRB a x (AT SR E y E) = HB (TB a x (TR E y E))
balanceRB a x (AT SR (TB l x0 r) y (TB l' x1 r')) = HB (TB a x (TR (TB l x0 r) y (TB l' x1 r')))
balanceRB a x (AT SB l kv r) = HB (TB a x (TB l kv r))
balanceRB _ _ _ = error "balanceRB: this is impossible"


balanceLR :: HiddenTree n -> A -> Tree c n -> AlmostTree n
balanceLR (HR l) x r = AT SR l x r
balanceLR (HB l) x r = AT SR l x r

balanceRR :: Tree c n -> A -> HiddenTree n -> AlmostTree n
balanceRR l x (HR r) = AT SR l x r
balanceRR l x (HB r) = AT SR l x r

-- forget that the top node of the tree satisfies the color invariant
forget :: HiddenTree n -> AlmostTree n
forget (HR (TR l x r)) = AT SR l x r
forget (HB (TB l x r)) = AT SB l x r

insBlack :: Tree B n -> A -> HiddenTree n
insBlack E x = HR (TR E x E)
insBlack (TB l y r) x = case (compare x y) of
    LT -> balanceLB (insAny l x) y r
    GT -> balanceRB l y (insAny r x)
    EQ -> HB (TB l y r)

insAny :: Tree c n -> A -> AlmostTree n
insAny (TR l y r) x =  case compare x y of
   LT -> balanceLR (insBlack l x) y r
   GT -> balanceRR l y (insBlack r x) 
   EQ -> AT SR l y r
insAny (TB l y r) x = forget (insBlack (TB l y r) x)  
insAny E          x = forget (insBlack E x)

blacken :: AlmostTree n -> RBT
blacken (AT _ l x r) = (Root (TB l x r))

insert :: RBT -> A -> RBT
insert (Root t) x = blacken (insAny t x)

--------------------------------------------------
-- Tests:

t0 :: RBT
t0 = insert (Root E) A3

t1 :: RBT
t1 = insert t0 A1

t2 :: RBT
t2 = insert t1 A2

