{-# LANGUAGE GADTs, DataKinds, KindSignatures, ExistentialQuantification, 
    TypeFamilies #-}

-- This module is a Haskell transliteration of RBT.agda

{-# OPTIONS -fwarn-incomplete-patterns #-}
{- Note that this code produces two warnings because GHC cannot tell that the 
branches are inaccessible. (But adding the branches produces a type error!)

/Users/sweirich/vc/dth/icfp14/RBT.hs:62:1: Warning:
    Pattern match(es) are non-exhaustive
    In an equation for ‘balanceL’:
        Patterns not matched:
            (AT SR E _ (TB _ _ _)) _ _
            (AT SR (TB _ _ _) _ E) _ _

and similar for balanceR. 

-}

module RBT where
    
-- a fixed element type for simplicity, could generalize the definitions here
data A = A1 | A2 | A3 deriving (Eq, Ord)

data Color :: * where
    R :: Color
    B :: Color
    
data Nat = Z | S Nat

data Tree :: Color -> Nat -> * where
  E  :: Tree B Z
  TR :: (Tree B n)  -> A -> (Tree B n)  -> Tree R n 
  TB :: (Tree c1 n) -> A -> (Tree c2 n) -> Tree B (S n)

-- a well-formed red-black tree. Root is black, but height 
-- could be anything.
data RBT :: * where
  Root :: Tree B m -> RBT

-- example: reverse the tree
rev :: Tree c n -> Tree c n 
rev E = E
rev (TR a x b) = TR (rev b) x (rev a)
rev (TB a x b) = TB (rev b) x (rev a)

-- find the maximum value stored in a non-empty tree
maxB :: Tree B (S n) -> A
maxB (TB _ x E)          = x
maxB (TB _ _ (TR a x b)) = maxR (TR a x b)
maxB (TB _ _ (TB a x b)) = maxB (TB a x b)

maxR :: Tree R n -> A
maxR (TR _ x E)          = x
maxR (TR _ _ (TB a x b)) = maxB (TB a x b)

data Sing (c :: Color) :: * where    
    SR :: Sing R
    SB :: Sing B
    
-- for insertion, sometimes we need to break the invariant.
type family Incr (c :: Color) (x :: Nat) :: Nat where
    Incr R x = x
    Incr B x = S x

-- hide the color of the tree
data HTree :: Nat -> * where
  H :: Tree c n -> HTree n

-- captures the height, but not the fact that red nodes have black children
data AlmostTree :: Nat -> * where
  AE :: AlmostTree Z
  AT :: Sing c -> (Tree c1 n) -> A -> (Tree c2 n) -> AlmostTree (Incr c n)

-- input color is implicitly black 
balanceL ::  AlmostTree n -> A -> Tree c n -> HTree (S n)
-- these are the two rotation cases
balanceL (AT SR (TR a x b) y c) z d = H (TR (TB a x b) y (TB c z d))
balanceL (AT SR a x (TR b y c)) z d = H (TR (TB a x b) y (TB c z d))
-- need to expand the catch-all, because the *proof* is different in each case.  
balanceL AE kv r = H (TB E kv r)
balanceL (AT SB a  x b) kv r = H (TB (TB a x b) kv r)
balanceL (AT SR E x E) kv r = H (TB (TR E x E) kv r)
balanceL (AT SR (TB a1 x1 a2) x (TB b1 y1 b2)) y c = H (TB (TR (TB a1 x1 a2) x (TB b1 y1 b2)) y c)

-- input color is implicitly black 
balanceR :: Tree c n -> A -> AlmostTree n -> HTree (S n)
-- these are the two rotation cases
balanceR a x (AT SR (TR b y c)  z d) = H (TR (TB a x b) y (TB c z d))
balanceR a x (AT SR b y (TR c z d)) = H (TR (TB a x b) y (TB c z d))
-- catch-all 
balanceR a x AE = H (TB a x E)
balanceR a x (AT SR E kv E) = H (TB a x (TR E kv E))
balanceR a x (AT SR (TB l kv r) kv' (TB l' kv0 r')) = H (TB a x (TR (TB l kv r) kv' (TB l' kv0 r')))
balanceR a x (AT SB l kv r) = H (TB a x (TB l kv r))

-- forget that the top node of the tree satisfies the color invariant
forget :: HTree n -> AlmostTree n
forget (H E) = AE 
forget (H (TR l kv r)) = AT SR l kv r
forget (H (TB l kv r)) = AT SB l kv r

-- determine the color of the tree
decide :: (Tree c n) -> Either (Tree B n) (Tree R n)
decide E = Left E
decide (TR a x b) = Right (TR a x b)
decide (TB a x b) = Left (TB a x b)

balanceBreak :: HTree n -> A -> HTree n -> AlmostTree n
balanceBreak (H l) x (H r) = AT SR l x r

insRed :: Tree R n -> A -> AlmostTree n
insRed (TR l y r) x = case compare x y of
   LT -> balanceBreak (insBlack l x) y (H r)
   GT -> balanceBreak (H l) y (insBlack r x) 
   EQ -> AT SR l y r

insBlack :: Tree B n -> A -> HTree n
insBlack E x = H (TR E x E)
insBlack (TB l y r) x = case (compare x y) of
    LT -> balanceL (insAny l x) y r
    GT -> balanceR l y (insAny r x)
    EQ -> H (TB l y r)

insAny :: Tree c n -> A -> AlmostTree n
insAny t x = case decide t of
   Left rt -> forget (insBlack rt x )
   Right rt -> insRed rt x

blacken :: AlmostTree n -> RBT
blacken AE = Root E
blacken (AT _ l x r) = (Root (TB l x r))

insert :: RBT -> A -> RBT
insert (Root t) x = blacken (insAny t x)
