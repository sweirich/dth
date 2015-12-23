{-# LANGUAGE DataKinds, FlexibleInstances, GADTs, InstanceSigs, KindSignatures,
    MultiParamTypeClasses, TypeFamilies #-}

{- Implementation of GADT TREAPs by Thomas Delacour and Pearl Li -}

module Treap where

import Control.Monad (liftM)
import Data.List (intercalate)
import Prelude hiding (GT, LT)
import Test.QuickCheck (Arbitrary, Positive, arbitrary, getPositive)

-- -----------------------------------------------------------------------------
-- Data definitions
-- -----------------------------------------------------------------------------

data Nat = Z | S Nat

data Priority p where
  Zero :: Priority Z
  Succ :: Priority p -> Priority (S p)

-- | The GE typeclass defines a priority p1 being greater than or equal to
-- a priority p2.
class GE (p1 :: Nat) (p2 :: Nat) where
instance GE p Z
instance GE p1 p2 => GE (S p1) (S p2)

data Cmp p1 p2 where
  GT :: GE p1 p2 => Cmp p1 p2
  LT :: GE p2 p1 => Cmp p1 p2

-- | The PPriority type is a wrapper for Priority p which doesn't include the
-- priority in the type.
data PPriority where
  Wrap :: Priority p -> PPriority

-- | The TH type is either empty or a node whose children's priorities satisfy
-- the max-heap property.
data TH (p :: Nat) (pl :: Nat) (pr :: Nat) a where
  E :: TH Z Z Z a
  N :: (GE p pl, GE p pr) => Priority p -> a -> TH pl pll plr a ->
         TH pr prl prr a -> TH p pl pr a

-- | The TL type is a node whose priority is less than its left child's
-- priority, but will form a valid treap node after a right rotation.
data TL (p :: Nat) (pl :: Nat) (pll :: Nat) (plr :: Nat) (pr :: Nat) a where
  NL :: (GE pl p, GE p pr, GE p plr) => Priority p -> a -> TH pl pll plr a ->
          TH pr prl prr a -> TL p pl pll plr pr a

-- | The TR type is a node whose priority is less than its right child's
-- priority, but will form a valid treap node after a left rotation.
data TR (p :: Nat) (pl :: Nat) (prl :: Nat) (prr :: Nat) (pr :: Nat) a where
  NR :: (GE pr p, GE p pl, GE p prl) => Priority p -> a -> TH pl pll plr a ->
          TH pr prl prr a -> TR p pl prl prr pr a

-- | Tree a represents a BST which also satisfies the max-heap property wrt
-- each node's priority.
data Tree a where
  Root :: TH p pl pr a -> Tree a

-- -----------------------------------------------------------------------------
-- Instance Classes
-- -----------------------------------------------------------------------------

instance Eq Nat where
  n1 == n2 = toInt n1 == toInt n2

instance Eq a => Eq (Tree a) where
  Root E == Root E = True
  Root (N p1 v1 lt1 rt1) == Root (N p2 v2 lt2 rt2) =
    toNat p1 == toNat p2 && v1 == v2 &&
    Root lt1 == Root lt2 && Root rt1 == Root rt2

instance Show Nat where
  show = show . toInt

instance Show (Priority n) where
  show = show . toNat

instance Show a => Show (TH p pl pr a) where
  show E             = "E"
  show (N p v lt rt) = unwords ["N", show p, show v, ts] where
    ts = case (lt, rt) of
           (E,  E)  -> "E E"
           (lt, E)  -> "(" ++ show lt ++ ") E"
           (E,  rt) -> "E (" ++ show rt ++ ")"
           (lt, rt) -> "(" ++ show lt ++ ") (" ++ show rt ++ ")"

instance Show a => Show (Tree a) where
  show (Root t) = show t

instance Arbitrary Nat where
  arbitrary = liftM fromInt arbitrary

instance Arbitrary PPriority where
  arbitrary = liftM fromNat arbitrary

-- -----------------------------------------------------------------------------
-- Main Functions
-- -----------------------------------------------------------------------------

-- | The function 'empty' returns the Empty Tree constructor.
empty :: Tree a
empty = Root E

-- | The function 'size' returns the number of nodes contained in a given tree.
size :: Tree a -> Int
size (Root E)             = 0
size (Root (N _ _ lt rt)) = 1 + size (Root lt) + size (Root rt)

-- | The function 'height' returns the longest path from the root of the given
-- tree to any of its leaves.
height :: Tree a -> Int
height (Root E)             = 0
height (Root (N _ _ lt rt)) = 1 + max (height $ Root lt) (height $ Root rt)

-- | The function 'insert' inserts a new element with given priority into the
-- given Tree.
insert :: (Ord a, Show a) => Positive Int -> a -> Tree a -> Tree a
insert pn = case fromNat $ fromInt pn of
              Wrap ppn -> insert' ppn
  where
    insert' :: (Ord a, Show a) => Priority p -> a -> Tree a -> Tree a
    insert' pn x (Root E) = Root (N pn x E E)
    insert' pn x t@(Root (N p v lt rt))
      | x < v     = build p v (insert' pn x (Root lt)) (Root rt)
      | x > v     = build p v (Root lt) (insert' pn x (Root rt))
      | otherwise = t

-- | The function 'delete' deletes a given element from the given tree.
delete :: (Ord a, Show a) => a -> Tree a -> Tree a
delete x t@(Root E) = t
delete x t@(Root (N p v lt rt))
  | x < v     = build p v (delete x (Root lt)) (Root rt)
  | x > v     = build p v (Root lt) (delete x (Root rt))
  | otherwise =
      case (lt, rt) of
        (E, E) -> Root E
        (E, _) -> Root rt
        (_, E) -> Root lt
        _      -> delete x $ sink t

-- | The function 'member' checks to see if a given element is contained in the
-- Tree.
member :: Ord a => a -> Tree a -> Bool
member x (Root E) = False
member x (Root (N _ v lt rt))
  | x < v     = member x (Root lt)
  | x > v     = member x (Root rt)
  | otherwise = True 

-- | The function 'elements' returns an (ordered) list of elements from a given
-- Tree.
elements :: Tree a -> [a]
elements = elements' []
  where 
    elements' l (Root E)             = l
    elements' l (Root (N _ v lt rt)) =
      elements' (v:elements' l (Root rt)) (Root lt)

-- | The function 'union' combines two trees following the definition of set
-- union.
union :: (Show a, Ord a) => Tree a -> Tree a -> Tree a
union t1 (Root E) = t1
union (Root E) t2 = t2
union t1@(Root (N p1 v1 lt1 rt1)) t2@(Root (N p2 _ _ _)) = 
  case cmp p1 p2 of
   LT -> t2 `union` t1
   GT -> build p1 v1 (Root lt1 `union` lt2) (Root rt1 `union` rt2)
  where 
    (lt2, rt2) = split v1 t2

-- | The function 'intersect' combines two trees following the definition of set
-- intersection.
intersect :: (Show a, Ord a) => Tree a -> Tree a -> Tree a
intersect t1@(Root (N p1 v1 lt1 rt1)) t2@(Root (N p2 _ _ _)) = 
  case cmp p1 p2 of
   LT -> t2 `intersect` t1
   GT -> if member v1 t2 then build p1 v1 lt' rt'
         else join lt' rt'
  where 
    (lt2, rt2) = split v1 t2
    lt'        = Root lt1 `intersect` lt2
    rt'        = Root rt1 `intersect` rt2
intersect _ _  = Root E

-- | The function 'difference' finds the difference between two trees, following
-- the definition of set difference (not symmetric!)
difference :: (Show a, Ord a) => Tree a -> Tree a -> Tree a
difference = difference' True
  where
    difference' :: (Show a, Ord a) => Bool -> Tree a -> Tree a -> Tree a
    difference' b t1 (Root E) = if b then t1 else Root E
    difference' b (Root E) t2 = if b then Root E else t2
    difference' b t1@(Root (N p1 v1 lt1 rt1)) t2@(Root (N p2 _ _ _)) = 
      case cmp p1 p2 of
       LT -> difference' (not b) t2 t1
       GT -> if b && not (member v1 t2) then build p1 v1 lt' rt'
             else join lt' rt'
      where 
        (lt2, rt2) = split v1 t2
        lt'        = difference' b (Root lt1) lt2
        rt'        = difference' b (Root rt1) rt2

-- -----------------------------------------------------------------------------
-- Auxiliary Functions
-- -----------------------------------------------------------------------------

toInt :: Nat -> Int
toInt Z     = 0
toInt (S n) = 1 + toInt n

fromInt :: Positive Int -> Nat
fromInt p = fromPosInt $ getPositive p

fromPosInt :: Int -> Nat
fromPosInt 0 = Z
fromPosInt n = S $ fromPosInt (n-1)

toNat :: Priority p -> Nat
toNat Zero     = Z
toNat (Succ p) = S (toNat p)

fromNat :: Nat -> PPriority
fromNat Z     = Wrap Zero
fromNat (S n) =
  case fromNat n of
    Wrap res -> Wrap (Succ res)

-- | The 'cmp' function compares two priorities and returns a GT or LT.
cmp :: Priority p1 -> Priority p2 -> Cmp p1 p2
cmp Zero Zero           = GT
cmp (Succ s1) Zero      = GT
cmp Zero (Succ s2)      = LT
cmp (Succ s1) (Succ s2) =
  case cmp s1 s2 of
    GT -> GT
    LT -> LT

isEmpty :: Tree a -> Bool
isEmpty (Root E)           = True
isEmpty (Root N{}) = False

getLeft :: Tree a -> Tree a
getLeft (Root E)            = error "getLeft called on empty tree"
getLeft (Root (N _ _ lt _)) = Root lt

getRight :: Tree a -> Tree a
getRight (Root E)            = error "getRight called on empty tree"
getRight (Root (N _ _ _ rt)) = Root rt

rotateRight :: TL p pl pll plr pr a -> TH pl pll p a
rotateRight (NL p v (N pl vl llt lrt) rt) = N pl vl llt (N p v lrt rt)

rotateLeft :: TR p pl prl prr pr a -> TH pr p prr a
rotateLeft (NR p v lt (N pr vr rlt rrt) ) = N pr vr (N p v lt rlt) rrt

-- | The 'priority' function returns the priority of a TH.
priorityTH :: TH p pl pr a -> Priority p
priorityTH E             = Zero
priorityTH (N p v lt rt) = p

-- | The 'priority' function returns the integer priority of a Tree a.
priority :: Tree a -> Int
priority (Root E)           = 0
priority (Root (N p _ _ _)) = toInt $ toNat p

-- | The 'build' function takes in a priority, the node value, and left and
-- right subtrees; performs a rotation if necessary; and returns a valid Tree.
build :: Show a => Priority p -> a -> Tree a -> Tree a -> Tree a
build p v (Root E)  (Root E)  = Root (N p v E E)
build p v (Root lt) (Root rt) =
  case (cmp p (priorityTH lt), cmp p (priorityTH rt)) of
    (GT, GT) -> Root $ N p v lt rt
    (LT, GT) ->
      case lt of
        N pl vl llt lrt ->
          case cmp p (priorityTH lrt) of
            GT -> Root $ rotateRight $ NL p v lt rt
    (GT, LT) ->
      case rt of
        N pr vr rlt rrt ->
          case cmp p (priorityTH rlt) of
            GT -> Root $ rotateLeft $ NR p v lt rt
    _        -> error $ intercalate " \n" ["Invalid build:", show p, show v,
                                           show lt, show rt]

-- | The 'sink' function changes the root's priority to the priority of its
-- highest-priority child and forces a rotation.
sink :: Tree a -> Tree a
sink t@(Root E) = t
sink (Root (N p v lt rt)) =
  case cmp pl pr of
    GT ->
      case (cmp pl pl, lt) of
        (GT, N{}) -> Root $ rotateRight $ NL pl v lt rt
    LT ->
      case (cmp pr pr, rt) of
        (GT, N{}) -> Root $ rotateLeft $ NR pr v lt rt
  where
    pl = priorityTH lt
    pr = priorityTH rt

-- | The 'fromList2' function creates a Tree by repeatedly inserting values
-- and their corresponding priorities into the empty tree.
fromList2 :: (Ord a, Show a) => [Positive Int] -> [a] -> Tree a 
fromList2 lp le = foldr (\(p, y) acc -> insert p y acc) empty $ zip lp le

split :: (Show a, Ord a) => a -> Tree a -> (Tree a, Tree a)
split _ (Root E) = (Root E, Root E)
split x (Root (N p v lt rt))
  | x < v     = (llt, build p v lrt (Root rt))
  | x > v     = (build p v (Root lt) rlt, rrt)
  | otherwise = (Root lt, Root rt)
  where
    (llt, lrt) = split x (Root lt)
    (rlt, rrt) = split x (Root rt)

join :: (Show a, Ord a) => Tree a -> Tree a -> Tree a
join t1 (Root E) = t1
join (Root E) t2 = t2
join t1@(Root (N p1 v1 lt1 rt1)) t2@(Root (N p2 v2 lt2 rt2)) =
  case cmp p1 p2 of
   GT -> build p1 v1 (Root lt1) (join (Root rt1) t2)
   LT -> build p2 v2 (join t1 (Root lt2)) (Root rt2)