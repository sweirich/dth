Red-Black Trees with GADTs
==========================

This version of RedBlack trees demonstrates the use of GADTs to statically
verify all four RedBlack tree invariants. It is a modification of the 
RedBlack module (minus deletion).

> {-# LANGUAGE InstanceSigs,GADTs, DataKinds, KindSignatures, MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}

> module RedBlackGADT where

> import Set

> import Control.Monad 
> import Test.QuickCheck hiding (elements)
> import Data.Maybe as Maybe
> import Data.List (sort, nub)

A red-black tree is a binary search tree where every node is
additionally marked with a color (red or black).

> data Color = Red | Black deriving (Eq, Show)

A singleton type for colors.
Datatype promotion allows us to use Colors as parameters to type
definitions.  This is a GADT---a type that is indexed by another type. Each
data constructor determines what the type parameter c must be.

> data SColor (c :: Color) where
>    R :: SColor Red
>    B :: SColor Black


An equality test for singleton colors. 

> (%==%) :: SColor c1 -> SColor c2 -> Bool
> R %==% R = True
> B %==% B = True
> _ %==% _ = False

A colored tree, where the index c indicates the color of the top node of the
tree, and n indicates the black height of the tree.

> data CT (n :: Nat) (c :: Color) (a :: *) where
>    E  :: CT Z Black a
>    N  :: Valid c c1 c2 => SColor c -> (CT n c1 a) -> a -> (CT n c2 a) 
>       -> CT (Incr c n) c a

We can extract the color of a node in the tree

> color :: CT n c a -> SColor c
> color (N c _ _ _) = c
> color E = B

To make sure that red nodes have black children, we use a multiparameter type
class. This class captures the valid relationships between the color of a node
and the colors of the two children. If the former is `Red` the latter must be
`Black`. Alternatively, if the former is `Black` then the latter could be
anything.

> class Valid (c :: Color) (c1 :: Color) (c2 :: Color) where
> instance Valid Red Black Black 
> instance Valid Black c1 c2

To enforce that trees have balanced black heights, we index the tree by a
natural number that tracks this black height statically.

> data Nat = Z | S Nat

The black height of a node however is conditionally incremented. A *type
family* is like a function at the type level. This function below increments
the number `n` when the color is `Black` and leaves it alone otherwise. We use
this type family in the type of `N` above.

> type family Incr (c :: Color) (n :: Nat) :: Nat
> type instance Incr Black n = S n
> type instance Incr Red   n = n

A *top-level definition* that enforces that the root of the tree is black.

> data RBT a where
>   Root :: (CT n Black a) -> RBT a

> instance Show a => Show (RBT a) where
>   show (Root x) = show x

Haskell cannot derive the show instances for `SColor` and `CT` now that 
they are indexed.

> instance Show (SColor c) where
>    show R = "R"
>    show B = "B"

> instance Show a => Show (CT n c a) where
>    show E = "E"
>    show (N c l x r) = "(N " ++ show c ++ " " ++ show l ++ " " ++ show x ++ " " ++ show r ++ ")"



Furthermore, Red Black trees must satisfy the following 
invariants.

  1. The empty nodes at the leaves are black,
     *enforced by the types*
                        
  2. The root is always black,
     *enforced by the types*
                        
  3. From each node, every path to a leaf 
     has the same number of black nodes,
     *enforced by the types*
                        
  4. Red nodes have black children,
     *enforced by the types*
  
* Together, these invariants imply that every red-black tree is
"approximately balanced", in the sense that the longest path to an
empty node is no more than twice the length of the shortest.

* From this, it follows that all operations will run in O(log_2 n)
time.

Checking the invariants
---------------------------  

We still need to test that the implementation satisfies the binary search tree
condition.

> prop_BST :: RBT Int -> Bool
> prop_BST t = isSortedNoDups (elements t)

> isSortedNoDups :: Ord a => [a] -> Bool  
> isSortedNoDups x = nub (sort x) == x

To use quickcheck, we need an arbitrary instance. We'll use the one 
based on `insert` and `empty`. 

> instance (Ord a, Arbitrary a) => Arbitrary (RBT a)  where
>    arbitrary = liftM (foldr insert empty) arbitrary

RBT proxy for the general set properties.

> rbt :: Proxy RBT
> rbt = Proxy

> main :: IO ()
> main = do

Make sure the RBT is a set  
  
>   quickCheck $ prop_empty rbt
>   quickCheck $ prop_insert1 rbt
>   quickCheck $ prop_insert2 rbt

Implementation specific properties.

>   putStrLn "BST property"
>   quickCheck prop_BST
>   -- putStrLn "Leaves are black"
>   -- quickCheck prop_Rb1
>   -- putStrLn "Root is black"
>   -- quickCheck prop_Rb2
>   -- putStrLn "Black height the same"
>   -- quickCheck prop_Rb3
>   -- putStrLn "Red nodes have black children"
>   -- quickCheck prop_Rb4


Implementation
--------------

We then just need to implement the method of the 
Set class for this data structure. 

> instance Set RBT where

The empty tree is the same as before.

>   empty :: RBT a
>   empty = (Root E)

Membership testing and listing the elements 
requires just a trivial change.

>   member :: Ord a => a -> RBT a -> Bool
>   member x (Root t) = aux x t where
>     aux :: Ord a => a -> CT n c a -> Bool
>     aux x E = False
>     aux x (N _ a y b)
>       | x < y     = aux x a
>       | x > y     = aux x b
>       | otherwise = True

>   elements :: Ord a => RBT a -> [a]
>   elements (Root t) = aux t [] where
>      aux :: Ord a => CT n c a -> [a] -> [a]
>      aux E acc = acc
>      aux (N _ a x b) acc = aux a (x : aux b acc)
  

Insertion, is, of course a bit trickier. 

>   insert :: Ord a => a -> RBT a -> RBT a
>   insert x (Root t) = blacken (ins x t)

After insertion, with the auxilary functio `ins`, we blacken the top node of
the tree to make sure that invariant (2) is always satisfied.

> blacken :: IR n a -> RBT a
> blacken (IN _ l v r) = Root (N B l v r)

Note that the types describe what happens with insertion now. After insertion
into a tree of type `CT n c a`, we don't know what color of tree will be
produced. Furthermore, this tree might not satisfy condition number #4, it is
allowed to have a red root with one red subtree. However, the black height
doesn't change (at least, not until we call `blacken`).  Therefore, we need 
an auxiliary type that tracks the black height, but hides the top color.

> data IR n a where
>   IN :: SColor c -> CT n c1 a -> a -> CT n c2 a -> IR (Incr c n) a

> ins :: Ord a => a -> CT n c a -> IR n a
> ins x E = IN R E x E
> ins x s@(N c a y b)
>   | x < y     = balanceL c (ins x a) y b
>   | x > y     = balanceR c a y (ins x b)
>   | otherwise = (IN c a y b)


In the recursive calls, before returning the new tree, however, we may
need to *rebalance* to maintain the red-black invariants. The code to
do this is encapsulated in a helper function `balance`.

Balancing
---------

* The key insight in writing the balancing function is that we do not try to
rebalance as soon as we see a red node with a red child. That can be fixed
just by blackening the root of the tree, so we return this tree as-is.  (We
call such trees, which violate invariants two and four only at the root
"infrared").

The real problem comes when we've inserted a new red node between a black
parent and a red child. 

* i.e., the job of the balance function is to rebalance trees with a
black-red-red path starting at the root.

* The result of rebalancing maintains the black height by converting 
to a red parent with black children.

* Since the root has two children and four grandchildren, there are
four ways in which such a path can happen.

> {-
> -- The original definition of balance. Note that there are two sorts of cases,
> -- one where we inserted on the left, and one where we inserted on the right.

> balance :: RBT a -> RBT a 
> balance (N B (N R (N R a x b) y c) z d) = N R (N B a x b) y (N B c z d)
> balance (N B (N R a x (N R b y c)) z d) = N R (N B a x b) y (N B c z d)

> balance (N B a x (N R (N R b y c) z d)) = N R (N B a x b) y (N B c z d)
> balance (N B a x (N R b y (N R c z d))) = N R (N B a x b) y (N B c z d)
> balance t = t
> -}

To work with the refined types, we need to modify the balance function
above. First, we break it into two parts, because the recursive call to insert
produces a result of type `IR` not `CT`. Now we have two balance functions,
one for rebalancing after an insertion in the left subtree and one for
rebalancing after an insertion in the right subtree.

> balanceL :: SColor c -> IR n a -> a -> CT n c1 a -> IR (Incr c n) a
> balanceL B (IN R (N R a x b) y c) z d = IN R (N B a x b) y (N B c z d)
> balanceL B (IN R a x (N R b y c)) z d = IN R (N B a x b) y (N B c z d)

The second issue is that we need to be more precise when the tree does not
need rebalancing. The type checker checks each branch individually, it doesn't
know the ordering of pattern matching. So we have to match the cases for
already balanced trees individually so that all calls to `N` will satisfy
their requirements.

> balanceL col (IN B a x b) z d        = IN col (N B a x b) z d
> balanceL col (IN R a@(N B _ _ _) x b@(N B _ _ _)) z d = IN col (N R a x b) z d
> balanceL col (IN R a@E x b@E) z d                     = IN col (N R a x b) z d

Note that we don't need these two cases, they don't have the same black height
on each side.

> -- balanceL col (IN R a@E x b@(N B _ _ _)) z d  = IN col (N R a x b) z d
> -- balanceL col (IN R a@(N B _ _ _) x b@E) z d  = IN col (N R a x b) z d

The balanceR function is similar.

> balanceR :: SColor c -> CT n c1 a -> a -> IR n a -> IR (Incr c n) a
> balanceR B a x (IN R (N R b y c) z d) = IN R (N B a x b) y (N B c z d)
> balanceR B a x (IN R b y (N R c z d)) = IN R (N B a x b) y (N B c z d)
> balanceR c a x (IN B b z d)           = IN c a x (N B b z d)
> balanceR c a x (IN R b@(N B _ _ _) z d@(N B _ _ _)) = IN c a x (N R b z d)
> --balanceR c a x (IN R b@E z d@(N B _ _ _)) = IN c a x (N R b z d)
> --balanceR c a x (IN R b@(N B _ _ _) z d@E) = IN c a x (N R b z d)
> balanceR c a x (IN R b@E z d@E) = IN c a x (N R b z d)





