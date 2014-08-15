-- Implementation of deletion for red black trees by Matt Might

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf
-- Draft paper:
--   http://matt.might.net/tmp/red-black-pearl.pdf

module MightRedBlack where

import Prelude hiding (max)
import Control.Monad 
import Test.QuickCheck hiding (elements)
import Data.List(nub,sort)

data Color = 
   R  -- red
 | B  -- black
 | BB -- double black
 | NB -- negative black
 deriving (Show, Eq)

data RBSet a =
   E  -- black leaf
 | EE -- double black leaf
 | T Color (RBSet a) a (RBSet a)
 deriving (Show, Eq)

 -- Private auxiliary functions --

redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

-- blacken for insert
-- never a leaf, could be red or black
blacken' :: RBSet a -> RBSet a
blacken' (T R a x b) = T B a x b
blacken' (T B a x b) = T B a x b

-- blacken for delete
-- root is never red, could be double black
blacken :: RBSet a -> RBSet a
blacken (T B a x b) = T B a x b
blacken (T BB a x b) = T B a x b
blacken E = E
blacken EE = E

isBB :: RBSet a -> Bool
isBB EE = True
isBB (T BB _ _ _) = True
isBB _ = False

blacker :: Color -> Color
blacker NB = R
blacker R = B
blacker B = BB
blacker BB = error "too black"

redder :: Color -> Color
redder NB = error "not black enough"
redder R = NB
redder B = R
redder BB = B

blacker' :: RBSet a -> RBSet a
blacker' E = EE
blacker' (T c l x r) = T (blacker c) l x r

redder' :: RBSet a -> RBSet a
redder' EE = E
redder' (T c l x r) = T (redder c) l x r 

 -- `balance` rotates away coloring conflicts:
balance :: Color -> RBSet a -> a -> RBSet a -> RBSet a

 -- Okasaki's original cases:
balance B (T R (T R a x b) y c) z d = T R (T B a x b) y (T B c z d)
balance B (T R a x (T R b y c)) z d = T R (T B a x b) y (T B c z d)
balance B a x (T R (T R b y c) z d) = T R (T B a x b) y (T B c z d)
balance B a x (T R b y (T R c z d)) = T R (T B a x b) y (T B c z d)

 -- Six cases for deletion:
balance BB (T R (T R a x b) y c) z d = T B (T B a x b) y (T B c z d)
balance BB (T R a x (T R b y c)) z d = T B (T B a x b) y (T B c z d)
balance BB a x (T R (T R b y c) z d) = T B (T B a x b) y (T B c z d)
balance BB a x (T R b y (T R c z d)) = T B (T B a x b) y (T B c z d)

balance BB a x (T NB (T B b y c) z d@(T B _ _ _)) 
    = T B (T B a x b) y (balance B c z (redden d))
balance BB (T NB a@(T B _ _ _) x (T B b y c)) z d
    = T B (balance B (redden a) x b) y (T B c z d)

balance color a x b = T color a x b

 -- `bubble` "bubbles" double-blackness upward toward the root:
bubble :: Color -> RBSet a -> a -> RBSet a -> RBSet a
bubble color l x r
 | isBB(l) || isBB(r) = balance (blacker color) (redder' l) x (redder' r)
 | otherwise          = balance color l x r




 -- Public operations --

empty :: RBSet a
empty = E


member :: (Ord a) => a -> RBSet a -> Bool
member x E = False
member x (T _ l y r) | x < y     = member x l
                     | x > y     = member x r
                     | otherwise = True


insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x s = blacken' (ins s) 
 where ins E = T R E x E
       ins s@(T color a y b) | x < y     = balance color (ins a) y b
                             | x > y     = balance color a y (ins b)
                             | otherwise = s


max :: RBSet a -> a
max E = error "no largest element"
max (T _ _ x E) = x
max (T _ _ x r) = max r

-- Remove this node: it might leave behind a double black node
remove :: RBSet a -> RBSet a
-- remove E = E   -- impossible!
-- ; Leaves are easiest to kill:
remove (T R E _ E) = E
remove (T B E _ E) = EE
-- ; Killing a node with one child;
-- ; parent or child is red:
-- remove (T R E _ child) = child
-- remove (T R child _ E) = child
remove (T B E _ (T R a x b)) = T B a x b
remove (T B (T R a x b) _ E) = T B a x b
-- ; Killing a black node with one black child:
-- remove (T B E _ child@(T B _ _ _)) = blacker' child
-- remove (T B child@(T B _ _ _) _ E) = blacker' child
-- ; Killing a node with two sub-trees:
remove (T color l y r) = bubble color l' mx r 
 where mx = max l
       l' = removeMax l

removeMax :: RBSet a -> RBSet a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ _ E) = remove s
removeMax s@(T color l x r) = bubble color l x (removeMax r)

delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x s = blacken (del x s)
       
del x E = E
del x s@(T color a' y b') | x < y   = bubble color (del x a') y b'
                        | x > y     = bubble color a' y (del x b')
                        | otherwise = remove s

prop_del :: Int -> RBSet Int -> Bool
prop_del x s = color (del x s) `elem` [B, BB]


--- Testing code
       
elements :: Ord a => RBSet a -> [a]
elements t = aux t [] where
      aux E acc = acc
      aux (T _ a x b) acc = aux a (x : aux b acc)

instance (Ord a, Arbitrary a) => Arbitrary (RBSet a)  where
  arbitrary = liftM (foldr insert empty) arbitrary
       
prop_BST :: RBSet Int -> Bool
prop_BST t = isSortedNoDups (elements t)

color :: RBSet a -> Color
color (T c _ _ _) = c
color E = B
color EE = BB

prop_Rb2 :: RBSet Int -> Bool
prop_Rb2 t = color t == B

prop_Rb3 :: RBSet Int -> Bool
prop_Rb3 t = fst (aux t) where 
  aux E = (True, 0)
  aux (T c a x b) = (h1 == h2 && b1 && b2, if c == B then h1 + 1 else h1) where
      (b1 , h1) = aux a
      (b2 , h2) = aux b

prop_Rb4 :: RBSet Int  -> Bool
prop_Rb4 E = True
prop_Rb4 (T R a x b) = color a == B && color b == B && prop_Rb4 a && prop_Rb4 b
prop_Rb4 (T B a x b) = prop_Rb4 a && prop_Rb4 b


isSortedNoDups :: Ord a => [a] -> Bool  
isSortedNoDups x = nub (sort x) == x
              
                            
prop_delete_spec1 :: RBSet Int -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

prop_delete_spec2 :: RBSet Int -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
   allpairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete_spec3 :: RBSet Int -> Int -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (delete x t == t)

prop_delete_bst :: RBSet Int -> Bool
prop_delete_bst t = all (\x -> prop_BST (delete x t)) (elements t)

prop_delete2 :: RBSet Int -> Bool
prop_delete2 t = all (\x -> prop_Rb2 (delete x t)) (elements t)

prop_delete3 :: RBSet Int -> Bool
prop_delete3 t = all (\x -> prop_Rb3 (delete x t)) (elements t)

prop_delete4 :: RBSet Int -> Bool
prop_delete4 t = all (\x -> prop_Rb4 (delete x t)) (elements t)

check_insert = do
    putStrLn "BST property"
    quickCheck prop_BST
    putStrLn "Root is black"
    quickCheck prop_Rb2
    putStrLn "Black height the same"
    quickCheck prop_Rb3
    putStrLn "Red nodes have black children"
    quickCheck prop_Rb4

check_delete = do
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec1
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec2
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_spec3
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete2
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete3
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete4
   quickCheckWith (stdArgs {maxSuccess=100}) prop_delete_bst
       

main :: IO ()
main = 
 do
 return $! ()
