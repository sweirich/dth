-- Implementation of deletion for red black trees by Matt Might

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf

module MightRedBlack where

import Prelude hiding (max)

data Color = 
   R  -- red
 | B  -- black
 | BB -- double black
 | NB -- negative black
 deriving (Show)

data RBSet a =
   E  -- black leaf
 | EE -- double black leaf
 | T Color (RBSet a) a (RBSet a)
 deriving (Show)

 -- Private auxiliary functions --

redden :: RBSet a -> RBSet a
redden (T _ a x b) = T R a x b

blacken :: RBSet a -> RBSet a
blacken (T _ a x b) = T B a x b

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
insert x s = blacken (ins s) 
 where ins E = T R E x E
       ins s@(T color a y b) | x < y     = balance color (ins a) y b
                             | x > y     = balance color a y (ins b)
                             | otherwise = s


max :: RBSet a -> a
max E = error "no largest element"
max (T _ _ x E) = x
max (T _ _ x r) = max r

remove :: RBSet a -> RBSet a
remove E = E
remove (T R E _ E) = E
remove (T B E _ E) = EE
remove (T B E _ (T R a x b)) = T B a x b
remove (T B (T R a x b) _ E) = T B a x b
remove (T color l@(T R a x b) y r) = bubble color l' mx r 
 where mx = max l
       l' = removeMax l

removeMax :: RBSet a -> RBSet a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ _ E) = remove s
removeMax s@(T color l x r) = bubble color l x (removeMax r)

delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x s = T B a x b
 where del E = E
       del s@(T color a y b) | x < y     = bubble color (del a) y b
                             | x > y     = bubble color a y (del b)
                             | otherwise = remove s
       T _ a x b = del s


main :: IO ()
main = 
 do
 return $! ()
