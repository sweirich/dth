{-# LANGUAGE InstanceSigs,GADTs, DataKinds, KindSignatures, MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}

-- Implementation of deletion for red black trees by Matt Might

-- Original available from: 
--   http://matt.might.net/articles/red-black-delete/code/RedBlackSet.hs
-- Slides:
--   http://matt.might.net/papers/might2014redblack-talk.pdf

module MightRedBlackGADT where

import Prelude hiding (max)

data Color = Red | Black | DoubleBlack | NegativeBlack

data SColor (c :: Color) where
   R  :: SColor Red -- red
   B  :: SColor Black -- black
   BB :: SColor DoubleBlack -- double black
   NB :: SColor NegativeBlack -- negative black

(%==%) :: SColor c1 -> SColor c2 -> Bool
R %==% R = True
B %==% B = True
BB %==% BB = True
NB %==% NB = True
_ %==% _ = False

data Nat = Z | S Nat

data CT (n :: Nat) (c :: Color) (a :: *) where
   E  :: CT n Black a
   T  :: Valid c c1 c2 => 
         SColor c -> (CT n c1 a) -> a -> (CT n c2 a) -> CT (Incr c n) c a

class Valid (c :: Color) (c1 :: Color) (c2 :: Color) where
instance Valid Red Black Black 
instance Valid Black c1 c2

type family Incr (c :: Color) (n :: Nat) :: Nat
type instance Incr Black n       = S n
type instance Incr DoubleBlack n = S (S n)
type instance Incr Red   n       = n
type instance Incr NegativeBlack (S n) = n

data RBSet a where
  Root :: (CT n Black a) -> RBSet a

instance Show a => Show (RBSet a) where
  show (Root x) = show x
  
instance Show (SColor c) where  
  show R = "R"
  show B = "B"
  show BB = "BB"
  show NB = "NB"
  
instance Show a => Show (CT n c a) where
  show E = "E"
  show (T c l x r) = 
    "(N " ++ show c ++ " " ++ show l ++ " " 
          ++ show x ++ " " ++ show r ++ ")"

{-
data RBSet a =
   E  -- black leaf
 | EE -- double black leaf
 | T Color (RBSet a) a (RBSet a)
 deriving (Show)
-}



 -- Public operations --

empty :: RBSet a
empty = Root E

member :: (Ord a) => a -> RBSet a -> Bool
member x (Root t) = aux x t where
  aux :: Ord a => a -> CT n c a -> Bool
  aux x E = False
  aux x (T _ l y r) | x < y     = aux x l
                    | x > y     = aux x r
                    | otherwise = True

insert :: (Ord a) => a -> RBSet a -> RBSet a                    
insert x (Root s) = blacken (ins x s) 
 where ins :: Ord a => a -> CT n c a -> IR n a
       ins x E = IN R E x E
       ins x s@(T color a y b) | x < y     = balanceL color (ins x a) y b
                               | x > y     = balanceR color a y (ins x b)
                               | otherwise = (IN color a y b)


       blacken :: IR n a -> RBSet a
       blacken (IN _ a x b) = Root (T B a x b)

data IR n a where
   IN :: SColor c -> CT n c1 a -> a -> CT n c2 a -> IR (Incr c n) a

 -- `balance` rotates away coloring conflicts:
   
balanceL :: SColor c -> IR n a -> a -> CT n c1 a -> IR (Incr c n) a
balanceL B (IN R (T R a x b) y c) z d = IN R (T B a x b) y (T B c z d)
balanceL B (IN R a x (T R b y c)) z d = IN R (T B a x b) y (T B c z d)
balanceL col (IN B a x b) z d        = IN col (T B a x b) z d
balanceL col (IN R a@(T B _ _ _) x b@(T B _ _ _)) z d = IN col (T R a x b) z d
balanceL col (IN R a@E x b@E) z d                     = IN col (T R a x b) z d
   
   
balanceR :: SColor c -> CT n c1 a -> a -> IR n a -> IR (Incr c n) a
balanceR B a x (IN R (T R b y c) z d) = IN R (T B a x b) y (T B c z d)
balanceR B a x (IN R b y (T R c z d)) = IN R (T B a x b) y (T B c z d)
balanceR c a x (IN B b z d)           = IN c a x (T B b z d)
balanceR c a x (IN R b@(T B _ _ _) z d@(T B _ _ _)) = IN c a x (T R b z d)
balanceR c a x (IN R b@E z d@E) = IN c a x (T R b z d)
                                                        
                                  
 -- DELETION --
                                  
-- del and remove have the same type.
-- they take a well formed tree to some tree with a broken invariant
                                  
delete :: (Ord a) => a -> RBSet a -> RBSet a
delete x (Root s) = blacken (del x s) 
 where blacken :: DT n a -> RBSet a
       blacken (DT _ a x b) = undefined -- Root (T B a x b)
       blacken DE  = Root E
       blacken DEE = Root E
       
       del :: Ord a => a -> CT n c a -> DT n a
       del x E = DE
       del x s@(T color a y b) | x < y     = bubbleL color (del x a) y b
                               | x > y     = bubbleR color a y (del x b)
                               | otherwise = remove s
                                  
data DT n a where
  DT  :: SColor c -> CT n c1 a -> a -> CT n c2 a -> DT (Incr c n) a
  DE  :: DT Z a
  DEE :: DT (S Z) a
  
remove :: CT n c a -> DT n a   
remove = undefined

bubbleL :: SColor c -> DT n a -> a -> CT n c1 a -> DT n a
bubbleL = undefined

bubbleR :: SColor c -> CT n c1 a -> a -> DT n a -> DT n a 
bubbleR = undefined

type family Blacker (c :: Color) :: Color
type instance Blacker NegativeBlack = Red
type instance Blacker Red = Black
type instance Blacker Black = DoubleBlack

blacker :: SColor c -> SColor (Blacker c)
blacker NB = R
blacker R = B
blacker B = BB
blacker BB = error "too black"

type family Redder (c :: Color) :: Color
type instance Redder Red = NegativeBlack     
type instance Redder Black = Red
type instance Redder DoubleBlack = Black

redder :: SColor c -> SColor (Redder c)
redder NB = error "not black enough"
redder R = NB
redder B = R
redder BB = B

{-
redden :: CT n c a -> CT n Red a
redden (T _ a x b) = T R a x b

isBB :: CT n c a -> Bool
isBB EE = True
isBB (T BB _ _ _) = True
isBB _ = False
-}


blacker' :: CT n c a -> CT (S n) (Blacker c) a
-- blacker' E = EE
-- blacker' (T NB l x r) = T R l x r
blacker' (T R l x r) = T B l x r
-- blacker' (T B l x r) = T BB l x r



redder' :: CT (S n) c a -> CT n (Redder c) a
-- redder' EE = E
-- redder' (T R l x r) = T NB l x r 
-- redder' (T B l x r) = T R l x r 
redder' (T BB l x r) = T B l x r 
                                  
{-                                                        
balance :: SColor c -> CT n c1 a -> a -> CT n c2 a -> CT n c3 a

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
-}

{-
 -- `bubble` "bubbles" double-blackness upward toward the root:
bubble :: SColor c -> CT n c a -> a -> CT n c a -> CT n c a
bubble color l x r
 | isBB(l) || isBB(r) = balance (blacker color) (redder' l) x (redder' r)
 | otherwise          = balance color l x r

max :: CT n c a -> a
max E = error "no largest element"
max (T _ _ x E) = x
max (T _ _ x r) = max r

-- Remove this node: it might leave behind a double black node
remove :: CT n c a -> CT n c a
remove (T R E _ E) = E
remove (T B E _ E) = EE
remove (T R E _ child) = child
remove (T R child _ E) = child
remove (T B E _ (T R a x b)) = T B a x b
remove (T B (T R a x b) _ E) = T B a x b
remove (T B E _ child@(T B _ _ _)) = blacker' child
remove (T B child@(T B _ _ _) _ E) = blacker' child
remove (T color l y r) = bubble color l' mx r 
 where mx = max l
       l' = removeMax l

removeMax :: CT n c a -> CT n c a
removeMax E = error "no maximum to remove"
removeMax s@(T _ _ _ E) = remove s
removeMax s@(T color l x r) = bubble color l x (removeMax r)


-}

main :: IO ()
main = 
 do
 return $! ()
