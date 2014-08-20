{-# LANGUAGE RankNTypes, ExistentialQuantification, EmptyDataDecls, NoMonomorphismRestriction, MultiParamTypeClasses, FlexibleInstances, TypeFamilies #-}        

{- 

Capturing the constraints of perfect trees using the "finally tagless"
approach. This version uses a technique popularized in:

   Finally Tagless, Partially Evaluated
   Tagless Staged Interpreters for Simpler Typed Languages
   Jacques Carette, Oleg Kiselyov and Chung-chieh Shan
   JFP 2009

However, the idea itself is much older:

   See for example:

   Metacircularity in the polymorphic λ-calculus.
   Pfenning, Frank, and Peter Lee. 1991. 
   Theoretical Computer Science 89(1):137–159

   Encoding types in ML-like languages. Yang. ICFP 1998

For a modern take on this practice, see:

   Folding Domain-Specific Languages: Deep and Shallow Embeddings (Functional Pearl)
   Jeremy Gibbons Nicolas Wu
   ICFP 2014

-}

data Z
data S n

-- Complete trees with Higher-order polymporphism
class Semantics repr a where
  leaf :: repr Z a 
  node :: repr h a -> a -> repr h a -> repr (S h) a 
  
data Tree a = forall h. Tree (Semantics repr a => repr h a)

zero' = leaf  
zero  = Tree zero'

one' = node zero' 1 zero'
one  = Tree one'

two' = node one' 2 one'
two = Tree two'

-- show function
newtype Sh h a = Sh { unSh :: String }
instance Show a => Semantics Sh a where
  leaf = Sh "."
  node l x r = Sh ("(" ++ unSh l ++ show x ++ unSh r ++ ")")

instance Show a => Show (Tree a) where
  show (Tree t) = unSh t

-- height function
newtype Ht h a = Ht { unHt :: Int }
instance Semantics Ht a where
  leaf = Ht 0
  node (Ht n1) _ (Ht n2) = (Ht (1 + n1))
  
height :: Tree a -> Int 
height (Tree t) = unHt t

-- Oleg's challenge

type family Pred h
type instance Pred Z = Z
type instance Pred (S n) = n

decr :: Tree a -> Tree a 
decr (Tree t) = undefined
  -- (Tree (Node (Node ll xl lr) xc (Node rl xr rr)))
  -- Tree (Node ll xc rr)

next :: Tree Int -> Tree Int
next (Tree t) = Tree (node t 0 t)

merge :: Tree a -> Tree a -> Maybe a 
merge = undefined
