{-# LANGUAGE TemplateHaskell, GADTs, DataKinds, PolyKinds, TypeFamilies, RankNTypes, TypeOperators, UndecidableInstances, KindSignatures, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, AllowAmbiguousTypes, ConstraintKinds #-}

-- investigating Conor's "How to keep your neighbors in order" in Haskell

module Order where

import Data.Singletons.Prelude
import Data.Singletons.TH

-- Section 2.

-- Conor starts out with a large elimination that changes a boolean value into
-- a proposition. In Haskell, we repressent propositions by classes or
-- types. The latter is more expressive, but inconsistent. So we'll stick with 
-- classes where we can.

class So (b :: Bool) where
instance So True   

-- The next definition, of the squash operator !, is unnecessary, at least for
-- 'So'. Haskell will never let you see dictionaries, so they are already
-- hidden. Furthermore, So has no evidence, so it will be represented with 0-bits.

-- Section 3. The Wrong attempt.

-- like Conor, we'll fix a parameter for the data in our trees.  we'll also
-- make sure that we can promote it and compare it at the type level.

  
$(singletons [d| 
              
   data P = A | B | C deriving (Eq, Ord)
                               
                      |])                                                   
  
$(singletons [d| 
                               
   data STRange = Zero | Span P P                       
                                            
   data Tree = Leaf | Node Tree P Tree

   guard :: Bool -> Maybe a -> Maybe a
   guard True mx = mx
   guard False _ = Nothing

                      |])                                                   

-- note, some bug in singletons library prevents this from promotion. The 
-- problem is with the ord instance (p <= c).
valid :: Tree -> Maybe STRange
valid Leaf = Just Zero
valid (Node l p r) = 
     case (valid l, valid r) of 
       (Just Zero, Just Zero) -> Just (Span p p)
       (Just Zero, Just (Span c d)) -> guard (p <= c) (Just (Span p d))
       (Just (Span a b), Just Zero) -> guard (b <= p) (Just (Span a p))
       (Just (Span a b), Just (Span c d)) -> 
          guard (b <= p) (guard (p <= c) (Just (Span a d)))
       (_ , _) -> Nothing

-- for that reason, we have to also define these explicitly
-- and closed type families don't seem to work
-- on the other hand, we really need to have these definitions...
       

lep :: P -> P -> Bool
lep A A = True
lep A B = True
lep A C = True
lep B B = True
lep B C = True
lep C C = True
lep a b = False

type family LEP (a :: P) (b :: P) where
   LEP A A = True
   LEP A B = True
   LEP A C = True
   LEP B B = True
   LEP B C = True
   LEP C C = True
   LEP B A = False
   LEP C A = False
   LEP C B = False   
   
sLep :: Sing p -> Sing q -> Sing (LEP p q) 
sLep SA SA = STrue
sLep SA SB = STrue
sLep SA SC = STrue
sLep SB SB = STrue
sLep SB SC = STrue
sLep SC SC = STrue
sLep SB SA = SFalse
sLep SC SA = SFalse
sLep SC SB = SFalse

type family LOK (s :: STRange) (p :: P) :: Bool where
   LOK Zero p = True
   LOK (Span a u) p = LEP u p
   
type family ROK (p :: P)  (s :: STRange)  :: Bool where   
   ROK p Zero = True
   ROK p (Span l b) = LEP p l
   
type family ROut (s :: STRange) (p :: P) (t ::STRange) :: STRange where   
  ROut Zero p Zero = Span p p 
  ROut Zero p (Span a u) = Span p u
  ROut (Span l b) p Zero = Span l p
  ROut (Span l a) p (Span b u) = Span l u

data BST3 (s :: STRange) where
  Leaf3 :: BST3 Zero
  Node3 :: (So (LOK l p), So (ROK p r)) => BST3 l -> Sing p -> BST3 r -> BST3 (ROut l p r)

-- Oops, can't write insert for this type
  
type family ORange (r :: STRange) (y :: P) :: STRange  where
     ORange Zero y = Span y y
     ORange (Span l u) y = If (LEP y l) (Span y u) (If (LEP u y) (Span l y) (Span l u))
  
insert3 :: Sing y -> BST3 r -> BST3 (ORange r y)
insert3 y Leaf3 = Node3 Leaf3 y Leaf3
insert3 y (Node3 lt p rt) = case sLep y p of 
  STrue -> undefined -- Node3 (insert3 y lt) p rt
  SFalse -> undefined -- Node3 lt p (insert3 y rt)

-- Section 4
  
data TB p = Top | Actual p | Bot deriving (Eq)

-- a type class for term-level ordering
instance Ord p => Ord (TB p) where
  _ <= Top = True
  (Actual a) <= (Actual b) = a <= b
  Bot <= _ = True
  _ <= _ = False
  
type family LE (a :: TB k)(b :: TB k) where
  LE a Top = True
  LE (Actual a) (Actual b) = LEP a b
  LE Bot b = True
  LE a b = False
  

data BST4 l u where 
  Leaf4 :: BST4 l u   
  Node4 :: (So (LE l (Actual p)), So (LE (Actual p) r)) =>
    BST4 l (Actual p) -> Sing p -> BST4 (Actual p) u -> BST4 l u

-- still can't define insert
  
-- Section 5  
  
-- one way or another. We can't just use True / False because that doesn't
-- give us the right evidence.  
-- However: this strategy is limited to relations
-- that are 'obviously' anti-symmetric.
  
data OWOTO p q where
  L  :: (So (LEP x y)) => OWOTO x y
  R  :: (So (LEP y x)) => OWOTO x y

owoto :: Sing p -> Sing q -> OWOTO p q 
owoto SA SA = L
owoto SA SB = L
owoto SA SC = L
owoto SB SB = L
owoto SB SC = L
owoto SC SC = L
owoto SB SA = R
owoto SC SA = R
owoto SC SB = R


-- Section 6
  
-- Skipping general relation stuff. Will use P -> P -> * instead of uncurried version.             
              
-- Section 7


-- Some pivot value p exists, where s holds before p and t holds after p
data Pivot s t l u where
  Piv :: s l (Actual p) -> Sing p -> t (Actual p) u -> Pivot s t l u


-- some data, with a proof about the bounds
data Lift b l u = So (LE l u) => Lift (b l u)

-- actually no data
data U2 l u = U2

-- an element within some bounds
-- this is sort of like "Pivot LE LE l u", but we need to turn LE into a proposition 
type Interval l u = Pivot (Lift U2) (Lift U2) l u
-- smart constructor for intervals
int :: (So (LE l (Actual p)), So (LE (Actual p) u)) => Sing p -> Interval l u
int p = Piv (Lift U2) p (Lift U2)

data BST7 (l :: (TB P)) (u :: (TB P)) where
  Leaf7 :: BST7 l u
  Node7 :: Pivot (Lift BST7) (Lift BST7) l u -> BST7 l u
  
insert7 :: Interval l u -> BST7 l u -> BST7 l u 
insert7 (Piv (Lift _) y (Lift _)) Leaf7 = Node7 (Piv (Lift Leaf7) y (Lift Leaf7))
insert7 yy@(Piv (Lift _) y (Lift _)) (Node7 (Piv (Lift lt) p (Lift rt))) = case owoto y p of
  L -> Node7 (Piv (Lift (insert7 (int y) lt)) p (Lift rt))
  R -> Node7 (Piv (Lift lt) p (Lift (insert7 (int y) rt)))
  
-- Section 8

data BST8 (l :: (TB P)) (u :: (TB P)) where
  Leaf8 :: So (LE l u) => BST8 l u
  Node8 :: Pivot BST8 BST8 l u -> BST8 l u
  
insert8 :: Interval l u -> BST8 l u -> BST8 l u 
insert8 (Piv (Lift _) y (Lift _)) Leaf8 = Node8 (Piv Leaf8 y Leaf8)
insert8 (Piv (Lift _) y (Lift _)) (Node8 (Piv lt p rt)) = case owoto y p of
  L -> Node8 (Piv (insert8 (int y) lt) p rt)
  R -> Node8 (Piv lt p (insert8 (int y) rt))
  
rotR :: BST8 l u -> BST8 l u
rotR (Node8 (Piv (Node8 (Piv lt m mt)) p rt)) = Node8 (Piv lt m (Node8 (Piv mt p rt)))
rotR t = t
  
-- the kind signature here is MANDATORY         
data OList (l :: TB P) (u :: TB P) where         
  Nil  :: So (LE l u) => OList l u
  Cons :: Pivot (Lift U2) OList l u -> OList l u 
  
oinsert :: Interval l u -> OList l u -> OList l u  
oinsert (Piv (Lift _) y (Lift _)) Nil = Cons (Piv (Lift U2) y Nil)
oinsert (Piv (Lift _) y (Lift _)) (Cons (Piv (Lift U2) p xs)) =
  case owoto y p of
  L -> Cons (Piv (Lift U2) y (Cons (Piv (Lift U2) p xs)))
  R -> Cons (Piv (Lift U2) p (oinsert (int y) xs))
  
  
-- Section 16  (Non-generic 2-3 trees)
  
$(singletons [d|
    data Nat = O | S Nat deriving (Eq, Ord) 
                         
                         |])
  
data TwoThree (h :: Nat) (l :: TB P) (u :: TB P) where  
  Leaf23 :: So (LE l u) => TwoThree O l u
  Node23_2 :: Pivot (TwoThree h) (TwoThree h) l u -> TwoThree (S h) l u
  Node23_3 :: Pivot (TwoThree h) (Pivot (TwoThree h) (TwoThree h)) l u -> TwoThree (S h) l u

node2 lt p rt = Node23_2 (Piv lt p rt)
node3 lt p mt r rt = Node23_3 (Piv lt p (Piv mt r rt))

data InsertResult h l u where
  Same :: TwoThree h l u -> InsertResult h l u
  Bump :: Pivot (TwoThree h) (TwoThree h) l u -> InsertResult h l u

ins23 :: Sing h -> Interval l u -> TwoThree h l u -> InsertResult h l u
ins23 h (Piv (Lift _) y (Lift _)) t = case (h, t) of 
  (SO, Leaf23) -> Bump (Piv Leaf23 y Leaf23)
  -- (SS h, Leaf23)   -> impossible case
  -- (SO, Node23_2 _) -> error
  -- (SO, Node23_3 _) -> error
  (SS h, Node23_2 (Piv lt p rt)) -> case owoto y p of 
    L -> case ins23 h (int y)  lt of 
      Same lt' -> Same (node2 lt' p rt)
      Bump (Piv llt r lrt) -> Same (node3 llt r lrt p rt)
    R -> case ins23 h (int y)  rt of
      Same rt' -> Same (node2 lt p rt')
      Bump (Piv rlt r rrt) -> Same (node3 lt p rlt r rrt)
  (SS h, Node23_3 (Piv lt p rt@(Piv mt q rrt))) -> case owoto y p of 
    L -> case ins23 h (int y)  lt of 
      Same lt' -> Same (node3 lt' p mt q rrt)
      Bump (Piv llt r lrt) -> 
        Bump (Piv (node2 llt r lrt) p (node2 mt q rrt))
    R -> case owoto y q of 
      L -> case ins23 h (int y) mt of
        Same mt' -> Same (node3 lt p mt' q rrt)
        Bump (Piv mlt r mrt) -> 
          Bump (Piv (node2 lt p mlt) r (node2 mrt q rrt))
      R -> case ins23 h (int y) rrt of   
        Same rt' -> Same (node3 lt p mt q rt')
        Bump (Piv rlt r rrt') -> 
          Bump (Piv (node2 lt p mt) q (node2 rlt r rrt'))
          
data Tree23 =
  forall h. Tree23 (Sing h) (TwoThree h Bot Top)
  
insert :: forall (p :: P). Sing p -> Tree23 -> Tree23  
insert p (Tree23 h t) = case ins23 h (int p) t of 
  Same t' -> Tree23 h t'
  Bump (Piv lt r rt) -> Tree23 (SS h) (node2 lt r rt)
  
-- Section 17 -- Deletion

-- transitivity

-- trans :: (So (LEQ x y), So (LEQ y z)) => 

data Del23 h l u = 
    DelShort (Short23 h l u)
  | DelSame (TwoThree h l u) 
    
data Short23 h l u where
  -- h cannot be 0
  Short :: TwoThree h l u -> Short23 (S h) l u
  
  

data Re2 h l u where
  ReShort :: Short23 (S h) l u -> Re2 h l u
  RePivot :: Pivot (TwoThree h) (TwoThree h) l u -> Re2 h l u
  
-- rebalancing  
d2t :: Sing h -> Pivot (Del23 h) (TwoThree h) l u -> Re2 h l u
d2t h (Piv (DelSame lp) p pu) = RePivot (Piv lp p pu)
-- d2t S0 impossible  
d2t (SS h) (Piv (DelShort (Short lp)) p (Node23_2 (Piv pq q qu))) = 
   ReShort (Short (node3 lp p pq q qu))
d2t (SS h) (Piv (DelShort (Short lp)) p (Node23_3 (Piv pq q (Piv qr r ru)))) = 
   RePivot (Piv (node2 lp p pq) q (node2 qr r ru))
   
-- ? can we make Sing h an implicit argument?   
t2d :: Sing h -> Pivot (TwoThree h) (Del23 h) l u -> Re2 h l u   
t2d h (Piv lp p (DelSame pu)) = RePivot (Piv lp p pu)
-- t2d S0 impossible
t2d (SS h) (Piv (Node23_2 (Piv ln n np)) p (DelShort (Short pu))) = 
  ReShort (Short (node3 ln n np p pu))
t2d (SS h) (Piv (Node23_3 (Piv lm m (Piv mn n np))) p (DelShort (Short pu))) =  
  RePivot (Piv (node2 lm m mn) n (node2 np p pu))
  
  
-- The adaptor |rd| allows us to throw away the knowledge that the full
-- height reconstruction must be a 2-node if we do not need it, but the
-- extra detail allows us to use 2-node reconstructors in the course of
-- 3-node reconstruction.   
rd :: Re2 h l u -> Del23 (S h) l u  
rd (ReShort (Short s)) = DelShort (Short s)
rd (RePivot (Piv lp p pu)) = DelSame (node2 lp p pu)

r3t :: Pivot (Re2 h) (TwoThree h) l u -> Del23 (S h) l u
r3t (Piv (RePivot (Piv lm m mp)) p pu) = DelSame (node3 lm m mp p pu)
r3t (Piv (ReShort (Short lp)) p pu) = DelSame (node2 lp p pu)

t3r :: Pivot (TwoThree h) (Re2 h) l u -> Del23 (S h) l u
t3r (Piv lp p (RePivot (Piv pq q qu))) = DelSame (node3 lp p pq q qu)
t3r (Piv lp p (ReShort (Short pu)))    = DelSame (node2 lp p pu)

-- keep extracted element on the right and hide the ordering proof
lr -\ r = Piv lr r (Lift U2)

--  extracting the extreme right key from a nonempty left subtree
extr  :: Sing h -> TwoThree (S h) l u  -> Pivot (Del23 (S h)) (Lift U2) l u
extr SO (Node23_2 (Piv lr r Leaf23)) = (DelShort (Short lr)) -\ r 
extr SO (Node23_3 (Piv lp p (Piv pr r Leaf23))) = (DelSame (node2 lp p pr)) -\ r
extr (SS h) (Node23_2 (Piv lp p pu)) = case extr h pu of 
  (Piv pr r (Lift U2)) -> rd (t2d (SS h) (Piv lp p pr)) -\ r
extr (SS h) (Node23_3 (Piv lp p (Piv pq q qu))) = case extr h qu of   
  (Piv qr r (Lift U2)) -> t3r (Piv lp p (t2d (SS h) (Piv pq q qr))) -\ r
  
--  To delete the pivot key from between two trees, we extract the rightmost key
-- from the left tree, then weaken the bound on the right tree
-- (traversing its left spine only). Again, we are sure that if the height
-- remains the same, we shall deliver a 2-node.

trans :: forall (x :: TB P)(p :: P) (z :: TB P) (a :: *). 
         (So (LE x (Actual p)), So (LE (Actual p) z)) => Proxy x -> Sing p -> Proxy z -> (So (LE x z) => a) -> a
trans = undefined

delp :: forall h l u . Sing h -> Pivot (TwoThree h) (TwoThree h) l u -> Re2 h l u
delp SO (Piv Leaf23 p Leaf23) = ReShort (Short leaf) where 
  leaf = trans (undefined :: Proxy l) p (undefined :: Proxy u) Leaf23
delp (SS h) (Piv lp (p :: Sing p) pu) = case extr h lp of 
  (Piv lr (r :: Sing r) (Lift U2)) -> d2t (SS h) (Piv lr r (weak (SS h) pu)) where
     weak :: forall h' u'. Sing h' -> TwoThree h' (Actual p) u' -> 
             TwoThree h' (Actual r) u'
     weak SO Leaf23 = leaf where
       leaf = trans (undefined :: Proxy (Actual r)) p (undefined :: Proxy u') Leaf23
     weak (SS h) (Node23_2 (Piv pq q qu)) = (Node23_2 (Piv (weak h pq) q qu))
     weak (SS h) (Node23_3 (Piv pq q qu)) = (Node23_3 (Piv (weak h pq) q qu))
       
-- Conor notes that it is unfortunate the weak must be executed, as it is essentially
-- an identity function. Would be good to see if we could work subtyping into the system        
-- somehow....       

-- finding the key to delete       
del23 :: Sing h -> Interval l u -> TwoThree h l u -> Del23 h l u
del23 SO _ Leaf23 = DelSame Leaf23
del23 (SS h) (Piv (Lift U2) y (Lift U2)) t = case t of 
  (Node23_2 (Piv lp p pu)) -> case y %:== p of 
      STrue -> rd (delp h (Piv lp p pu))
      SFalse -> case owoto y p of 
        L -> rd (d2t h (Piv (del23 h (int y) lp) p pu))
        R -> rd (t2d h (Piv lp p (del23 h (int y) pu)))
  (Node23_3 (Piv lp p (Piv pq q qu))) -> case y %:== p of 
      STrue -> r3t (Piv (delp h (Piv lp p pq)) q qu)
      SFalse -> case owoto y p of
        L -> r3t (Piv (d2t h (Piv (del23 h (int y) lp) p pq)) q qu)
        R -> case y %:== q of 
          STrue -> t3r (Piv lp p (delp h (Piv pq q qu)))
          SFalse -> case owoto y q of 
            L -> r3t (Piv (t2d h (Piv lp p (del23 h (int y) pq))) q qu)
            R -> t3r (Piv lp p (t2d h (Piv pq q (del23 h (int y) qu))))
            
-- Conor doesn't include it, but we should finish it out            

-- this should be in the TypeLits library!
spred :: Sing (S n) -> Sing n
spred (SS n) = n

-- top-level deletion function
delete :: forall (p :: P). Sing p -> Tree23 -> Tree23   
delete p (Tree23 h t) = case del23 h (int p) t of 
  DelShort (Short t') -> Tree23 (spred h) t'
  DelSame t -> Tree23 h t
    