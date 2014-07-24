{-# LANGUAGE TemplateHaskell, GADTs, DataKinds, PolyKinds, TypeFamilies, RankNTypes, TypeOperators, UndecidableInstances, KindSignatures, FlexibleContexts, FlexibleInstances, ScopedTypeVariables, AllowAmbiguousTypes, ConstraintKinds #-}

-- investigating Conor's "How to keep your neighbors in order" in Haskell

module Order where

import Data.Singletons.Prelude
import Data.Singletons.TH

import qualified Test.QuickCheck (elements)
import Test.QuickCheck hiding (elements)
import Data.List (nub,sort)
import Control.Monad hiding (guard)

-- Section 2.

-- Conor starts out with a large elimination that changes a boolean value into
-- a proposition. In Haskell, we repressent propositions by classes or by
-- types. The latter is more expressive, but inconsistent. So we'll stick with 
-- classes where we can.

class So (b :: Bool) where
instance So True   

-- Conor's next definition, of the squash operator !, is unnecessary, at least for
-- 'So'. Haskell will never let you see dictionaries, so they are already
-- hidden. Furthermore, 'So' has no evidence, so it will be represented with 0-bits.

-- Section 3.

-- like Conor, we'll fix a parameter for the data in our trees.  we'll also
-- make sure that we can promote it and compare it at the type level.

  
$(singletons [d| 
              
   data P = A | B | C deriving (Eq, Ord, Show)
                               
   -- for some reason, the Ord instance doesn't work                            
   lep :: P -> P -> Bool
   lep A A = True
   lep A B = True
   lep A C = True
   lep B B = True
   lep B C = True
   lep C C = True
   lep B A = False
   lep C A = False
   lep C B = False  

                      |])    

--  The Wrong attempt.                                               
  
$(singletons [d| 
                               
   data STRange = Zero | Span P P                       
                                            
   data Tree = Leaf | Node Tree P Tree

   guard :: Bool -> Maybe a -> Maybe a
   guard True mx = mx
   guard False _ = Nothing

   -- we don't need these as term functions, but as singletons can 
   -- promote them, we can write them this way
   lOK :: STRange -> P -> Bool
   lOK Zero p = True
   lOK (Span a u) p = lep u p 

   rOK ::  P -> STRange -> Bool
   rOK p Zero = True
   rOK p (Span l b) = lep p l

   rOut :: STRange -> P -> STRange -> STRange 
   rOut Zero p Zero = Span p p 
   rOut Zero p (Span a u) = Span p u
   rOut (Span l b) p Zero = Span l p
   rOut (Span l a) p (Span b u) = Span l u

   oRange :: STRange -> P -> STRange  
   oRange Zero y = Span y y
   oRange (Span l u) y = 
      if lep y l then Span y u
        else if lep u y then Span l y 
        else Span l u

   |])                                                   

-- note, some bug in singletons library prevents this from promotion.

valid :: Tree -> Maybe STRange
valid Leaf = Just Zero
valid (Node l p r) = 
     case (valid l, valid r) of 
       (Just Zero, Just Zero) -> Just (Span p p)
       (Just Zero, Just (Span c d)) -> guard (lep p c) (Just (Span p d))
       (Just (Span a b), Just Zero) -> guard (lep b p) (Just (Span a p))
       (Just (Span a b), Just (Span c d)) -> 
          guard (lep b p) (guard (lep p c) (Just (Span a d)))
       (_ , _) -> Nothing
  
-- BSTs with refinement that guarantees ordering

data BST3 (s :: STRange) where
  Leaf3 :: BST3 Zero
  Node3 :: (So (LOK l p), So (ROK p r)) => BST3 l -> Sing p -> BST3 r -> BST3 (ROut l p r)

-- As Conor notes, we can't readily write insert for this type
  
insert3 :: Sing y -> BST3 r -> BST3 (ORange r y)
insert3 y Leaf3 = Node3 Leaf3 y Leaf3
insert3 y (Node3 lt p rt) = case sLep y p of 
  STrue -> undefined -- Node3 (insert3 y lt) p rt
  SFalse -> undefined -- Node3 lt p (insert3 y rt)

-- Section 4
  
$(singletons [d|
              
    -- extending types with top and bottom elements
    -- Actual is # in the Agda version              
    data TB p = Top | Actual p | Bot deriving (Eq)
                                                                      
  |])


  
-- type-level function for ordering        
type family LE (a :: TB P)(b :: TB P) where
  LE a Top = True
  LE (Actual a) (Actual b) = Lep a b
  LE Bot b = True
  LE a b = False

{- Note that we can't write the singleton version of this 
   function as using the same GADT pattern
   matching isn't as clever as closed type families. 
   So the last case doesn't type check. 

sLE :: Sing a -> Sing b -> Sing (LE a b) 
sLE a STop = STrue
sLE (SActual a) (SActual b) = sLep a b 
sLE SBot b = STrue
sLE a b = SFalse

-}
  
-- instead we need to expand all of the cases out 
-- (It would be good if singletons could automatically 
-- generate this definition for closed type families)  
sLE :: Sing a -> Sing b -> Sing (LE a b)   
sLE SBot SBot = STrue      
sLE SBot (SActual b) = STrue
sLE SBot STop = STrue
sLE (SActual a) SBot = SFalse   
sLE (SActual a) (SActual b) = sLep a b
sLE (SActual a) STop = STrue
sLE STop SBot = SFalse
sLE STop (SActual b) = SFalse
sLE STop STop = STrue       

    
-- We can now index search trees by a pair of loose bounds, not
-- measuring the range of the contents exactly, but constraining it
-- sufficiently. At each node, we can require that the pivot falls in the
-- interval, then use the pivot to bound the subtrees.

data BST4 l u where 
  Leaf4 :: BST4 l u   
  Node4 :: (So (LE l (Actual p)), So (LE (Actual p) u)) =>
    BST4 l (Actual p) -> Sing p -> BST4 (Actual p) u -> BST4 l u

-- However, as Conor says, we still can't define insert without knowing that 
-- Le (Actual y) (Actual p) ~ False implies that Le (Actual p) (Actual y) ~ True  
-- We can write a short proof that that is the case, but (in Haskell) this proof must be 
-- executed at run time.
  
antisym :: forall (y :: P) (p :: P) (a :: *). 
           (Lep y p ~ False) => Sing y -> Sing p -> (So (Lep p y) => a) -> a 
antisym SB SA a = a
antisym SC SA a = a
antisym SC SB a = a
-- all other cases do not type check.
-- antisym SA SA a = undefined  
  
insert4 :: forall (y :: P)(l :: TB P)(u :: TB P). 
           (So (LE l (Actual y)), So (LE (Actual y) u)) => Sing y -> BST4 l u -> BST4 l u 
insert4 y Leaf4 = Node4 Leaf4 y Leaf4
insert4 y (Node4 lt p rt) = case sLep y p of 
  STrue -> Node4 (insert4 y lt) p rt
  SFalse -> Node4 lt p (antisym y p (insert4 y rt))
  
-- Section 5    
  
-- We're going to redefine our term level discrimator
-- for bounded Ps that will give us 
-- more properties directly from the definition.  
    
-- Conor calls this function 'owoto' or 'one way or the other'
-- The result of this discriminator gives us the evidence that we need, 
-- either So(Lep p q) or So (Lep q p).
  
-- Conor defines this result type using combinators like below, but because of (a)   
-- ambiguity and (b) weaker view patterns, we'll just define a new datatype.

{-
data Constrain (b :: Bool) = (So b) => Bang

type OWOTO (p :: P) (q :: P) = Either (Constrain (Lep p q)) (Constrain (Lep q p))

le :: (So (Lep p q)) => OWOTO p q
le = Left Bang
ge :: (So (Lep q p)) => OWOTO p q
ge = Right Bang

-}

data OWOTO (p :: P) (q :: P) = So (Lep p q) => LE | So (Lep q p) => GE


{-  
-- also could be written as a GADT
data OWOTO p q where
  LE  :: (So (Lep x y)) => OWOTO x y
  GE  :: (So (Lep y x)) => OWOTO x y
-}


owoto :: forall (p :: P) (q :: P). Sing p -> Sing q -> OWOTO p q 
owoto SA SA = LE
owoto SA SB = LE
owoto SA SC = LE
owoto SB SB = LE
owoto SB SC = LE
owoto SC SC = LE
owoto SB SA = GE
owoto SC SA = GE
owoto SC SB = GE


-- Section 6

-- Skipping general relation stuff. Will use P -> P -> * instead of uncurried version (P,P) -> *.             
              
-- Section 7


-- some data, with a proof about the bounds
data Lift b l u = So (LE l u) => Lift (b l u)

-- actually no data
data U2 l u = U2

-- note that (Lift U2) is analogous to Conor's !

-- Some pivot value p exists, where s holds before p and t holds after p
data Pivot s t l u where
  Piv :: (SingI p) => s l (Actual p) -> Sing p -> t (Actual p) u -> Pivot s t l u

-- an element within some bounds
-- this is sort of like "Pivot LE LE l u", but we need to turn LE into a proposition 
type Interval l u = Pivot (Lift U2) (Lift U2) l u

-- smart constructor for intervals
int :: (So (LE l (Actual p)), So (LE (Actual p) u), SingI p) => Sing p -> Interval l u
int p = Piv (Lift U2) p (Lift U2)

-- now we can define binary search trees & insertion where the order is guaranteed. 

data BST7 (l :: (TB P)) (u :: (TB P)) where
  Leaf7 :: BST7 l u
  Node7 :: Pivot (Lift BST7) (Lift BST7) l u -> BST7 l u
  
insert7 :: Interval l u -> BST7 l u -> BST7 l u 
insert7 (Piv (Lift _) y (Lift _)) Leaf7 = Node7 (Piv (Lift Leaf7) y (Lift Leaf7))
insert7 yy@(Piv (Lift _) y (Lift _)) (Node7 (Piv (Lift lt) p (Lift rt))) = case owoto y p of
  LE -> Node7 (Piv (Lift (insert7 (int y) lt)) p (Lift rt))
  GE -> Node7 (Piv (Lift lt) p (Lift (insert7 (int y) rt)))
  
-- Section 8
  
-- pushing the constraints to the leaves.

data BST8 (l :: (TB P)) (u :: (TB P)) where
  Leaf8 :: So (LE l u) => BST8 l u
  Node8 :: Pivot BST8 BST8 l u -> BST8 l u
  
insert8 :: Interval l u -> BST8 l u -> BST8 l u 
insert8 (Piv (Lift _) y (Lift _)) Leaf8 = Node8 (Piv Leaf8 y Leaf8)
insert8 (Piv (Lift _) y (Lift _)) (Node8 (Piv lt p rt)) = case owoto y p of
  LE -> Node8 (Piv (insert8 (int y) lt) p rt)
  GE -> Node8 (Piv lt p (insert8 (int y) rt))
  
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
  LE -> Cons (Piv (Lift U2) y (Cons (Piv (Lift U2) p xs)))
  GE -> Cons (Piv (Lift U2) p (oinsert (int y) xs))
  
  
-- Section 16  (Non-generic 2-3 trees)
  
$(singletons [d|
    data Nat = O | S Nat deriving (Eq, Ord) 
    |])
      
  
data TwoThree :: Nat -> TB P -> TB P -> * where  
  Leaf23   :: So (LE l u) => TwoThree O l u
  Node23_2 :: Pivot (TwoThree h) (TwoThree h) l u -> TwoThree (S h) l u
  Node23_3 :: Pivot (TwoThree h) (Pivot (TwoThree h) (TwoThree h)) l u -> TwoThree (S h) l u


-- smart constructors
node2 lt p rt = Node23_2 (Piv lt p rt)
node3 lt p mt r rt = Node23_3 (Piv lt p (Piv mt r rt))

-- Could replace with an Either, but I like the more informative
-- data constructor names
data InsertResult h l u where
  Same :: TwoThree h l u -> InsertResult h l u
  Bump :: Pivot (TwoThree h) (TwoThree h) l u -> InsertResult h l u

ins23 :: Sing h -> Interval l u -> TwoThree h l u -> InsertResult h l u
ins23 h (Piv (Lift _) y (Lift _)) t = case (h, t) of 
  (SO, Leaf23) -> Bump (Piv Leaf23 y Leaf23)
  -- (SS h, Leaf23)   -> impossible
  -- (SO, Node23_2 _) -> impossible
  -- (SO, Node23_3 _) -> impossible
  (SS h, Node23_2 (Piv lt p rt)) -> case owoto y p of 
    LE -> case ins23 h (int y)  lt of 
      Same lt' -> Same (node2 lt' p rt)
      Bump (Piv llt r lrt) -> Same (node3 llt r lrt p rt)
    GE -> case ins23 h (int y)  rt of
      Same rt' -> Same (node2 lt p rt')
      Bump (Piv rlt r rrt) -> Same (node3 lt p rlt r rrt)
  (SS h, Node23_3 (Piv lt p rt@(Piv mt q rrt))) -> case owoto y p of 
    LE -> case ins23 h (int y)  lt of 
      Same lt' -> Same (node3 lt' p mt q rrt)
      Bump (Piv llt r lrt) -> 
        Bump (Piv (node2 llt r lrt) p (node2 mt q rrt))
    GE -> case owoto y q of 
      LE -> case ins23 h (int y) mt of
        Same mt' -> Same (node3 lt p mt' q rrt)
        Bump (Piv mlt r mrt) -> 
          Bump (Piv (node2 lt p mlt) r (node2 mrt q rrt))
      GE -> case ins23 h (int y) rrt of   
        Same rt' -> Same (node3 lt p mt q rt')
        Bump (Piv rlt r rrt') -> 
          Bump (Piv (node2 lt p mt) q (node2 rlt r rrt'))
          
data Tree23 =
  forall h. Tree23 (Sing h) (TwoThree h Bot Top)
  
insert :: P -> Tree23 -> Tree23  
insert p (Tree23 h t) = case (toSing p) of 
    SomeSing p' -> withSingI p'
      (case ins23 h (int p') t of 
         Same t' -> Tree23 h t'
         Bump (Piv lt r rt) -> Tree23 (SS h) (node2 lt r rt))
  
-- Look up in TwoThree trees  

member :: P -> Tree23 -> Bool 
member p (Tree23 h t) = case (toSing p) of 
    SomeSing p' -> withSingI p' (mem (int p') t)
  
mem :: forall (l :: TB P)(u :: TB P) (h :: Nat). Interval l u -> TwoThree h l u -> Bool
mem p Leaf23 = False
mem (Piv (Lift _) p (Lift _)) t = case t of 
    (Node23_2 (Piv lt r rt)) -> case p %:== r of 
       STrue -> True
       SFalse -> case owoto p r of 
         LE -> mem (int p) lt  
         GE -> mem (int p) rt
    (Node23_3 (Piv lt r (Piv mt q rt))) -> case p %:== r of 
       STrue -> True
       SFalse -> case owoto p r of 
         LE -> mem (int p) lt  
         GE -> case p %:== q of 
           STrue -> True
           SFalse -> case owoto p q of 
             LE -> mem (int p) mt 
             GE -> mem (int p) rt
             
-- Flatten (nongeneric)             
             
elements :: Tree23 -> [P]             
elements (Tree23 h t) = el t where
  el :: forall h l u. TwoThree h l u -> [P]
  el Leaf23 = []
  el (Node23_2 (Piv lt r rt)) = el lt ++ [fromSing r] ++ el rt
  el (Node23_3 (Piv lt p (Piv mt r rt))) = el lt ++ [fromSing p] ++ el mt ++ [fromSing r] ++ el rt
                                          
instance Show Tree23 where
  show (Tree23 h t) = sho t where
    sho :: forall h l u. TwoThree h l u -> String
    sho Leaf23 = "no0"
    sho (Node23_2 (Piv lt r rt)) = "(no2" ++ sho lt ++ show (fromSing r) ++ sho rt ++ ")"
    sho (Node23_3 (Piv lt p (Piv mt r rt))) = "(no3" ++ sho lt ++ show (fromSing p) ++ sho mt 
                                              ++ show (fromSing r) ++ sho rt ++ ")"
      
                                              
  
-- Section 17 -- Deletion

-- Again could replace with an Either
data Del23 h l u = 
    DelShort (Short23 h l u)
  | DelSame (TwoThree h l u) 
    
data Short23 h l u where
  -- h cannot be 0
  Short :: TwoThree h l u -> Short23 (S h) l u
  
-- Maybe inline Short23 into this type?
  
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
r3t (Piv (ReShort (Short lp)) p pu)    = DelSame (node2 lp p pu)

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
  
  
-- Transitivity  
transP :: forall (x :: P)(p :: P) (z :: P) (a :: *). 
  (So (Lep x p), So (Lep p z)) => Sing x -> Sing p -> Sing z -> (So (Lep x z) => a) -> a  
transP px ps pz a = undefined

trans :: forall (x :: TB P)(p :: P) (z :: TB P) (a :: *). 
         (So (LE x (Actual p)), So (LE (Actual p) z)) => Sing x -> Sing p -> Sing z -> (So (LE x z) => a) -> a
trans _ p STop a = a
trans SBot p _ a = a
trans (SActual l) p (SActual u) a = transP l p u a
-- trans STop p _ impossible
-- trans (Actual l) p SBot _ impossible


--  To delete the pivot key from between two trees, we extract the rightmost key
-- from the left tree, then weaken the bound on the right tree
-- (traversing its left spine only). Again, we are sure that if the height
-- remains the same, we shall deliver a 2-node.

delp :: forall h l u . (SingI l, SingI u) => Sing h -> Pivot (TwoThree h) (TwoThree h) l u -> Re2 h l u
delp SO (Piv Leaf23 p Leaf23) = ReShort (Short leaf) where 
  leaf = trans (sing :: Sing l) p (sing :: Sing u) Leaf23
delp (SS h) (Piv lp (p :: Sing p) pu) = case extr h lp of 
  (Piv lr (r :: Sing r) (Lift U2)) -> d2t (SS h) (Piv lr r (weak (SS h) pu)) where
     weak :: forall h' u'. (SingI u') => Sing h' -> TwoThree h' (Actual p) u' -> 
             TwoThree h' (Actual r) u'
     weak SO Leaf23 = leaf where
       leaf = trans (sing :: Sing (Actual r)) p (sing :: Sing u') Leaf23
     weak (SS h) (Node23_2 (Piv pq q qu)) = (Node23_2 (Piv (weak h pq) q qu))
     weak (SS h) (Node23_3 (Piv pq q qu)) = (Node23_3 (Piv (weak h pq) q qu))
       
-- Conor notes that it is unfortunate the weak must be executed, as it is essentially
-- an identity function. Would be good to see if we could work subtyping into the system        
-- somehow....       
     
-- I'll note that the proof of transitivity also unfortunately computational. I think this is
-- an example where Haskell's treatment of erasable arguments is not sufficient. This is because there
-- is no way to do induction during type class resolution.     

-- Now that we can remove a key,
-- we need only ﬁnd the key to remove. I have chosen to delete
-- the topmost occurrence of the given key, and to return the tree
-- unscathed if the key does not occur at all.

del23 :: (SingI l, SingI u) => Sing h -> Interval l u -> TwoThree h l u -> Del23 h l u
del23 SO _ Leaf23 = DelSame Leaf23
del23 (SS h) (Piv (Lift U2) y (Lift U2)) t = case t of 
  (Node23_2 (Piv lp p pu)) -> case y %:== p of 
      STrue -> rd (delp h (Piv lp p pu))
      SFalse -> case owoto y p of 
        LE -> rd (d2t h (Piv (del23 h (int y) lp) p pu))
        GE -> rd (t2d h (Piv lp p (del23 h (int y) pu)))
  (Node23_3 (Piv lp p (Piv pq q qu))) -> case y %:== p of 
      STrue -> r3t (Piv (delp h (Piv lp p pq)) q qu)
      SFalse -> case owoto y p of
        LE -> r3t (Piv (d2t h (Piv (del23 h (int y) lp) p pq)) q qu)
        GE -> case y %:== q of 
          STrue -> t3r (Piv lp p (delp h (Piv pq q qu)))
          SFalse -> case owoto y q of 
            LE -> r3t (Piv (t2d h (Piv lp p (del23 h (int y) pq))) q qu)
            GE -> t3r (Piv lp p (t2d h (Piv pq q (del23 h (int y) qu))))
            
-- Conor doesn't include it, but we should finish it out            

-- this should be in the TypeLits library!
spred :: Sing (S n) -> Sing n
spred (SS n) = n


-- top-level deletion function
delete :: P -> Tree23 -> Tree23   
delete p (Tree23 h t) = case (toSing p) of 
    SomeSing p' -> withSingI p'   
      (case del23 h (int p') t of 
         DelShort (Short t') -> Tree23 (spred h) t'
         DelSame t -> Tree23 h t)

empty :: Tree23
empty = Tree23 SO Leaf23

--  The elements of the set are sorted.

prop_elements :: Tree23 -> Bool
prop_elements x = elements x == (sort (elements x)) &&
      all (\y -> member y x) (elements x)

prop_insert1 :: P -> Tree23 -> Bool
prop_insert1 x t = member x (insert x t)

-- And that the new set also contains all of the original elements.

prop_insert2 :: P -> Tree23 -> Bool
prop_insert2 x t = all (\y -> member y t') (elements t) where 
  t' = insert x t
  
prop_delete_spec1 :: Tree23 -> Bool
prop_delete_spec1 t = all (\x -> not (member x (delete x t))) (elements t)

prop_delete_spec2 :: Tree23 -> Bool
prop_delete_spec2 t = all (\(x,y) -> x == y || (member y (delete x t))) allpairs where
  allpairs = [ (x,y) | x <- elements t, y <- elements t ]

prop_delete_spec3 :: Tree23 -> P -> Property
prop_delete_spec3 t x = not (x `elem` elements t) ==> (elements (delete x t) == elements t)

{-
check_delete = do
  quickCheckWith (stdArgs {maxSuccess=1000}) prop_delete_spec1
  quickCheckWith (stdArgs {maxSuccess=1000}) prop_delete_spec2
  quickCheckWith (stdArgs {maxSuccess=1000}) prop_delete_spec3
-}
  
  
instance Arbitrary P where  
  arbitrary = Test.QuickCheck.elements [A,B,C]
  
instance (Ord a) => Arbitrary Tree23  where
  arbitrary = liftM (foldr insert empty) arbitrary
  