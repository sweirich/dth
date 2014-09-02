-- Original version by Dan Licata for OPLSS. 
-- Many modifications by Stephanie Weirich for ICFP 14 presentation.  

open import Ordering
open import Data.Sum

module RBT (A : Set) (compare : A → A → Ordering) where 

    data Nat : Set where
      Zero : Nat
      Suc  : Nat → Nat

    data Color : Set where
      R : Color
      B : Color

    data Tree : Color → Nat → Set where
      E  : Tree B Zero
      TR : ∀ {n} → Tree B n → A → Tree B n → Tree R n 
      TB : ∀ {n c1 c2} → (Tree c1 n) → A → (Tree c2 n) → Tree B (Suc n)

    -- a well-formed red-black tree. Root is black, but height 
    -- could be anything.
    data RBT : Set where
       Root : {n : Nat} → Tree B n → RBT

    -- example: reverse the tree
    rev : ∀ {c n} → Tree c n → Tree c n
    rev E = E
    rev (TR t x t₁) = TR (rev t₁) x (rev t)
    rev (TB t x t₁) = TB (rev t₁) x (rev t)

    -- example program: calculate the maximum of a non-empty tree.
    mutual
      maxB : ∀ {n} → Tree B (Suc n) → A
      maxB (TB _ x E)    = x
      maxB (TB _ _ (TR a x b)) = maxR (TR a x b)
      maxB (TB _ _ (TB a x b)) = maxB (TB a x b)

      maxR : ∀ {n} → Tree R n → A
      maxR (TR _ x E)    = x
      maxR (TR _ _ (TB a x b)) = maxB (TB a x b)

    -- for insertion, sometimes we need to break the invariant.
    incr-if-black : Color → Nat → Nat
    incr-if-black R x = x
    incr-if-black B x = Suc x

    -- hide the color of a well-formed, non-empty tree
    data HTree : Nat → Set where
       HR : {m : Nat} → Tree R m → HTree m
       HB : {m : Nat} → Tree B (Suc m) → HTree (Suc m)
    
    -- captures the height, but not the fact that red nodes could have black children
    data AlmostTree : Nat → Set where
      AT :  ∀ {n c1 c2}
              → (c : Color)
              → Tree c1 n → A → Tree c2 n
              → AlmostTree (incr-if-black c n)

    -- input color is implicitly red
    balance-left-red : {n : Nat}{c : Color} → HTree n → A → Tree c n → AlmostTree n
    balance-left-red (HR l) x r = AT R l x r
    balance-left-red (HB l) x r = AT R l x r

    -- note: we cannot give balance-left-red  th type
    -- ∀ {n c} → AlmostTree n → A → Tree c n → AlmostTree n
    -- as it is not strong enough to show totality. That type allows the 
    -- left subtree to be red, with a red child. 
    -- There is no way to recover from that situation.

    balance-right-red : ∀ {n c} → Tree c n → A → HTree n → AlmostTree n
    balance-right-red l x (HR r) = AT R l x r
    balance-right-red l x (HB r) = AT R l x r


    -- input color is implicitly black 
    balance-left-black : {n : Nat}{c : Color} → AlmostTree n → A → Tree c n → HTree (Suc n)

    -- these are the two rotation cases
    balance-left-black (AT R (TR a x b) y c) z d = HR (TR (TB a x b) y (TB c z d))
    balance-left-black (AT R a x (TR b y c)) z d = HR (TR (TB a x b) y (TB c z d))
    -- need to expand the catch-all, because the *proof* is different 
    -- in each case.  
    balance-left-black (AT B a  x b) y r = HB (TB (TB a x b) y r)
    balance-left-black (AT R E x E) y r = HB (TB (TR E x E) y r)
    balance-left-black (AT R (TB a1 x1 a2) x (TB b1 y1 b2)) y c = HB (TB (TR (TB a1 x1 a2) x (TB b1 y1 b2)) y c)

    -- input color is implicitly black 
    balance-right-black : ∀ {n c} → Tree c n → A → AlmostTree n → HTree (Suc n)
    -- these are the two rotation cases
    balance-right-black a x (AT R (TR b y c)  z d) = HR (TR (TB a x b) y (TB c z d))
    balance-right-black a x (AT R b y (TR c z d)) = HR (TR (TB a x b) y (TB c z d))
    -- catch-all 
    balance-right-black a x (AT R E y E) = HB (TB a x (TR E y E))
    balance-right-black a x (AT R (TB l y r) x' (TB l' y' r')) = 
           HB (TB a x (TR (TB l y r) x' (TB l' y' r')))
    balance-right-black a x (AT B l y r) = HB (TB a x (TB l y r))

    -- forget that the top node of the tree is well-formed
    forget : ∀ {n} → HTree n → AlmostTree n
    forget (HR (TR l x r)) = AT R l x r
    forget (HB (TB l x r)) = AT B l x r

    mutual
      ins-black : {n : Nat} (t : Tree B n) (x : A) → HTree n
      ins-black E x = HR (TR E x E)
      ins-black (TB l y r) x with compare x y
      ... | LT  = balance-left-black (ins l x) y r
      ... | GT  = balance-right-black l x (ins r x)
      ... | EQ  = HB (TB l x r)

      ins : {n : Nat}{c : Color} (t : Tree c n) (x : A) → AlmostTree n
      ins (TR l y r) x with compare x y 
      ... | LT = balance-left-red (ins-black l x) y r
      ... | GT = balance-right-red l y (ins-black r x)
      ... | EQ = AT R l x r
      ins (TB l y r) x = forget (ins-black (TB l y r) x)
      ins E x          = forget (ins-black E x)

    blacken-root : ∀ {n} → HTree n → RBT
    blacken-root (HR (TR l x r)) = Root (TB l x r)
    blacken-root (HB (TB l x r)) = Root (TB l x r)

    insert : RBT → A → RBT
    insert (Root t) x = blacken-root (ins-black t x)
