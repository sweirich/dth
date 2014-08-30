-- Original version by Dan Licata for OPLSS. 
-- Minor changes by Stephanie Weirich for ICFP 14 presentation.  

open import Ordering
open import Data.Sum

module RBT (A : Set) (compare : A -> A -> Ordering) where 

    data Either (A B : Set) : Set where
      Left  : A -> Either A B
      Right : B -> Either A B

    data Nat : Set where
      Zero : Nat
      Suc  : Nat -> Nat

    data Color : Set where
      R : Color
      B : Color

    data Tree : Color -> Nat → Set where
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
      maxB : ∀ {n} -> Tree B (Suc n) -> A
      maxB (TB _ x E)    = x
      maxB (TB _ _ (TR a x b)) = maxR (TR a x b)
      maxB (TB _ _ (TB a x b)) = maxB (TB a x b)

      maxR : ∀ {n} -> Tree R n -> A
      maxR (TR _ x E)    = x
      maxR (TR _ _ (TB a x b)) = maxB (TB a x b)

    -- for insertion, sometimes we need to break the invariant.
    incr-if-black : Color -> Nat -> Nat
    incr-if-black R x = x
    incr-if-black B x = Suc x

    -- hide the color of a well-formed tree
    data HTree : Nat -> Set where
       HideColor : {c : Color}{m : Nat} -> Tree c m -> HTree m
    
    -- captures the height, but not the fact that red nodes have black children
    data AlmostTree : Nat → Set where
      AE : AlmostTree Zero
      AT :  ∀ {n c1 c2}
              → (c : Color)
              → Tree c1 n → A → Tree c2 n
              → AlmostTree (incr-if-black c n)

    balance-break : ∀ {n} -> HTree n -> A -> HTree n -> AlmostTree n
    balance-break (HideColor l) x (HideColor r) = AT R l x r

    -- input color is implicitly black 
    balance-left : ∀ {n c} → AlmostTree n → A → Tree c n → HTree (Suc n)

    -- these are the two rotation cases
    balance-left (AT R (TR a x b) y c) z d = HideColor (TR (TB a x b) y (TB c z d))
    balance-left (AT R a x (TR b y c)) z d = HideColor (TR (TB a x b) y (TB c z d))
    -- need to expand the catch-all, because the *proof* is different in each case.  
    balance-left AE x r = HideColor (TB E x r)
    balance-left (AT B a  x b) y r = HideColor (TB (TB a x b) y r)
    balance-left (AT R E x E) y r = HideColor (TB (TR E x E) y r)
    balance-left (AT R (TB a1 x1 a2) x (TB b1 y1 b2)) y c = HideColor (TB (TR (TB a1 x1 a2) x (TB b1 y1 b2)) y c)

    -- input color is implicitly black 
    balance-right : ∀ {n c} → Tree c n → A → AlmostTree n → HTree (Suc n)
    -- these are the two rotation cases
    balance-right a x (AT R (TR b y c)  z d) = HideColor (TR (TB a x b) y (TB c z d))
    balance-right a x (AT R b y (TR c z d)) = HideColor (TR (TB a x b) y (TB c z d))
    -- catch-all 
    balance-right a x AE = HideColor (TB a x E)
    balance-right a x (AT R E y E) = HideColor (TB a x (TR E y E))
    balance-right a x (AT R (TB l y r) x' (TB l' y' r')) = 
           HideColor (TB a x (TR (TB l y r) x' (TB l' y' r')))
    balance-right a x (AT B l y r) = HideColor (TB a x (TB l y r))

    -- forget that the top node of the tree is well-formed
    forget : ∀ {n} → HTree n -> AlmostTree n
    forget (HideColor E) = AE 
    forget (HideColor (TR l x r)) = AT R l x r
    forget (HideColor (TB l x r))   = AT B l x r

    -- determine the color of the tree
    decide-root : ∀ {n c} (t : Tree c n) → Either (Tree B n) (Tree R n)
    decide-root E = Left E
    decide-root (TR a x b) = Right (TR a x b)
    decide-root (TB a x b) = Left (TB a x b)

    mutual
      ins-red : ∀ {n} (t : Tree R n) (x : A) → AlmostTree n
      ins-red (TR l y r) x with compare x y
      ... | LT = balance-break (ins-black l x) y (HideColor r)
      ... | GT = balance-break (HideColor l) y (ins-black r x)
      ... | EQ = (AT R l x r)

      ins-black : ∀ {n} (t : Tree B n) (x : A) → HTree n
      ins-black E x = HideColor (TR E x E)
      ins-black (TB l y r) x with compare x y
      ... | LT  = balance-left (ins-any l x) y r
      ... | GT  = balance-right l x (ins-any r x)
      ... | EQ  = HideColor (TB l x r)

      ins-any : ∀ {n c} (t : Tree c n) (x : A) -> AlmostTree n
      ins-any t x with decide-root t 
      ... | Left rt = forget (ins-black rt x )
      ... | Right rt = ins-red rt x

    blacken-root : ∀ {n} → HTree n → RBT
    blacken-root (HideColor E)          = Root E
    blacken-root (HideColor (TR l x r)) = Root (TB l x r)
    blacken-root (HideColor (TB l x r)) = Root (TB l x r)

    insert : RBT → A → RBT
    insert (Root t) x = blacken-root (ins-black t x)
