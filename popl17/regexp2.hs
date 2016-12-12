{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, RankNTypes,
    ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, GeneralizedNewtypeDeriving,
    TemplateHaskell, InstanceSigs #-}
{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses #-}

-- Based on:
-- Sulzmann & Lu
-- Regular Expression SubMatching Using Partial Derivatives

-- So far, inefficient version only
-- Type system keeps track of the named matches that can be
-- produced by the regexp
-- Doesn't allow marking inside of Kleene-*

import Data.Kind (Type)

import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude
import CLaSH.Promoted.Nat(SNat, snat, addSNat)
import CLaSH.Sized.Vector (Vec(..))
import qualified CLaSH.Sized.Vector as V

import Control.Applicative (Applicative(..), Alternative(..))


import qualified Tmap as T

{-
instance CanMerge ()     where
  canMerge = undefined
instance CanMerge String where
  canMerge = undefined
instance CanMerge (Maybe String) where
  canMerge = undefined
instance CanMerge [String] where
  canMerge = undefined

instance MergeClass (Maybe String) (Maybe String) where
  type Merge (Maybe String) (Maybe String) = [String]
  sMerge (Just s1) (Just s2) = ([s1,s2], M)
  sMerge (Just s1) Nothing   = ([s1], M)
  sMerge Nothing   (Just s2) = ([s2], M)
  sMerge Nothing  Nothing    = ([], M)

instance MergeClass String String where
  type Merge String String = [String]
  sMerge s1 s2 = ([s1,s2], M)
-}



-- Index is number of match expressions in the regexp
-- and the number of results that we can expect after we match against this regexp

$(singletons [d|
    data Occ = Opt | One | Many deriving (Eq, Ord)
  |])

type family Optional (a :: Type) :: Type where
  Optional String         = Maybe String
  Optional (Maybe String) = Maybe String
  Optional [String]       = [String]

type family Many (a :: Type) :: Type where
  Many String         = [String]
  Many (Maybe String) = [String]
  Many [String]       = [String]

type family Repeat (m :: [(Symbol,Type)]) :: [(Symbol, Type)] where
  Repeat '[] = '[]
  Repeat ('(s,a):m) = '(s,Many a):Repeat m
  
type family
  Merge (m1 :: [(Symbol,Type)]) (m2 :: [(Symbol,Type)]) :: [(Symbol,Type)] where
  Merge m m = m -- kind of a hack...
  Merge '[] ('(t,b):m2) = '(t,Optional b)':Merge '[] m2
  Merge ('(s,a):m1) '[] = '(s,Optional a)':Merge m1 '[]
  Merge ('(s1,a):m1) ('(s2,b):m2) = MergeHelper (CmpSymbol s1 s2) s1 s2 a b m1 m2

type family MergeHelper (o :: Ordering)
         s t (a :: Type) (b :: Type) (m1 :: [(Symbol,Type)])
                                     (m2 :: [(Symbol,Type)]) where
  MergeHelper EQ s s a b m1 m2 = '(s, [String])  ': Merge m1 m2
  MergeHelper LT s t a b m1 m2 = '(s, Optional a)': Merge m1 ('(t,b)':m2)
  MergeHelper GT s t a b m1 m2 = '(t, Optional b)': Merge ('(s,a)':m1) m2


data R (n :: [(Symbol,Type)] ) where
  Empty :: R '[]   -- Empty word
  Void  :: R '[]   -- Match nothing
  Char  :: Char -> R '[]
  Seq   :: R m1 -> R m2 -> R (T.Join m1 m2)
                                   -- no duplicates allowed
  Alt   :: R m1 -> R m2 -> R (Merge m1 m2)
  Star  :: R m -> R (Repeat m)              -- merges all of the subpatterns together
  Mark  :: forall (s :: Symbol).
    String -> R '[] -> R '[ '(s,String)]    -- no sub patterns (for now)

instance Show (R n) where
  show Empty = "ε"
  show Void  = "∅"   
  show (Char c) = [c]
  show (Seq r1 r2)   = show r1 ++ show r2
  show (Alt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Star r)    = "(" ++ show r  ++ ")*"
  show (Mark w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

-- These types can be inferred
--
--r1 :: R '[]
r1 = Alt (Char 'a') (Char 'b')

-- r2 :: R '[ '("a", String) ]
r2 = Mark @"a" "" r1

--r4 :: R '[ '("b", [String]) ]
r4 = Star (Mark "" (Seq r1 r1))

--r6 :: R '[ '("a", Maybe String), '("b", Maybe String) ]
r6 = Alt (Mark @"a" "" (Char 'a')) (Mark @"b" "" (Char 'b'))


getDom :: R m -> T.Dom m
getDom Empty = T.DNil
getDom Void  = T.DNil
getDom (Char c) = T.DNil
getDom (Seq r1 r2) = T.sJoin (getDom r1) (getDom r2)

{-
-- Count the number of results from a regexp
count :: R n -> SNat n
count Empty  = snat @0
count Void   = snat @0
count (Seq r1 r2)  = (count r1) `addSNat` (count r2)
count (Merge r1 r2)  = count r1 
count (Alt r1 r2)    = count r1 
count (Star r)    = count r
count (Mark w r)  = snat @1
-}

-- The main idea is that we will run the regexp against the input
-- word to produce a new regexp.
-- This new regexp will contain the strings that
-- matched at each marked point. If the new regexp is nullable, then
-- the match succeeds.
match :: R m -> String -> Maybe [T.Dict m]
match r w = extract (deriveWord r w)

deriveWord :: R n -> String -> R n
deriveWord r []    = r
deriveWord r (l:w) = deriveWord (deriv r l) w 


data Exists (t :: k -> Type) where
  Witness :: t a -> Exists t

parse :: String -> Maybe (Exists R)
parse = undefined

{-
class IsString a where
  fromString :: String -> a

class IsStaticString (a :: k -> Type) where
  type f a :: Symbol -> k
  fromString :: pi (s :: Symbol). a (f a s)

x = [regexp|"ksjhsdkfhdskhf"|]
-}

-- A result from a match expression 
-- newtype Result s = Result [s] deriving
--    (Eq, Show, Alternative, Applicative, Functor)


-- Extract all possible strings stored in the regexp
-- if the match succeeds
-- (note: the match succeeds iff it is nullable)
-- Due to |, there could be multiple results
-- Due to * each matching location could produce multiple results
extract :: R m -> Maybe [T.Dict m]
extract Empty       = return [T.Nil]
extract Void        = return [T.Nil]
extract (Char c)    = return [T.Nil]
extract (Seq r1 r2) = do
  s1 <- extract r1
  s2 <- extract r2
  let d1 = undefined
  let d2 = undefined
  let x = [ fmap snd (T.sJoin d1 d2 v1 v2) | v1 <- s1, v2 <- s2]
  undefined
extract (Alt r1 r2) = undefined
extract (Star r)    = undefined
extract (Mark s r)  = if nullable r then 
  return [T.Cons s T.Nil] else Nothing

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Empty         = True
nullable (Char c)      = False
nullable (Alt re1 re2) = nullable re1 || nullable re2
nullable (Seq re1 re2) = nullable re1 || nullable re2
nullable (Star re)     = True
nullable Void          = False
nullable (Mark _ r)    = nullable r


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: R n -> R n
markEmpty (Mark w r)  | nullable r = (Mark w Empty)
markEmpty (Mark w r)  = Mark w Void
markEmpty (Alt r1 r2) = Alt  (markEmpty r1) (markEmpty r2)
markEmpty (Seq r1 r2) = Seq  (markEmpty r1) (markEmpty r2)
markEmpty (Star r)    = Star (markEmpty r)
markEmpty r           = r  

deriv :: R n -> Char -> R n
deriv (Char s)    c = if s == c then Empty else Void
deriv Empty       c = Void
deriv (Seq r1 r2) c | nullable r1 = 
     Alt (Seq (deriv r1 c) r2) (Seq (markEmpty r1) (deriv r2 c))
deriv (Seq r1 r2) c = Seq (deriv r1 c) r2
deriv (Alt r1 r2) c = Alt (deriv r1 c) (deriv r2 c)
deriv Void        c = Void
deriv (Mark w r)  c = Mark (w ++ [c]) (deriv r c)

{-
-----------------------------------------------------------
-----------------------------------------------------------
-- Standard Vector stuff
{-
data Vec (n :: Nat) (a :: Type) where
  Nil  :: Vec 0 a
  Cons :: a -> Vec n a -> Vec (1 + n) a
  
vappend :: forall n m a . Vec n a -> Vec m a -> Vec (n + m) a
vappend Nil         vs = vs
vappend (Cons a (vs :: Vec n1 a)) us = axiom @n1 @m (Cons a (vappend vs us))
-}


{-
vrepeat :: Sing n -> a -> Vec n a
vrepeat n a = if natVal n == 0 then unsafeCoerce Nil
              else unsafeCoerce (Cons a (vrepeat (sPred n) a))

vmerge :: Monoid a => Vec n a -> Vec n a -> Vec n a
vmerge Nil Nil = Nil
vmerge (Cons a1 v1) (Cons a2 v2) = undefined -- Cons (mappend a1 a2) (vmerge v1 v2)

instance (KnownNat n, Monoid a) => Monoid (Vec n a) where
  mempty  = undefined -- vrepeat mempty
  mappend = vmerge
-}
{-
toList :: Vec n a -> [a]
toList Nil = []
toList (Cons a vs) = a : toList vs

instance Show a => Show (Vec n a) where
  show vs = show (toList vs)
-}


{-
-- Interpreting a regular expression as a type
-- The contents of this type will be inhabited if the regular expression
-- matches anything
type family Interpret (r :: R) :: Type where
  Interpret Empty       = Void
  Interpret (Exact n)   = Sing n
  Interpret (Sequ r1 r2) = (Interpret r1, Interpret r2)
  Interpret (Alt r1 r2) = Either (Interpret r1) (Interpret r2)
  Interpret (Star r)    = [ Interpret r ]

{-
class Flat a where
  flat :: a -> [ Nat ]

instance Flat Void where
  flat x = []
instance Flat (Sing n) where
  flat n = [toNat n]
instance (Flat a, Flat b) => Flat (a,b) where
  flat (x,y) = flat x ++ flat y
instance (Flat a, Flat b) => Flat (Either a b) where
  flat (Left x) = flat x
  flat (Right x) = flat x
instance (Flat a) => Flat [a] where
  flat xs = concatMap flat xs 
-}

type family Flat k (r :: k) :: [Nat] where
  Flat Nat n                  = '[n]
  Flat (a,b) '(x,y)           = Flat a x :++ Flat b y
  Flat (Either a b) (Left x)  = Flat a x
  Flat (Either a b) (Right x) = Flat b x
  Flat [ k ] xs               = ConcatMap (Flat k) xs




-- a vector containing exactly the sequence of values described by r
data Lang (r :: R) where
  Nil    :: Lang Empty


type family Nullable (r :: R) :: Bool where
  Nullable Empty     = True
  Nullable (Exact a) = False
--  Nullable (Seq r1 r2) = Nullable r1 || Nullable r2
--  Nullable (Alt r1 r2) = Nullable r1 && Nullable r2
-}
-}
