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
--import CLaSH.Promoted.Nat(SNat, snat, addSNat)
-- import CLaSH.Sized.Vector (Vec(..))
-- import qualified CLaSH.Sized.Vector as V

import Control.Applicative (Applicative(..), Alternative(..))
import Data.Maybe (catMaybes, listToMaybe)


import Data.Typeable

import Tmap (Dom(..), Dict(..), sym)
import qualified Tmap as T


-- For alternation expressions
type family Optional (a :: Type) :: Type where
  Optional String         = Maybe String
  Optional (Maybe String) = Maybe String
  Optional [String]       = [String]

none :: forall a proxy. Typeable a => Optional a
none | Just Refl <- eqT @a @String         = Nothing
     | Just Refl <- eqT @a @(Maybe String) = Nothing
     | Just Refl <- eqT @a @[String]       = []                                

some :: forall a proxy. Typeable a => a -> Optional a
some a | Just Refl <- eqT @a @String         = Just a
       | Just Refl <- eqT @a @(Maybe String) = a
       | Just Refl <- eqT @a @[String]       = a             




type family Many (a :: Type) :: Type where
  Many String         = [String]
  Many (Maybe String) = [String]
  Many [String]       = [String]



type family Repeat (m :: [(Symbol,Type)]) :: [(Symbol, Type)] where
  Repeat '[] = '[]
  Repeat ('(s,a):m) = '(s,Many a):Repeat m

sRepeatDom :: Dom m -> Dom (Repeat m)
sRepeatDom DNil = DNil
sRepeatDom (DCons ps pa d) = DCons ps Proxy (sRepeatDom d)

sRepeat :: Dom m -> Dict m -> Dict (Repeat m)
sRepeat DNil T.Nil = T.Nil
sRepeat (DCons ps pt d) (Cons a m) = undefined
                             
type family
  Merge (m1 :: [(Symbol,Type)]) (m2 :: [(Symbol,Type)]) :: [(Symbol,Type)] where
  Merge '[] '[] = '[] -- also Merge m m = m
  Merge '[] ('(t,b):m2) = '(t,Optional b)':Merge '[] m2
  Merge ('(s,a):m1) '[] = '(s,Optional a)':Merge m1 '[]
  Merge ('(s1,a):m1) ('(s2,b):m2) = MergeHelper (CmpSymbol s1 s2) s1 s2 a b m1 m2

type family MergeHelper (o :: Ordering)
         s t (a :: Type) (b :: Type) (m1 :: [(Symbol,Type)])
                                     (m2 :: [(Symbol,Type)]) where
  MergeHelper EQ s s a b m1 m2 = '(s, [String])  ': Merge m1 m2
  MergeHelper LT s t a b m1 m2 = '(s, Optional a)': Merge m1 ('(t,b)':m2)
  MergeHelper GT s t a b m1 m2 = '(t, Optional b)': Merge ('(s,a)':m1) m2

axiom :: Merge m m :~: m
axiom = undefined


sMergeDom :: T.Dom m1 -> T.Dom m2 -> T.Dom (Merge m1 m2)
sMergeDom DNil DNil = DNil
sMergeDom DNil (DCons pt pb m2) = DCons pt Proxy (sMergeDom DNil m2)
sMergeDom (DCons ps pa m1) DNil = DCons ps Proxy (sMergeDom m1   DNil)
sMergeDom (DCons (ps :: p1 s) pa m1) (DCons (pt :: p2 t) pb m2) = case (sym @s %~ sym @t) of
  Proved Refl -> DCons ps Proxy (sMergeDom m1 m2)
  Disproved _ -> case (sCompare (sym @s) (sym @t)) of
    SLT -> DCons ps Proxy (sMergeDom m1 (DCons pt pb m2))
    SGT -> DCons pt Proxy (sMergeDom (DCons ps pa m1) m2)

sMerge1 :: Dom m1 -> Dom m2 -> Dict m1 -> Dict (Merge m1 m2)
sMerge1 DNil DNil Nil                      = Nil
sMerge1 DNil (DCons pt (pb :: p b) m2) Nil = undefined

data R (n :: [(Symbol,Type)] ) where
  Empty :: R '[]   -- Empty word
  Void  :: R '[]   -- Match nothing
  Char  :: Char -> R '[]
  Seq   :: R m1 -> R m2 -> R (T.Join m1 m2)
                                   -- no duplicates allowed
  Alt   :: R m1 -> R m2 -> R (Merge m1 m2)
  Star  :: R m -> R (Repeat m)              -- merges all of the subpatterns together
  Mark  :: KnownSymbol s => proxy s -> String -> R '[] -> R '[ '(s,String)]    -- no sub patterns (for now)

instance Show (R n) where
  show Empty = "ε"
  show Void  = "∅"   
  show (Char c) = [c]
  show (Seq r1 r2)   = show r1 ++ show r2
  show (Alt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Star r)    = "(" ++ show r  ++ ")*"
  show (Mark (ps :: p s) w r)  = "/" ++ w ++ "(" ++ show r ++ ")"

-- These types can be inferred
--
--r1 :: R '[]
r1 = Alt (Char 'a') (Char 'b')

-- r2 :: R '[ '("a", String) ]
r2 = Mark (sym @"a") "" r1

--r4 :: R '[ '("b", [String]) ]
r4 = Star (Mark (sym @"b") "" (Seq r1 r1))

--r6 :: R '[ '("a", Maybe String), '("b", Maybe String) ]
r6 = Alt (Mark (sym @"a") "" (Char 'a')) (Mark (sym @"b") "" (Char 'b'))

-- Get the domain of the map (if it is defined)
getDom :: R m -> Maybe (T.Dom m)
getDom Empty       = return $ T.DNil
getDom Void        = return $ T.DNil
getDom (Char c)    = return $ T.DNil
getDom (Seq r1 r2) = do
  d1 <- getDom r1
  d2 <- getDom r2
  T.sJoinDom d1 d2
getDom (Alt r1 r2) = do
  d1 <- getDom r1
  d2 <- getDom r2
  return $ sMergeDom d1 d2
getDom (Star r) = do
  d <- getDom r
  return $ sRepeatDom d
getDom (Mark ps _ _) = return $ DCons ps Proxy DNil

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
  d1 <- getDom r1
  d2 <- getDom r2
  let
    x = catMaybes [ T.sJoin d1 d2 v1 v2 | v1 <- s1, v2 <- s2]
  case x of
     [] -> Nothing
     _  -> return (map snd x)
extract (Alt r1 r2) = case (extract r1, extract r2) of
  (Just s1, Just s2) -> undefined -- Just (s1 ++ s2)
  (Just s1, Nothing) -> undefined -- Just s1
  (Nothing, Just s2) -> undefined -- Just s2
  (Nothing, Nothing) -> Nothing
  
extract (Star r)    = undefined
extract (Mark _ s r)  = if nullable r then 
  return [T.Cons s T.Nil] else Nothing

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Empty         = True
nullable (Char c)      = False
nullable (Alt re1 re2) = nullable re1 || nullable re2
nullable (Seq re1 re2) = nullable re1 || nullable re2
nullable (Star re)     = True
nullable Void          = False
nullable (Mark _ _ r)    = nullable r


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: R n -> R n
markEmpty (Mark p w r)  | nullable r = (Mark p w Empty)
markEmpty (Mark p w r)  = Mark p w Void
markEmpty (Alt r1 r2) = Alt  (markEmpty r1) (markEmpty r2)
markEmpty (Seq r1 r2) = Seq  (markEmpty r1) (markEmpty r2)
markEmpty (Star r)    = Star (markEmpty r)
markEmpty r           = r  

deriv :: forall n. R n -> Char -> R n
deriv (Char s)    c = if s == c then Empty else Void
deriv Empty       c = Void
deriv (Seq r1 r2) c | nullable r1, Refl <- axiom @n = 
     Alt (Seq (deriv r1 c) r2) (Seq (markEmpty r1) (deriv r2 c))
deriv (Seq r1 r2) c = Seq (deriv r1 c) r2
deriv (Alt r1 r2) c = Alt (deriv r1 c) (deriv r2 c)
deriv Void        c = Void
deriv (Mark p w r)  c = Mark p (w ++ [c]) (deriv r c)

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
