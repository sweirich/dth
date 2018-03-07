{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs,
    ScopedTypeVariables, InstanceSigs, TypeApplications,
    TypeFamilyDependencies,
    TemplateHaskell, AllowAmbiguousTypes,
    FlexibleContexts, TypeSynonymInstances, FlexibleInstances,
    MultiParamTypeClasses, FunctionalDependencies #-}


{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fprint-expanded-synonyms #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

-- | This module defines a dictionary indexed by a "symbol occurrence map"
-- This structure statically tracks the set of keys (symbols) as well as
-- three possible value types for each key: a single string,
-- an optional string, or a list of strings.
module OccDict(
  Occ(..), OccType(..), Dict(..), Entry(..), Wf(..), OccMap,
  Symbol, showSym,
  Empty,One,Merge(..),Alt(..),Repeat(..),
  nils,combine,glueLeft,glueRight,
  module GHC.Records,
  getValues) where

import Data.Kind(Type)
import GHC.Records
import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.TypeLits (Sing(..),
       Symbol(..),KnownSymbol(..),symbolVal)

-------------------------------------------------------------------------
-- Symbol Maps

-- | Occurrences: once, at most once, or any number of times
$(singletons [d|
  data Occ = Once | Opt | Many deriving (Eq, Ord, Show)
  |])
-- We use the 'singletons' library to automatically give us
-- a Singleton type for Occ, plus definitions for Eq, Ord, Show.


-- | The static description of a dictionary: a mapping of
-- symbols to their occurrence information.
type OccMap = [(Symbol,Occ)]

-- We could use the singletons library as so to lift definitions to the type
-- level. However, haddock doesn't support comments in TH. So we don't.
{-
$(singletons [d|

  empty :: OccMap
  empty = []

  one :: Symbol -> OccMap
  one s = [(s,Once)]

  merge :: OccMap -> OccMap -> OccMap
  merge m  [] = m
  merge [] m  = m
  merge (e1@(s1,o1):t1) (e2@(s2,o2):t2) =
    if s1 == s2 then (s1,Many) : merge t1 t2
    else if s1 <= s2 then e1 : merge t1 (e2:t2)
      else e2 : merge (e1:t1) t2

  alt :: OccMap -> OccMap -> OccMap
  alt [] [] = []
  alt ((n1,o1):t1) [] = (n1, max Opt o1): alt t1 []
  alt [] ((n2,o2):t2) = (n2, max Opt o2): alt [] t2
  alt ((n1,o1):t1)((n2,o2):t2) =
      if n1 == n2 then (n1, max o1 o2) : alt t1 t2
      else if n1 <= n2 then (n1, max Opt o1) : alt t1 ((n2,o2):t2)
           else (n2, max Opt o2) : alt ((n1,o1):t1) t2

  repeat :: OccMap -> OccMap
  repeat [] = []
  repeat ((n,o):t) = ((n, Many):repeat t)

  |])
-}


-- Equivalent to 'singletons' above.

-- | Symbol map with no entries
type Empty = '[]

-- | Singleton map, with single occurrence
type One s = '[ '(s,Once) ]

-- | Combine two sorted maps, noting when symbols appear
-- on both sides that we could have many occurrences
type family Merge (a :: OccMap) (b :: OccMap) :: OccMap where
   Merge s  '[] = s
   Merge '[] s  = s
   Merge ('(n1,o1):t1) ('(n2,o2):t2) =
     If (n1 :== n2) ('(n1, 'Many) : Merge t1 t2)
        (If (n1 :<= n2) ('(n1, o1) : Merge t1 ('(n2,o2):t2))
                        ('(n2, o2) : Merge ('(n1,o1):t1) t2))

-- | Combine two (sorted) symbol maps
-- Convert any occurrences that only appear on one side to 'Opt'
-- otherwise, take the max
type family Alt (a :: OccMap) (b :: OccMap) :: OccMap where
   Alt '[] '[] = '[]
   Alt ( '(n1,o1) : t1)  '[] = '(n1, Max Opt o1) : Alt t1 '[]
   Alt '[] ( '(n2,o2) : t2)  = '(n2, Max Opt o2) : Alt '[] t2
   Alt ('(n1,o1):t1) ('(n2,o2):t2) =
     If (n1 :== n2) ('(n1, Max o1 o2) : Alt t1 t2)
        (If (n1 :<= n2) ('(n1, Max Opt o1) : Alt t1 ('(n2,o2):t2))
                        ('(n2, Max Opt o2) : Alt ('(n1,o1):t1) t2))

-- | Convert all occurrences to 'Many'
type family Repeat (a :: OccMap) :: OccMap where
   Repeat '[] = '[]
   Repeat ( '(n,o) : t) = '(n, Many) : Repeat t



-------------------------------------------------------------------------

-- | A data structure indexed by a type-level map
data Dict :: OccMap -> Type where
   Nil  :: Dict '[]
   (:>) :: Entry s o -> Dict tl -> Dict ('(s,o) : tl)

infixr 5 :>

-- Note that the entries don't actually store the
-- keys (as we already know them from the type).
-- We only store the values, and the types of the values
-- are determined by the type family below.
-- | An entry in the dictionary
data Entry :: Symbol -> Occ -> Type where
   E :: forall s o. OccType o -> Entry s o

-- OccType is an *injective* type family. From the output we
-- can determine the input during type inference.
-- | A mapping from occurrence to the type of value stored in the dictionary
type family OccType (o :: Occ) = (res :: Type) | res -> o where
  OccType Once = String
  OccType Opt  = Maybe String
  OccType Many = [String]

-- type inferred to be (uses injectivity above for OccType)
-- example_dict :: Dict '['("b", 'Once), '("d", 'Many), '("e", 'Opt)]
example_dict = E @"b" "Regexp" :>
               E @"d" ["dth", "strl17"] :>
               E @"e" (Just "hs") :> Nil

-------------------------------------------------------------------------
-- Accessor function for dictionaries (get)

type family ShowOccMap (m :: OccMap) :: ErrorMessage where
  ShowOccMap '[]         = Text ""
  ShowOccMap '[ '(a,o) ] = Text a
  ShowOccMap ('(a,o): m) = Text a :<>: Text ", " :<>: ShowOccMap m

-- A proof that a particular name appears in the domain
data Index (n :: Symbol)  (o :: Occ) (s :: OccMap) where
  DH :: Index n o ('(n,o):s)
  DT :: Index n o s -> Index n o (t:s)

-- Find a name n in s, if it exists (and return a proof!),
-- or produce a TypeError
-- NOTE: We need TypeInType to return a GADT from a type family
type Find n s = (FindH n s s :: Index n o s)

-- The second argument is the original association list
-- Provided so that we can create a more informative error message
type family FindH (n :: Symbol) (s :: OccMap) (s2 :: OccMap) :: Index n o s where
  FindH n ('(n,o): s) s2 = DH
  FindH n ('(t,p): s) s2 = DT (FindH n s s2)
  FindH n '[]         s2 =
     TypeError (Text "Hey Comcast!  I couldn't find a capture group named '" :<>:
                Text n :<>: Text "' in" :$$:
                Text "    {" :<>: ShowOccMap s2 :<>: Text "}")

-- Look up an entry in the dictionary, given an index for a name
-- The functional dependency guides type inference
class Get (p :: Index n o s) | n s -> o where
  getp :: Dict s -> OccType o

-- The entry we want is here!
instance Get DH where
  getp (E v :> _ ) = v

-- Need to keep looking
instance (Get l) => Get (DT l) where
  getp ( _ :> xs) = getp @_ @_ @_ @l xs

-- Instance for the Dictionary: if we can find the name
-- without producing a type error, then type class
-- resolution for Get will generate the correct accessor
-- function at compile time

instance (Get (Find n s :: Index n o s),
         t ~ OccType o) => HasField n (Dict s) t where
  getField = getp @_ @_ @_ @(Find n s)


{-
class GetField (x :: Symbol) r a | x r -> a where
  gets :: Dict r -> a

instance GetField x xs a => HasField x (Dict xs) a where
  getField = gets

instance {-# OVERLAPPING #-} (t ~ OccType o) => GetField n ('(n,o):s) t where
  gets (E v :> _) = v

instance {-# OVERLAPPING #-} (GetField n s t) => GetField n ('(m,o):s) t where
  gets (_ :> xs) = gets @n xs

instance TypeError (Text "Cannot find name ") => GetField n '[] t where
  gets = error "unreachable"
-}


-- | Alternate interface that turns everything into a [String]
getValues :: forall n s o.
  (Get (Find n s :: Index n o s), SingI o) => Maybe (Dict s) -> [String]
getValues (Just x) = gg (sing :: Sing o) (getp @_ @_ @_ @(Find n s) x) where
     gg :: Sing o -> OccType o -> [String]
     gg SOnce s       = [s]
     gg SOpt (Just s) = [s]
     gg SOpt Nothing  = []
     gg SMany s       = s
getValues Nothing = []

-------------------------------------------------------------------------
-- Show instance for Dict

--instance Show (Sing (n :: Symbol)) where
--  show ps@SSym = symbolVal ps

instance (SingI n, SingI o) => Show (Entry n o) where
  show = showEntry sing sing where


instance SingI s => Show (Dict s) where
  show xs = "{ " ++ showDict sing xs where
    showDict :: Sing xs -> Dict xs -> String
    showDict SNil Nil = "}"
    showDict (SCons (STuple2 sn so) pp) (e :> Nil) = showEntry sn so e ++ " }"
    showDict (SCons (STuple2 sn so) pp) (e :> xs)  = showEntry sn so e ++ ", " ++ showDict pp xs

-- | Convert a runtime symbol to corresponding String
showSym :: forall (n::Symbol). Sing n -> String
showSym ps@SSym = symbolVal ps

showEntry :: forall n o. Sing n -> Sing o -> Entry n o -> String
showEntry sn so (E ss) = showSym sn ++ "=" ++ showData so ss

-- pattern matching selects the instance that we need
showData :: Sing o -> OccType o -> String
showData SOnce = show
showData SOpt  = show
showData SMany = show

-- Show a singleton Symbol Occurrence Map
instance Show (Sing (s :: OccMap)) where
  show r = "[" ++ show' r where
    show' :: Sing (ss :: OccMap) -> String
    show' SNil = "]"
    show' (SCons (STuple2 sn so) ss) = showSym sn ++ "," ++ show' ss


------------------------------------------------------
-- Operations on dictionaries (mostly used in extract, see below)

-- | Merge two dictionaries together, preserving the sorting of the
-- entries
combine :: Sing s1 -> Sing s2 -> Dict s1 -> Dict s2 -> Dict (Merge s1 s2)
combine SNil SNil Nil Nil = Nil
combine SNil _ Nil b = b
combine _ SNil b Nil = b
combine s1@(SCons (STuple2 ps so1) r1)  s2@(SCons (STuple2 pt so2) r2)
        (e1@(E ss) :> t1)              (e2@(E ts) :> t2) =
  case ps %:== pt of
   STrue  -> E (toMany so1 ss ++ toMany so2 ts) :> combine r1 r2 t1 t2
     where
       -- note that 'OccType Many' is [String]
       toMany :: Sing o -> OccType o -> OccType Many
       toMany SOnce  s       = [s]
       toMany SOpt  (Just s) = [s]
       toMany SOpt  Nothing  = []
       toMany SMany ss       = ss

   SFalse -> case ps %:<= pt of
     STrue  -> e1 :> combine r1 s2 t1 (e2 :> t2)
     SFalse -> e2 :> combine s1 r2 (e1 :> t1) t2


-- default value for optional types
defOcc :: Sing o -> OccType (Max Opt o)
defOcc SOnce = Nothing
defOcc SOpt  = Nothing
defOcc SMany = []

-- This was a not so bad to define.  I made it an id function for every case,
-- then used the four type errors to figure out which lines to change.
-- Agda-like splitting would have helped, though.
glueOccLeft :: Sing o1 -> Sing o2 -> OccType o2 -> OccType (Max o1 o2)
glueOccLeft SOnce SOnce m = m
glueOccLeft SOnce SOpt  m = m
glueOccLeft SOnce SMany m = m
glueOccLeft SOpt SOnce  m = Just m
glueOccLeft SOpt SOpt   m = m
glueOccLeft SOpt SMany  m = m
glueOccLeft SMany SOnce m = [m]
glueOccLeft SMany SOpt  (Just m) = [m]
glueOccLeft SMany SOpt  Nothing  = []
glueOccLeft SMany SMany m = m

-- We don't have a communitivity property for Max. If we did
-- we wouldn't have to define both Left and Right versions of
-- this function.
glueOccRight :: Sing o1 -> OccType o1 -> Sing o2 -> OccType (Max o1 o2)
glueOccRight SOnce m SOnce = m
glueOccRight SOnce m SOpt  = Just m
glueOccRight SOnce m SMany = [m]
glueOccRight SOpt m SOnce  = m
glueOccRight SOpt m SOpt   = m
glueOccRight SOpt (Just m) SMany = [m]
glueOccRight SOpt Nothing  SMany = []
glueOccRight SMany m SOnce = m
glueOccRight SMany m SOpt  = m
glueOccRight SMany m SMany = m

-- | Weaken a dictionary by converting all occurrences 'o' to 'Max Opt o'
glueLeft :: Sing s1 -> Sing s2 -> Dict s2 -> Dict (Alt s1 s2)
glueLeft SNil SNil Nil = Nil
glueLeft SNil (s2@(SCons (STuple2 pt so2) st2))(e2@(E ts) :> t2) =
  E tocc :> glueLeft SNil st2 t2 where
    tocc = glueOccLeft SOpt so2 ts
glueLeft (SCons (STuple2 ps so) t) SNil Nil =
  E (defOcc so) :> glueLeft t SNil Nil
glueLeft (SCons e1@(STuple2 ps so1)  t1)
         (s2@(SCons (STuple2 pt so2) st2))(e2@(E ts) :> t2) =
  case ps %:== pt of
   STrue -> E tocc :> glueLeft t1 st2 t2 where
              tocc = glueOccLeft so1 so2 ts
   SFalse -> case ps %:<= pt of
     STrue  -> E tocc :> glueLeft t1 s2 (e2 :> t2) where
                 tocc = defOcc so1
     SFalse -> E tocc :> glueLeft (SCons e1 t1) st2 t2 where
                 tocc = glueOccLeft SOpt so2 ts

-- | Weaken a dictionary by converting all occurrences 'o' to 'Max Opt o'
glueRight :: Sing s1 -> Dict s1 -> Sing s2 -> Dict (Alt s1 s2)
glueRight SNil Nil SNil = Nil
glueRight (SCons (STuple2 pt so2) st2) (e2@(E ts) :> t2) SNil =
  E tocc :> glueRight st2 t2 SNil where
    tocc = glueOccLeft SOpt so2 ts
glueRight SNil Nil (SCons (STuple2 ps so) t) =
  E  (defOcc so) :> glueRight SNil Nil t
glueRight s1@(SCons (STuple2 ps so1) st1) (e1@(E ss) :> t1)
          (SCons e2@(STuple2 pt so2) t2) =
  case ps %:== pt of
    STrue  -> E tocc :> glueRight st1 t1 t2 where
                tocc = glueOccRight so1 ss so2
    SFalse -> case ps %:<= pt of
      STrue  -> E tocc :> glueRight st1 t1 (SCons e2 t2) where
                  tocc = glueOccLeft SOpt so1 ss
      SFalse -> E tocc :> glueRight s1 (e1 :> t1) t2 where
                  tocc = defOcc so2


-- | A "default" Dict
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
-- Must use explicit type application when called because this function
-- has an ambiguous type.
nils :: forall s. SingI s => Dict (Repeat s)
nils = nils' (sing :: Sing s) where
    nils' :: Sing ss -> Dict (Repeat ss)
    nils' SNil                    = Nil
    nils' (SCons (STuple2 _ _) r) = E [] :> nils' r


----------------------------------------------------------------
-- Properties of "well-formed" symbol maps

-- we need this property of 'Occ' terms during type checking
class (o ~ Max o o, SingI o) => WfOcc (o :: Occ) where
instance WfOcc Once
instance WfOcc Opt
instance WfOcc Many

-- | A constraint for "well-formed" symbol occurrence maps
-- Also includes a runtime representation of the map
class (m ~ Alt m m,
       Repeat m ~ Repeat (Repeat m),
       Merge m (Repeat m) ~ Repeat m,
       SingI m) =>
       Wf (m :: OccMap)


-- proof of all base cases
instance Wf '[]
-- proof of all inductive steps
instance (SingI n, WfOcc o, Wf s) => Wf ('(n, o) : s)


-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: OccMap where
  T = '("a", Once) : T

testWf :: Wf a => ()
testWf = ()

x1 = testWf @'[ '("a", Once), '("b", Opt), '("c", Many) ]
-- x2 = testWf @T   -- doesn't type check
