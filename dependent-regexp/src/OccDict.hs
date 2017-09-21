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

{-
   This file defines a dictionary that
   statically tracks the set of keys as well as
   three possible value types for each key: a single string,
   an optional string, or a list of strings.
-}

module OccDict(
  Occ(..), Dict(..), Entry(..), Wf(..), SM,
  Empty,One,Merge(..),Alt(..),Repeat(..),
  nils,combine,glueLeft,glueRight,
  module GHC.Records,
  getMatch) where

import Data.Kind(Type)
import GHC.Records
import GHC.TypeLits
import Data.Singletons.TH
import Data.Singletons.Prelude
import Data.Singletons.TypeLits (Sing(..),
       Symbol(..),KnownSymbol(..),symbolVal)

-- We use the singletons library to lift definitions to the
-- type level

$(singletons [d|
  data Occ = Once | Opt | Many deriving (Eq, Ord, Show)
  |])

-- The static description of a dictionary: a mapping of
-- symbols to their occurrence information.
type SM = [(Symbol,Occ)]

-- Operations on the symbol map.

-- Merge combines two lists, preserving the sorted order of the keys
-- Alt combines two lists, marking values that occurr in only one of the
--   two as optional
-- Repeat marks all values as repeated.

$(singletons [d|

  empty :: SM
  empty = []

  one :: Symbol -> SM
  one s = [(s,Once)]

  merge :: SM -> SM -> SM
  merge m  [] = m
  merge [] m  = m
  merge (e1@(s1,o1):t1) (e2@(s2,o2):t2) =
    if s1 == s2 then (s1,Many) : merge t1 t2
    else if s1 <= s2 then e1 : merge t1 (e2:t2)
      else e2 : merge (e1:t1) t2

  alt :: SM -> SM -> SM
  alt [] [] = []
  alt ((n1,o1):t1) [] = (n1, max Opt o1): alt t1 []
  alt [] ((n2,o2):t2) = (n2, max Opt o2): alt [] t2
  alt ((n1,o1):t1)((n2,o2):t2) =
      if n1 == n2 then (n1, max o1 o2) : alt t1 t2
      else if n1 <= n2 then (n1, max Opt o1) : alt t1 ((n2,o2):t2)
           else (n2, max Opt o2) : alt ((n1,o1):t1) t2

  repeat :: SM -> SM
  repeat [] = []
  repeat ((n,o):t) = ((n, Many):repeat t)

  |])

{-
-- this is the equivalent code that we could have written

type Empty = '[]

type One s = '[ '(s,Once) ]

type family Merge (a :: SM) (b :: SM) :: SM where
   Merge s  '[] = s
   Merge '[] s  = s
   Merge ('(n1,o1):t1) ('(n2,o2):t2) =
     If (n1 :== n2) ('(n1, 'Many) : Merge t1 t2)
        (If (n1 :<= n2) ('(n1, o1) : Merge t1 ('(n2,o2):t2))
                        ('(n2, o2) : Merge ('(n1,o1):t1) t2))

type family Alt (a :: SM) (b :: SM) :: SM where
   Alt '[] '[] = '[]
   Alt ( '(n1,o1) : t1)  '[] = '(n1, Max Opt o1) : Alt t1 '[]
   Alt '[] ( '(n2,o2) : t2)  = '(n2, Max Opt o2) : Alt '[] t2
   Alt ('(n1,o1):t1) ('(n2,o2):t2) =
     If (n1 :== n2) ('(n1, Max o1 o2) : Alt t1 t2)
        (If (n1 :<= n2) ('(n1, Max Opt o1) : Alt t1 ('(n2,o2):t2))
                        ('(n2, Max Opt o2) : Alt ('(n1,o1):t1) t2))

type family Repeat (a :: SM) :: SM where
   Repeat '[] = '[]
   Repeat ( '(n,o) : t) = '(n, Many) : Repeat t
-}


-------------------------------------------------------------------------

-- A data structure indexed by a type-level map
-- Keeps the entries in sorted order by key
data Dict :: SM -> Type where
   Nil  :: Dict '[]
   (:>) :: Entry a -> Dict tl -> Dict (a : tl)

infixr 5 :>

-- Note that the entries don't actually store the
-- keys (as we already know them from the type).
-- We only store the values, and the types of the values
-- are determined by the type family below.
data Entry :: (Symbol,Occ) -> Type where
   E :: forall s o. OccType o -> Entry '(s,o)

-- OccType is an *injective* type family. From the output we
-- can determine the input during type inference.
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

type family ShowSM (m :: SM) :: ErrorMessage where
  ShowSM '[]         = Text ""
  ShowSM '[ '(a,o) ] = Text a
  ShowSM ('(a,o): m) = Text a :<>: Text ", " :<>: ShowSM m

-- A proof that a particular name appears in the domain
data Index (n :: Symbol)  (o :: Occ) (s :: SM) where
  DH :: Index n o ('(n,o):s)
  DT :: Index n o s -> Index n o (t:s)

-- Find a name n in s, if it exists (and return a proof!),
-- or produce a TypeError
-- NOTE: We need TypeInType to return a GADT from a type family
type Find n s = (FindH n s s :: Index n o s)

-- The second argument is the original association list
-- Provided so that we can create a more informative error message
type family FindH (n :: Symbol) (s :: SM) (s2 :: SM) :: Index n o s where
  FindH n ('(n,o): s) s2 = DH
  FindH n ('(t,p): s) s2 = DT (FindH n s s2)
  FindH n '[]         s2 =
     TypeError (Text "Hey StrangeLoop17!  I couldn't find a group named '" :<>:
                Text n :<>: Text "' in" :$$:
                Text "    {" :<>: ShowSM s2 :<>: Text "}")

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


-- Generic interface to flexible records
-- This class is now defined in GHC.Record to support overloaded field names
--class HasField (x :: k) r a | x r -> a where
--  getField    :: r -> a

-- Instance for the Maybe in the result type
instance (HasField n u t) => HasField n (Maybe u) (Maybe t) where
  getField (Just x) = Just (getField @n x)
  getField Nothing  = Nothing

-- Instance for the Dictionary: if we can find the name
-- without producing a type error, then type class
-- resolution for Get will generate the correct accessor
-- function at compile time
instance (Get (Find n s :: Index n o s),
         t ~ OccType o) => HasField n (Dict s) t where
  getField = getp @_ @_ @_ @(Find n s)

-- Alternate interface that turns everything into a [String]
getMatch :: forall n s o.
  (Get (Find n s :: Index n o s), SingI o) => Dict s -> [String]
getMatch x = gg (sing :: Sing o) (getp @_ @_ @_ @(Find n s) x) where
     gg :: Sing o -> OccType o -> [String]
     gg SOnce s       = [s]
     gg SOpt (Just s) = [s]
     gg SOpt Nothing  = []
     gg SMany s       = s

-------------------------------------------------------------------------
-- Show instance for Dict

--instance Show (Sing (n :: Symbol)) where
--  show ps@SSym = symbolVal ps

instance (SingI n, SingI o) => Show (Entry '(n,o)) where
  show = showEntry sing sing where


instance SingI s => Show (Dict s) where
  show xs = "{" ++ showDict sing xs where
    showDict :: Sing xs -> Dict xs -> String
    showDict SNil Nil = "}"
    showDict (SCons (STuple2 sn so) pp) (e :> Nil) = showEntry sn so e ++ "}"
    showDict (SCons (STuple2 sn so) pp) (e :> xs)  = showEntry sn so e ++ "," ++ showDict pp xs

showEntry :: forall n o. Sing n -> Sing o -> Entry '(n,o) -> String
showEntry sn so (E ss) = ssym sn ++ "=" ++ showData so ss where

    ssym :: Sing n -> String
    ssym ps@SSym = symbolVal ps

    showData :: Sing o -> OccType o -> String
    showData SOnce ss = show ss
    showData SOpt  ss = show ss
    showData SMany ss = show ss

------------------------------------------------------
-- Operations on dictionaries (mostly used in extract, see below)

-- Merge two dictionaries together, preserving the sorting of the
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

-- weaken a value to its maximum
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

-- Weaken a dictionary by converting all of its entries
-- to 'Max Opt o' versions.
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


-- A "default" Dict
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

-- Well-founded sets are exactly those constructed only
-- from a finite number of [] and :
-- Well-founded sets *also* have the following properies
class (m ~ Alt m m,
       Repeat m ~ Repeat (Repeat m),
       Merge m (Repeat m) ~ Repeat m,
       -- they also have runtime representations
       SingI m) =>
       Wf (m :: SM)


-- proof of all base cases
instance Wf '[]
-- proof of all inductive steps
instance (SingI n, WfOcc o, Wf s) => Wf ('(n, o) : s)


-- this constraint rules out "infinite" sets of the form
-- (which has a coinductive proof of the merge property?)
type family T :: SM where
  T = '("a", Once) : T

testWf :: Wf a => ()
testWf = ()

x1 = testWf @'[ '("a", Once), '("b", Opt), '("c", Many) ]
-- x2 = testWf @T   -- doesn't type check
