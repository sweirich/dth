{-# LANGUAGE TypeOperators, DataKinds, KindSignatures, TypeFamilies,
    PolyKinds, TypeInType, UndecidableInstances, GADTs, 
    ScopedTypeVariables, InstanceSigs, TypeApplications,
    TypeFamilyDependencies, 
    TemplateHaskell, AllowAmbiguousTypes #-}

{-# LANGUAGE FlexibleContexts, TypeSynonymInstances, FlexibleInstances, 
    MultiParamTypeClasses, FunctionalDependencies #-}

{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fprint-expanded-synonyms #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module RegexpDependent where

import Data.Kind(Type)
import Data.Type.Equality(TestEquality(..),(:~:)(..))

import GHC.TypeLits       
import Data.Singletons.TH   
import Data.Singletons.Prelude
import Data.Singletons.TypeLits (Sing(..),
       Symbol(..),KnownSymbol(..),symbolVal)

import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Char as Char

import Data.List(foldl')


-------------------------------------------------------------------------
type Π n = Sing n
-------------------------------------------------------------------------
        
$(singletons [d|
  -- Note: deriving Ord automatically defines "max", used in alt below
  -- that's super cool!
  data Occ = Once | Opt | Many deriving (Eq, Ord, Show)
  |])

type SM = [(Symbol,Occ)]

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
     
{-     
-- Could have also used the Singletons library to use term level notation
-- to define these operations. 

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
-}
        
-------------------------------------------------------------------------

type Result (s :: SM) = Maybe (Dict s)

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

-- type inferred to be (using injectivity above for OccType)
-- example_dict :: Dict '['("b", 'Once), '("d", 'Many), '("e", 'Opt)]
example_dict = E @"b" "Regexp" :>
               E @"d" ["dth", "popl17"] :>
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
-- or produce TypeError
-- We need TypeInType to return a GADT from a type family
type family Find (n :: Symbol) (s :: SM) :: Index n o s where
  Find n s = FindH n s s

-- The second argument is the original association list
-- Provided so that we can create a more informative error message
type family FindH (n :: Symbol) (s :: SM) (s2 :: SM) :: Index n o s where
  FindH n ('(n,o): s) s2 = DH
  FindH n ('(t,p): s) s2 = DT (FindH n s s2)
  FindH n '[]         s2 =
     TypeError (Text "Hey POPL17!  I couldn't find a group named '" :<>:
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
-- This class will eventually be defined in Data.Record
-- to support overloaded field names
-- (though it will be called HasField and getField)
class Has (x :: k) r a | x r -> a where
  get    :: r -> a
  
-- Instance for the Maybe in the result type
instance (Has n u t) => Has n (Maybe u) (Maybe t) where
  get (Just x) = Just (get @n x)
  get Nothing  = Nothing

-- Instance for the Dictionary: if we can find the name
-- without producing a type error, then type class
-- resolution for Get will generate the correct accessor
-- function at compile time
instance (Get (Find n s :: Index n o s),
         t ~ OccType o) => Has n (Dict s) t where
  get = getp @_ @_ @_ @(Find n s)

-- Alternate interface that turns everything into a [String]
getField :: forall n s o. (Get (Find n s :: Index n o s), SingI o) => Result s -> [String]
getField (Just x) = gg (sing :: Π o) (getp @_ @_ @_ @(Find n s) x) where
     gg :: Π o -> OccType o -> [String]
     gg SOnce s       = [s]
     gg SOpt (Just s) = [s]
     gg SOpt Nothing  = []
     gg SMany s       = s
getField Nothing  = [] 
             
-------------------------------------------------------------------------
-- Show instance for Dict

instance Show (Sing (n :: Symbol)) where
  show ps@SSym = symbolVal ps

instance (SingI n, SingI o) => Show (Entry '(n,o)) where
  show = showEntry sing sing

instance SingI s => Show (Dict s) where
  show xs = "{" ++ showDict sing xs where
    showDict :: Π xs -> Dict xs -> String
    showDict SNil Nil = "}"
    showDict (SCons (STuple2 sn so) pp) (e :> Nil) = showEntry sn so e ++ "}"
    showDict (SCons (STuple2 sn so) pp) (e :> xs)  = showEntry sn so e ++ "," ++ showDict pp xs

showEntry :: Π n -> Π o -> Entry '(n,o) -> String
showEntry sn so (E ss) = show sn ++ "=" ++ showData so ss where
    showData :: Π o -> OccType o -> String
    showData SOnce ss = show ss
    showData SOpt  ss = show ss
    showData SMany ss = show ss
          
------------------------------------------------------  
-- Operations on dictionaries (mostly used in extract, see below)


combine :: Π s1 -> Π s2 -> Dict s1 -> Dict s2 -> Dict (Merge s1 s2)
combine SNil SNil Nil Nil = Nil
combine SNil _ Nil b = b
combine _ SNil b Nil = b
combine s1@(SCons (STuple2 ps so1) r1)  s2@(SCons (STuple2 pt so2) r2)
        (e1@(E ss) :> t1)          (e2@(E ts) :> t2) =
  case ps %:== pt of
   STrue  -> E (toMany so1 ss ++ toMany so2 ts) :> combine r1 r2 t1 t2
     where
       -- note that 'OccType Many' is [String]
       toMany :: Π o -> OccType o -> OccType Many
       toMany SOnce  s       = [s]
       toMany SOpt  (Just s) = [s]
       toMany SOpt  Nothing  = []
       toMany SMany ss       = ss
  
   SFalse -> case ps %:<= pt of
     STrue  -> e1 :> combine r1 s2 t1 (e2 :> t2)
     SFalse -> e2 :> combine s1 r2 (e1 :> t1) t2 

-- combine the two results together, when they both are defined
both :: forall s1 s2. (SingI s1, SingI s2) => Result s1 -> Result s2 -> Result (Merge s1 s2)
both (Just xs) (Just ys) = Just $ combine (sing :: Sing s1) (sing :: Sing s2) xs ys
both _         _         = Nothing

-- default value for optional types
defOcc :: Π o -> OccType (Max Opt o)
defOcc SOnce = Nothing    
defOcc SOpt  = Nothing
defOcc SMany = []

-- weaken a value to its maximum
-- This was a not so bad to define.  I made it an id function for every case,
-- then used the four type errors to figure out which lines to change.
-- Agda-like splitting would have helped, though.
glueOccLeft :: Π o1 -> Π o2 -> OccType o2 -> OccType (Max o1 o2)
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
glueOccRight :: Π o1 -> OccType o1 -> Π o2 -> OccType (Max o1 o2)
glueOccRight SOnce m SOnce = m
glueOccRight SOnce m SOpt  = Just m
glueOccRight SOnce m SMany = [m]
glueOccRight SOpt m SOnce  = m
glueOccRight SOpt m SOpt   = m
glueOccRight SOpt (Just m) SMany = [m]
glueOccRight SOpt Nothing SMany  = []
glueOccRight SMany m SOnce = m
glueOccRight SMany m SOpt  = m
glueOccRight SMany m SMany = m

-- Weaken a dictionary by converting all of its entries
-- to 'Max Opt o' versions.
glueLeft :: Π s1 -> Π s2 -> Dict s2 -> Dict (Alt s1 s2)
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
                 
glueRight :: Π s1 -> Dict s1 -> Π s2 -> Dict (Alt s1 s2)
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


-- take the first successful result
-- note that we need to merge in empty labels for the ones that may
-- not be present in the successful version
first :: forall s1 s2. (SingI s1, SingI s2) =>
                      Result s1 -> Result s2 -> Result (Alt s1 s2)
first Nothing Nothing  = Nothing                   
first Nothing (Just y) = Just (glueLeft (sing :: Sing s1) sing y)
first (Just x) _       = Just (glueRight sing x (sing :: Sing s2))

-- A "default" Dict
-- [] for each name in the domain of the set
-- Needs a runtime representation of the set for construction
-- Must use explicit type application when called because this function
-- has a highly ambiguous type.
nils :: forall s. SingI s => Dict (Repeat s)
nils = nils' (sing :: Sing s) where 
    nils' :: Π ss -> Dict (Repeat ss)
    nils' SNil                    = Nil
    nils' (SCons (STuple2 _ _) r) = E [] :> nils' r

    
       
----------------------------------------------------------------
        
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
        
  
-------------------------------------------------------------------------

-- Our GADT, indexed by the set of pattern variables Note that we require all
-- sets, except for the index of Rvoid, to be Wf. (Empty is known to be.)

data R (s :: SM) where
  Rempty :: R Empty 
  Rvoid  :: R s
  Rseq   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
  Ralt   :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt   s1 s2)
  Rstar  :: Wf s => R s  -> R (Repeat s)
  Rchar  :: Set Char -> R Empty
  Rany   :: R Empty
  Rnot   :: Set Char -> R Empty
  Rmark  :: (Wf s) => Sing n -> String -> R s -> R (Merge (One n) s)

-------------------------------------------------------------------------
-- smart constructors
-- we optimize the regular expression whenever we
-- build it.  

-- reduces (r,epsilon) (epsilon,r) to just r
-- (r,void) and (void,r) to void
rseq :: (Wf s1, Wf s2) => R s1 -> R s2 -> R (Merge s1 s2)
rseq Rempty r2 = r2
rseq r1 Rempty = r1
rseq r1 r2 | isVoid r1 = Rvoid
rseq r1 r2 | isVoid r2 = Rvoid
rseq r1 r2             = Rseq r1 r2


-- a special case for alternations when both sides capture the
-- same groups. In this case it is cheap to remove voids
-- reduces void|r and r|void to r    
raltSame :: Wf s => R s -> R s -> R (Alt s s)
raltSame r1 r2 | isVoid r1 = r2
raltSame r1 r2 | isVoid r2 = r1
raltSame r1 r2 = ralt r1 r2

ralt :: forall s1 s2. (Wf s1, Wf s2) => R s1 -> R s2 -> R (Alt s1 s2)
-- we can remove a void on either side if the captured groups are equal
ralt r1 r2 | isVoid r1, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r2
ralt r1 r2 | isVoid r2, Just Refl <- testEquality (sing :: Sing s1) (sing :: Sing s2) = r1
-- some character class combinations
ralt (Rchar s1) (Rchar s2) = Rchar (s1 `Set.union` s2)
ralt Rany       (Rchar s ) = Rany
ralt (Rchar s)  Rany       = Rany
ralt (Rnot s1) (Rnot s2)   = Rnot (s1 `Set.intersection` s2)
ralt r1 r2 = Ralt r1 r2

-- r** = r*
-- empty* = empty
-- void*  = empty
rstar :: forall s. Wf s => R s -> R (Repeat s)
rstar (Rstar s) = Rstar s
rstar Rempty    = Rempty
rstar r1 | isVoid r1, Just Refl <- testEquality (sing :: Sing s) SNil = Rempty
rstar s         = Rstar s
     

-- convenience function for marks
-- MUST use explicit type application for 'n' to avoid ambiguity
rmark :: forall n s. (KnownSymbol n, Wf s) => R s -> R (Merge (One n) s)
rmark = rmarkSing (sing :: Sing n)

rmarkSing :: forall n s proxy.
   (KnownSymbol n, Wf s) => proxy n -> R s -> R (Merge (One n) s)
rmarkSing n = Rmark (sing :: Sing n) ""

-- Not the most general type. However, if rvoid appears in a static
-- regexp, it should have index 'Empty'
rvoid :: R Empty
rvoid = Rvoid

rempty :: R Empty
rempty = Rempty

rchar :: Char -> R Empty
rchar = Rchar . Set.singleton

rchars :: [Char] -> R Empty
rchars = Rchar . Set.fromList

rnot :: [Char] -> R Empty
rnot = Rnot . Set.fromList

ropt :: Wf s => R s -> R (Alt Empty s)
ropt = ralt rempty

rplus :: (Wf (Repeat s),Wf s) => R s -> R (Merge s (Repeat s))
rplus r = r `rseq` rstar r

rany :: R Empty
rany = Rany

------------------------------------------------------
isVoid :: R s -> Bool
isVoid Rvoid          = True
isVoid (Rseq r1 r2)   = isVoid r1 || isVoid r2  
isVoid (Ralt r1 r2)   = isVoid r1 && isVoid r2  
isVoid (Rmark ps s r) = isVoid r
isVoid _              = False

-- is this the regexp that accepts only the empty string?
-- and doesn't capture any subgroups??
isEmpty :: Wf s => R s -> Maybe (s :~: Empty)
isEmpty Rempty        = Just Refl
isEmpty (Rstar r)     | Just Refl <- isEmpty r = Just Refl
isEmpty (Ralt r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty (Rseq r1 r2)  | Just Refl <- isEmpty r1, Just Refl <- isEmpty r2 = Just Refl
isEmpty _             = Nothing


markResult :: Π n -> String -> Result (One n)
markResult n s = Just (E s :> Nil)


       
------------------------------------------------------

-- matching using derivatives
-- we compute the derivative for each letter, then
-- extract the data structure stored in the regexp
match :: Wf s => R s -> String -> Result s
match r w = extract (foldl' deriv r w)

-- Can the regexp match the empty string? 
nullable :: R n -> Bool
nullable Rempty         = True
nullable Rvoid          = False
nullable (Rchar cs)     = False
nullable (Rseq re1 re2) = nullable re1 && nullable re2
nullable (Ralt re1 re2) = nullable re1 || nullable re2
nullable (Rstar re)     = True
nullable (Rmark _ _ r)  = nullable r
nullable Rany           = False
nullable (Rnot cs)      = False

-- regular expression derivative function
deriv :: forall n. Wf n => R n -> Char -> R n
deriv Rempty       c   = Rvoid
deriv (Rseq r1 r2) c   =
      -- use raltSame instead of ralt for
      -- speed. We know the two sides
      -- capture the same groups here
     raltSame (rseq (deriv r1 c) r2)
              (rseq (markEmpty r1) (deriv r2 c))
deriv (Ralt r1 r2) c   = ralt (deriv r1 c) (deriv r2 c)
deriv (Rstar r)      c = rseq (deriv r c) (rstar r)
deriv Rvoid        c   = Rvoid
deriv (Rmark p w r)  c = Rmark p (w ++ [c]) (deriv r c)
deriv (Rchar s)    c   = if Set.member c s then rempty else Rvoid
deriv Rany         c   = rempty
deriv (Rnot s)     c   = if Set.member c s then Rvoid else rempty


-- Create a regexp that *only* matches the empty string in
-- marked locations
-- (if the original could have matched the empty string in the
-- first place)
markEmpty :: forall n. Wf n => R n -> R n
markEmpty (Rmark p w r) = Rmark p w (markEmpty r)
markEmpty (Ralt r1 r2)  = ralt  (markEmpty r1) (markEmpty r2)
markEmpty (Rseq r1 r2)  = rseq  (markEmpty r1) (markEmpty r2)
markEmpty (Rstar r)     = rstar (markEmpty r) 
markEmpty Rempty        = rempty
markEmpty Rvoid         = Rvoid
markEmpty (Rchar c)     = Rvoid
markEmpty (Rnot  c)     = Rvoid
markEmpty Rany          = Rvoid




-- | Extract the result from the regular expression
-- if the regular expression is nullable
-- even if the regular expression is not nullable, there
-- may be some subexpressions that were matched, so return those
extract :: forall s. Wf s => R s -> Result s
extract Rempty         = Just Nil
extract (Rchar cs)     = Nothing
extract (Rseq r1 r2)   = both  (extract r1) (extract r2)
extract (Ralt r1 r2)   = first (extract r1) (extract r2)
extract (Rstar r)      = Just $ nils @s
extract (Rmark n s r)  = withSingI n $ both (markResult n s) (extract r) 
extract (Rnot cs)      = Nothing
extract _              = Nothing

----------------------------------------------------------------
-- Additional library functions for the library, more flexible
-- than match
        
-- | Given r, return the result from the first part 
-- of the string that matches m (greedily... consume as much
-- of the string as possible)
matchInit :: Wf s => R s -> String -> (Result s, String)
matchInit r (x:xs) = let r' = deriv r x in
                 if isVoid r' then (extract r, x:xs)
                 else matchInit r' xs
matchInit r "" = (match r "", "")


pextract :: Wf s => R s -> String -> (Result s, String)
pextract r "" = (match r "", "")
pextract r t  = case matchInit r t of
 (Just r,s)  -> (Just r, s)
 (Nothing,_) -> pextract r (tail t)

-- | Extract groups from the first match of regular expression pat.
extractOne :: Wf s => R s -> String -> Result s
extractOne r s = fst (pextract r s)

-- | Extract groups from all matches of regular expression pat.
extractAll :: Wf s => R s -> String -> [Dict s]
extractAll r s = case pextract r s of
      (Just dict, "")   -> [dict]
      (Just dict, rest) -> dict : extractAll r rest
      (Nothing, _)      -> []

-- | Does this string contain the regular expression anywhere
contains :: Wf s => R s -> String -> Bool
contains r s = case pextract r s of
   (Just r,_)  -> True
   (Nothing,_) -> False

-------------------------------------------------------------------------
-- Show instances for regular expressions

instance Show (Sing (s :: SM)) where
  show r = "[" ++ show' r where
    show' :: Sing (ss :: SM) -> String
    show' SNil = "]"
    show' (SCons (STuple2 sn so) ss) = show sn ++ "," ++ show' ss
instance SingI n => Show (R n) where
  show Rvoid  = "ϕ" 
  show Rempty = "ε"
  show (Rseq r1 (Rstar r2)) | show r1 == show r2 = maybeParens r1 ++ "+"
  show (Rseq r1 r2)    = show r1 ++ show r2
  show (Ralt Rempty r) = maybeParens r ++ "?"
  show (Ralt r1 r2) = "(" ++ show r1 ++ "|" ++ show r2 ++ ")"
  show (Rstar r)    = maybeParens r ++ "*"
  show (Rchar cs)   = if (Set.size cs == 1) then (escape (head (Set.toList cs)))
                   else if cs == (Set.fromList chars_digit) then "\\d"
                   else if cs == (Set.fromList chars_whitespace) then "\\s"
                   else if cs == (Set.fromList chars_word) then "\\w"
                   else "[" ++ concatMap escape (Set.toList cs) ++ "]"
     where
       chars_whitespace = " \t\n\r\f\v"
       chars_digit      = ['0' .. '9']
       chars_word       = ('_':['a' .. 'z']++['A' .. 'Z']++['0' .. '9'])
  show (Rmark pn w r)  = "(?P<" ++ show pn ++ ">" ++ show r ++ ")"
  show Rany = "."
  show (Rnot cs) = "[^" ++ concatMap escape (Set.toList cs) ++ "]"

-- escape special characters
escape :: Char -> String
escape c  = if c `elem` specials then "\\" ++ [c] else [c] where
       specials         = ".[{}()\\*+?|^$"
  
maybeParens :: SingI s => R s -> String
maybeParens r = if needsParens r then "(" ++ show r ++ ")" else show r

needsParens :: R s -> Bool
needsParens Rvoid = False
needsParens Rempty = False
needsParens (Rseq r1 r2) = True
needsParens (Ralt r1 r2) = True
needsParens (Rstar r)    = True
needsParens (Rchar cs)   = False
needsParens (Rany)       = False
needsParens (Rnot _)     = False
needsParens (Rmark _ _ _) = False

   

