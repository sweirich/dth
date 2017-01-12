{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fdefer-type-errors #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}


module RegexpQuick where

import Regexp
import Test.QuickCheck
import Data.Set(Set)
import qualified Data.Set as Set
-------------------------------------------------------------------------

deriving instance (Eq R)

arbchars :: Gen (Set Char)
arbchars = Set.fromList <$> (listOf1 (elements ['a' .. 'm']))

arbname :: Gen String
arbname = elements ['n' .. 'z'] >>= \c -> return [c]

instance Arbitrary R where
   arbitrary = sized genR where
     genR 0 = oneof [ return Rempty,
                      return Rvoid,
                      return Rany, Rchar <$> arbchars , Rnot <$> arbchars ]
     genR n = frequency [(1, genR 0),
                         (n, Rseq  <$> genR (n `div` 2) <*> genR (n `div` 2)),
                         (n, Ralt  <$> genR (n `div` 2) <*> genR (n `div` 2)),
                         (n, Rstar <$> genR (n `div` 2)),
                         (n, Rmark <$> arbname <*> return [] <*> genR (n `div` 2))]

   shrink (Rchar c) = Rchar <$> (shrink c)
   shrink (Ralt r1 r2)  = [Ralt r1' r2 | r1' <- shrink r1] ++ [Ralt r1 r2' | r2' <- shrink r2] ++ [r1, r2]
   shrink (Rseq r1 r2)  = [Rseq r1' r2 | r1' <- shrink r1] ++ [Rseq r1 r2' | r2' <- shrink r2] ++ [r1, r2]
   shrink (Rmark n w r) = (Rmark n w <$> shrink r)  ++ [r]
   shrink (Rstar r)     = (Rstar <$> shrink r)  ++ [r]
   shrink _ = []


optimize (Rseq r1 r2) = rseq (optimize r1) (optimize r2)
optimize (Ralt r1 r2) = ralt (optimize r1) (optimize r2)
optimize (Rstar r)    = rstar (optimize r)
optimize (Rmark n w r) = rmarkInternal n w (optimize r)
optimize r = r

prop_markEmpty r = if nullable r then nullable (markEmpty r) else isVoid (markEmpty r)

deriv' :: R -> Char -> R
deriv' Rempty        c = Rvoid
deriv' (Rseq r1 r2)  c =
     ralt (rseq (deriv' r1 c) r2) 
          (rseq (markEmpty r1) (deriv' r2 c))
deriv' (Ralt r1 r2)  c = ralt (deriv' r1 c) (deriv' r2 c)
deriv' (Rstar r)     c = rseq (deriv' r c) (rstar r)
deriv' Rvoid         c = Rvoid
deriv' (Rmark n w r) c = rmarkInternal n (w ++ [c]) (deriv' r c)
deriv' (Rchar s)     c = if Set.member c s then rempty else Rvoid
deriv' Rany  c         = rempty
deriv' (Rnot s)      c = if Set.member c s then Rvoid else rempty


prop_sameDeriv r1 r2 c =
   collect (nullable r1) $
   optimize (deriv (Rseq r1 r2) c) == optimize (deriv' (Rseq r1 r2) c)

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith (stdArgs { maxSuccess = 1000 })


prop_isEmpty r =
  isEmpty r ==> nullable r

prop_isVoid r =
  isVoid r ==> not (nullable r)

