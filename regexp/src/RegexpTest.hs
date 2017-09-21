{-# LANGUAGE TypeApplications, GADTs, DataKinds, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | Some simple unit test cases for the regular expression module (no parser)
-- If you happen to think that it is impossible to have bugs in Haskell programs,
-- and especially not dependently-typed Haskell programs, you are sorely mistaken.
-- I went through so many correctness and performance bugs in this implementation
-- that I was tempted to give up entirely. I hope I got them all, but if I didn't,
-- caveat emptor.
module RegexpTest where

--import Regexp
import RegexpDependent
-- The non-dependently-typed Regexp module exports the same interface as the
-- RegexpDependent version. This helped me figure out the semantics of the
-- system that I wanted before adding dependent types.


import qualified Data.Set as Set

import Test.HUnit
import Data.Maybe

----------------------------------------------------------

r1 = ralt (rchar 'a') (rchar 'b')

r2 = rmark @"a" r1

r4 = rstar (rmark @"b" (rseq r1 r1))

r5 = ralt (rmark @"b" (rchar 'a')) (rmark @"b" (rchar 'b'))

r6 = ralt (rmark @"a" (rchar 'a')) (rmark @"b" (rchar 'b'))

r7 = ralt (rmark @"b" (rchar 'b')) (rmark @"b" (rchar 'b'))

r8 = rmark @"x" (rstar (rchar 'a'))

r9 = rmark @"c" (rseq (rstar (rchar 'c')) r6)

-- Our implementation is greedy like Posix.
greedy = rstar (rmark @"a" (rchar 'a')
                `ralt` (rmark @"ab" (rchar 'a' `rseq` rchar 'b'))
                `ralt` (rmark @"b" (rchar 'b')))



greedytest = match greedy "ab"
-- returns Just [a:[],ab:["ab"],b:[]]


r10 = (rstar Rany) `rseq` rmark @"a" (rchar 'a')

r11 = (rstar (rmark @"n" (rchar 'a')) `rseq` (rchar '}'))

r12 =  ((ralt rempty (rmark @"n" (rchar 'a'))) `rseq` (rchar 'b'))

r13 =  ((ralt (rmark @"n" (rchar 'a')) rempty) `rseq` (rchar 'b'))


main = runTestTT $
       TestList [
         "1" ~: assert $ isJust (match r1 "a"),
         "2" ~: assert $ isNothing (match r1 "c"),
         "3" ~: getValues @"a" (match r2 "a") ~?= ["a"],
--         "4" ~: getValues @"a" (match r4 "aa") ~?= [],
         "5" ~: getValues @"b" (match r4 "aa") ~?= ["aa"],
         "6" ~: getValues @"b" (match r4 "aaba") ~?= ["aa","ba"],
         "7" ~: getValues @"b" (match r5 "a") ~?= ["a"],
         "8" ~: getValues @"b" (match r5 "b") ~?= ["b"],
--         "9" ~: getValues @"a" (match r5 "b") ~?= [],
         "10" ~: getValues @"b" (match r6 "a") ~?= [],
         "11" ~: getValues @"b" (match r6 "b") ~?= ["b"],
         "12" ~: getValues @"a" (match r6 "b") ~?= [],
         "13" ~: getValues @"b" (match r7 "b") ~?= ["b"],
         "14" ~: getValues @"x" (match r8 "aaa") ~?= ["aaa"],
         "15" ~: getValues @"c" (match r9 "cb") ~?= ["cb"],
         "g1" ~: getValues @"a"  greedytest ~?= [],
         "g2" ~: getValues @"ab" greedytest ~?= ["ab"],
         "g3" ~: getValues @"b"  greedytest ~?= [],
         "c1" ~: getValues @"a" (match r10 "a") ~?= ["a"],
         "r11" ~: getValues @"n" (match r11 "a}") ~?= ["a"],
         "r12" ~: getValues @"n" (match r12 "ab") ~?= ["a"],
         "r13" ~: getValues @"n" (match r13 "ab") ~?= ["a"]
--         "c2" ~: getValues @"b" (match r10 "a") ~?= []
       ]


-------------------------------------------------------------------------

digit = Rchar (Set.fromList ['0' .. '9'])
dash  = Rchar (Set.fromList ['-','.',' '])

opt_dash = ralt dash rempty

phone = rmark @"phone"
   (digit `rseq` digit `rseq` digit `rseq` opt_dash
    `rseq` digit `rseq`  digit `rseq` digit `rseq` digit)

alpha  = Rchar (Set.fromList ['a' .. 'z' ])
alphaC = Rchar (Set.fromList ['A' .. 'Z' ])

name   = rmark @"name" (rseq alphaC (rstar alpha))

entry  = (name `rseq` rstar opt_dash `rseq` (ralt rempty phone))

pbook  = rstar (rchar '(' `rseq` (rmark @"entry" entry) `rseq` rchar ')')

pbookstring = "(Steve 123-2222)(Stephanie 1202323)(Ellie 121.1222)(Sarah 324-3444)"

result = match pbook pbookstring


nm = getValues @"name"  result
ph = getValues @"phone" result

-- Doesn't type check on enhanced versions
--bad = getValues @"email" result

-------------------------------------------------------------------------
-- For RegexpDependent also check out the more refined types that are possible:

nm2 = getField @"name" $ fromJust (match entry "Stephanie")
ph2 = getField @"phone" $ fromJust (match entry "Stephanie")

-------------------------------------------------------------------------

-- difficult pattern for backtracking implementations, like this one.
difficult = rstar (ralt (rchar 'a') (rchar 'a' `rseq` rchar 'a'))
                  `rseq` (rchar 'b')

sloooow =  match difficult "aaaaaaaaaaaaaaaaaaaaaaaab"
