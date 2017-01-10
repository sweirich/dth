{-# LANGUAGE TypeApplications, GADTs, DataKinds, PartialTypeSignatures #-}
{-# OPTIONS_GHC -Wno-partial-type-signatures #-}

-- | some simple unit test cases for the regular expression module (no parser)
module RegexpTest where

import RegexpDependent
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
         "3" ~: getField @"a" (match r2 "a") ~?= ["a"],
--         "4" ~: getField @"a" (match r4 "aa") ~?= [],
         "5" ~: getField @"b" (match r4 "aa") ~?= ["aa"],
         "6" ~: getField @"b" (match r4 "aaba") ~?= ["aa","ba"],
         "7" ~: getField @"b" (match r5 "a") ~?= ["a"],
         "8" ~: getField @"b" (match r5 "b") ~?= ["b"],
--         "9" ~: getField @"a" (match r5 "b") ~?= [],
         "10" ~: getField @"b" (match r6 "a") ~?= [],
         "11" ~: getField @"b" (match r6 "b") ~?= ["b"],
         "12" ~: getField @"a" (match r6 "b") ~?= [],
         "13" ~: getField @"b" (match r7 "b") ~?= ["b"],
         "14" ~: getField @"x" (match r8 "aaa") ~?= ["aaa"],
         "15" ~: getField @"c" (match r9 "cb") ~?= ["cb"],
         "g1" ~: getField @"a"  greedytest ~?= [],
         "g2" ~: getField @"ab" greedytest ~?= ["ab"],
         "g3" ~: getField @"b"  greedytest ~?= [],
         "c1" ~: getField @"a" (match r10 "a") ~?= ["a"],
         "r11" ~: getField @"n" (match r11 "a}") ~?= ["a"],
         "r12" ~: getField @"n" (match r12 "ab") ~?= ["a"],
         "r13" ~: getField @"n" (match r13 "ab") ~?= ["a"]
--         "c2" ~: getField @"b" (match r10 "a") ~?= []
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

entry  = name `rseq` rstar opt_dash `rseq` (ralt rempty phone) 

pbook  = rstar (rchar '(' `rseq` (rmark @"entry" entry) `rseq` rchar ')')

pbookstring = "(Steve 123-2222)(Stephanie 1202323)(Ellie 121.1222)(Sarah 324-3444)"

result = match pbook pbookstring


nm = getField @"name"  result
ph = getField @"phone" result

-- Doesn't type check on enhanced versions
-- bad = getField @"email" result

-------------------------------------------------------------------------
-- For RegexpOcc also check out the more refined types that are possible:

--nm2 = getFieldD @"name" $ fromJust (match entry "Stephanie")
--ph2 = getFieldD @"phone" $ fromJust (match entry "Stephanie")


-------------------------------------------------------------------------

-- difficult pattern for backtracking implementations, like this one.
difficult = rstar (ralt (rchar 'a') (rchar 'a' `rseq` rchar 'a'))
                  `rseq` (rchar 'b')

sloooow =  match difficult "aaaaaaaaaaaaaaaaaaaaaaaab"



{-
InternalDate = re.compile(r'INTERNALDATE "'
        r'(?P<day>[ 123][0-9])-(?P<mon>[A-Z][a-z][a-z])-'
        r'(?P<year>[0-9][0-9][0-9][0-9])'
        r' (?P<hour>[0-9][0-9]):(?P<min>[0-9][0-9]):(?P<sec>[0-9][0-9])'
        r' (?P<zonen>[-+])(?P<zoneh>[0-9][0-9])(?P<zonem>[0-9][0-9])'
        r'"')
-}

