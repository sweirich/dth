-- For best results in ghci
--  :set -XTypeApplications
--  :set -XDataKinds
--  :set -XQuasiQuotes
--  :set -XFlexibleContexts

{-# LANGUAGE TemplateHaskell, QuasiQuotes,
    DataKinds, GADTs, TypeFamilies,
    TypeApplications, AllowAmbiguousTypes #-}

module RegexpExample where

import RegexpParser
import Data.Maybe (fromJust)

-- A regular expression for selecting the directories "dir"
-- basename "base" and extension "ext" from a filepath

path = [re|/?((?P<dir>[^/]+)/)*(?P<base>[^\./]+)(?P<ext>\..*)?|]

-- match the regular expression against the string
-- returning a dictionary of the matched substrings
filename = "dth/regexp/Example.hs"
dict = fromJust (match path filename)

-- Access the components of the dictionary

x = getField @"base" dict
y = getField @"dir" dict
z = getField @"ext" dict

-- w = getField @"f" dict







------------------------------
-- Type computation examples
--


ra = rmark @"a" (rstar rany)


rb = rmark @"b" rany





ex1 = rb `rseq` ra




ex2 = ra `ralt` (rb `rseq` ra)





ex3 = rstar (ra `rseq` rb)






--------------------------------
-- Indexed types examples
--

entry1 :: Entry "base" Once
entry1 = E "Example"


entry2 = E @"ext" (Just "hs")

entry3 = E @"dir" ["dth", "regexp"]


d = entry1 :> entry3 :> entry2 :> Nil

------------------------------------
--
--
