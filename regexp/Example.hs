{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}  -- for regex parser
{-# LANGUAGE DataKinds, GADTs, TypeFamilies, KindSignatures, ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, TypeOperators #-}

-- For best results for playing in ghci
--  :set -XTypeApplications
--  :set -XDataKinds
--  :set -XQuasiQuotes
--  :set -XFlexibleContexts
module RegexpExample where

import RegexpParser
import Data.Maybe (fromJust)



-- A regular expression for selecting the directories "dir"
-- basename "base" and extension "ext" from a path

path = [re|/?((?P<dir>[^/]+)/)*(?P<base>[^\./]+)(?P<ext>\..*)?|]

-- match the regular expression against the string
-- returning a dictionary of the matched substrings
filename = "dth/regexp/Regexp.hs"
dict = fromJust (match path filename)

x      = getField @"base" dict
y      = getField @"dir" dict
z      = getField @"ext" dict
--w      = getField @"f" dict




------------------------------
-- Type computation examples
--

r1 = rmark @"ext" (rstar rany)

r2 = rmark @"base" rany


-- r1 r2
ex1 = r1 `rseq` r2


-- r1 | r1 r2
ex2 = r1 `ralt` (r1 `rseq` r2)


-- r1 r1*
ex3 = r1 `seq` (rstar r1)



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
