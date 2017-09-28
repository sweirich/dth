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
-- basename "base" and extension "ext" from a filepath

path = [re|/?((?P<dir>[^/]+)/)*(?P<base>[^\./]+)(?P<ext>\..*)?|]

-- match the regular expression against the string
-- returning a dictionary of the matched substrings
filename = "dth/regexp/Regexp.hs"
dict = fromJust (match path filename)

-- Access the components of the dictionary

x      = getField @"base" dict
y      = getField @"dir" dict
z      = getField @"ext" dict

-- Look for Haskell package that allows "expect type check failure

--w      = getField @"f" dict




------------------------------
-- Type computation examples
--

rext = rmark @"ext" (rstar rany)

rbase = rmark @"base" rany


-- rext rbase
ex1 = rext `rseq` rbase


-- rext | rext rbase
ex2 = rext `ralt` ex1


-- rext rext
ex3 = rext `rseq` rext



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
