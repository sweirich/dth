{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}  -- for regex parser
{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables,
    TypeApplications, AllowAmbiguousTypes, TypeOperators #-}

-- For best results for playing in ghci
--  :set -XTypeApplications
--  :set -XDataKinds
--  :set -XQuasiQuotes
--  :set -XFlexibleContexts
module RegexpExample where

import RegexpParser
import Data.Maybe (fromJust)



-- A regular expression for selecting the directories "d"
-- basename "b" and extension "e" from a path

path = [re|/?((?P<d>[^/]+)/)*(?P<b>[^\./]+)(?P<e>\..*)?|]

-- match the regular expression against the string
-- returning a dictionary of the matched substrings
filename = "dth/regexp/Regexp.hs"
dict = fromJust (match path filename)

x      = getField @"b" dict
y      = getField @"d" dict
z      = getField @"e" dict
--w      = getField @"f" dict
