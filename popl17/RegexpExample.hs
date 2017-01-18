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




       
path = [re|/?((?P<d>[^/]+)/)*(?P<b>[^\./]+)(?P<e>\..*)?|]

filename = "dth/popl17/Regexp.hs"

result   = match path filename
dict   = fromJust result

x      = get @"b" dict
y      = get @"d" dict
z      = get @"e" dict
w      = get @"f" dict

       






















         






