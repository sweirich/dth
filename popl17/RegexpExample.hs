{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}  -- for regex parser
{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables, 
    TypeApplications, AllowAmbiguousTypes, TypeOperators #-}

-- For best results in ghci
--  :set -XTypeApplications
--  :set -XDataKinds
--  :set -XQuasiQuotes
--  :set -XFlexibleContexts
module RegexpExample where

import RegexpParser
import Data.Maybe
import GHC.TypeLits




       
path  = [re|/?((?P<dirs>[^/]+)/)*(?P<base>[^\./]+)(?P<ext>\..*)?|]

filename = "dth/popl17/Regexp.hs"


result = match path filename

dict   = fromJust result

bn     = get @"base" dict
ds     = get @"dirs" dict
-- bad    = get @"name" dict       
       



















         
---------------------------------------------------------         

rpath = ropt (rchars "/") `rseq`
        rstar (rmark @"d" (rplus (rnot "/")) `rseq` (rchars "/")) `rseq`
        rmark @"b" (rplus (rnot "/.")) `rseq`
        ropt (rmark @"e"  ((rchars ".") `rseq` (rstar rany)))



