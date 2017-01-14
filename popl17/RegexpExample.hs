{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}  -- for regex parser
{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables, 
    TypeApplications, AllowAmbiguousTypes, TypeOperators #-}

module RegexpExample where

import RegexpParser
import qualified Data.Maybe as Maybe
import GHC.TypeLits

path  = [re|/?((?P<d>[^/]+)/)*(?P<b>[^/.]+)(?P<e>\..*)?|]

filename = "dth/popl17/Regexp.hs"























         
---------------------------------------------------------         

rpath = ropt (rchars "/") `rseq`
        rstar (rmark @"d" (rplus (rnot "/")) `rseq` (rchars "/")) `rseq`
        rmark @"b" (rplus (rnot "/.")) `rseq`
        ropt (rmark @"e"  ((rchars ".") `rseq` (rstar rany)))


---------------------------------------------------------
      
files = ["/Users/sweirich/github/dth/popl17/RegexpExample.hs", 
         "/Users/sweirich/github/dth/popl17/influence.pptx",
         "/Users/sweirich/github/dth/popl17/LICENSE"]

