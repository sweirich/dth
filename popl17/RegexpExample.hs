{-# LANGUAGE TemplateHaskell, QuasiQuotes, OverloadedStrings #-}
{-# LANGUAGE DataKinds, KindSignatures, TypeApplications #-}

module RegexpExample where

import RegexpParser

import NeatInterpolation
import Data.Text.Internal (showText)

import qualified Data.Set as Set



bibentry = showText [text|@InProceedings{sjoberg:congruence,
  author = 	  {Vilhelm Sj\"oberg and Stephanie Weirich},
  title = 	  {Programming up to Congruence},
  booktitle = {POPL 2015: 42nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages},
  month = 	  jan,
  year = 	  2015,
  address =   {Mumbai, India},
  plclub =    {yes},
  pages =     {369--382},
  pdf =       {http://www.seas.upenn.edu/~sweirich/papers/popl15-congruence.pdf}
}|]

notc = Rnot (Set.fromList [','])


d     = [re|[0-9]|]
month = [re|jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec|]
year  = [re|(?P<year>${d}${d}${d}${d})|]

anyy  = [re|.*${year}|]
fy    = [re|(${anyy})*.*|]

-- whitespace characters
ws = rchars (Set.fromList ['\n', '\r', ' ', '\t'])
-- newline characters
nl = rchars (Set.fromList ['\n', '\r'])
-- open brace
open  = rchars (Set.fromList ['{' , '\"'])
close = rchars (Set.fromList ['}' , '\"'])

line = [re|.*=.*,|]
popl = [re|booktitle${ws}*=${ws}*${open}POPL.*${close},|]
title = [re|title${ws}*=${ws}*${open}(?P<name>.*)${close},${nl}|]

entry = [re|article${open}.*{close}|]



rname  = [re|[A-Z][a-z]*|]

rphone = [re|${d}${d}${d}-${d}${d}${d}${d}|]

pb    = [re|?P<name>{rname}|]

x = match pb "sdfkdsfh"    -- :: Result '["email","name"]
name = getField @"name" x       -- :: Maybe [String]
--phone = getField @"phone" x     -- :: Maybe [String]
-- email = getField @"email" x     -- TypeError
