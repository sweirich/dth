{-# LANGUAGE TemplateHaskell, QuasiQuotes, OverloadedStrings #-}
{-# LANGUAGE DataKinds, KindSignatures, TypeApplications, AllowAmbiguousTypes #-}

module RegexpExample where

import RegexpParser

import NeatInterpolation
import Data.Text.Internal (showText)

import qualified Data.Set as Set

import qualified Data.Maybe as Maybe



bibentry = showText [text|@InProceedings{sjoberg:congruence,
  author = 	  {Vilhelm Sj\"oberg and Stephanie Weirich},
  title = 	  {Programming up to Congruence},
  booktitle = {POPL 2015: 42nd ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages},
  month = 	  jan,
  year = 	  2015,
  address =   {Mumbai, India},
  pages =     {369--382},
  pdf =       {http://www.seas.upenn.edu/~sweirich/papers/popl15-congruence.pdf}
}|]

notc = Rnot (Set.fromList [','])


month = [re|jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec|]
year  = [re|(?P<year>\d\d\d\d)|]

--bibline = [re|(?P<tag>\w)*\s*=\s*{[^,]*},?\n|]

anyy  = [re|.*${year}|]
fy    = [re|(${anyy})*.*|]

-- open brace
open  = rchars (Set.fromList ['{' , '\"'])
close = rchars (Set.fromList ['}' , '\"'])


popl = [re|booktitle\s*=\s*${open}POPL.*${close},|]
title = [re|title\s*=\s*${open}(?P<name>.*)${close},\n|]

entry = [re|article${open}.*${close}|]


-----------------------------------------------------------
-----------------------------------------------------------

rname  = [re|?P<name>[A-Z][a-z]*|]
rphone = [re|?P<phone>\d\d\d-\d\d\d\d|]
degree = [re|?P<degree>BA|BS|MS|PHD|MBA|]

pb    = [re|\{${rname}\s*(${degree}\s*)*${rphone}?\}|]

pb2  = rname `rseq` (ralt rempty rphone)

Just x = match pb "{V 123-4567}"    
name = getFieldD @"name" x       -- :: String
phone = getFieldD @"phone" x     -- :: Maybe String
--email = getField @"email" x     -- TypeError

-----------------------------------------------------------
-----------------------------------------------------------
-- pandas example
-- http://chrisalbon.com/python/pandas_regex_to_create_columns.html

dat = ["Arizona 1 2014-12-23       3242.0",
        "Iowa 1 2010-02-23       3453.7",
        "Oregon 0 2014-06-20       2123.0",
        "Maryland 0 2014-03-14       1123.6",
        "Florida 1 2013-01-15       2134.0",
        "Georgia 0 2012-07-14       2345.6"]

-- some regular expressions for the individual pieces
state  = [re|?P<state>[A-Z]\w*|]
female = [re|?P<female>\d|]
date   = [re|?P<date>....-..-..|]
score  = [re|?P<score>\d\d\d\d\.\d|]

-- Which rows contain dates?
c0 = map (contains date) dat

-- Extract the column of single digits
c1 = map (extractOne female) dat

-- Extract the column of dates
c2 = map (extractOne date) dat

-- Extract the column of thousands
c3 = map (extractOne score) dat

-- Extract the column of words
c4 = map (extractOne state) dat

-- Glue all columns together to make a table
beside = zipWith both
table = c1 `beside` c2 `beside` c3 `beside` c4

----------------------------------------------
-- instead of doing things like the demo, we can
-- also extract all of the information at once with a
-- regexp for the entire line's worth of data.

r1 <+> r2  = r1 `rseq` [re|\s*|] `rseq` r2 
line   = state <+> female <+> date <+> score

t1 = map (extractOne line) dat

-- or we can also get the columns this way
columns = match (rstar line) (concat dat)

-- or we can use extractAll to extract the rows directly
rows = extractAll line (concat dat)


