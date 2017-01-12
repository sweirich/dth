{-# LANGUAGE TemplateHaskell, QuasiQuotes, OverloadedStrings #-}
{-# LANGUAGE DataKinds, KindSignatures, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TypeOperators #-}

module RegexpExample where

import RegexpParser

import NeatInterpolation
import Data.Text.Internal (showText)

import qualified Data.Set as Set

import qualified Data.Maybe as Maybe

import GHC.TypeLits



path  = [re|/?((?P<d>[^/]+)/)*(?P<b>[^/.]+)(?P<e>\..*)?|]

rpath = ropt (rchars "/") `rseq`
        rstar (rmark @"d" (rplus (rnot "/")) `rseq` (rchars "/")) `rseq`
        rmark @"b" (rplus (rnot "/.")) `rseq`
        ropt (rmark @"e"  ((rchars ".") `rseq` (rstar rany)))


files = ["/Users/sweirich/github/dth/popl17/RegexpExample.hs", 
         "/Users/sweirich/github/dth/popl17/influence.pptx",
         "/Users/sweirich/github/dth/popl17/LICENSE"]


{-
notc = Rnot (Set.fromList [','])

-----------------------------------------------------------
-----------------------------------------------------------
rname  = [re|?P<name>[A-Z][a-z]*|]

rphone = [re|?P<phone>\d\d\d-\d\d\d\d|]
degree = [re|?P<degree>BA|BS|MS|PHD|MBA|]

pb    = [re|\{${rname}\s*(${degree}\s*)*${rphone}?\}|]

pb2  = rname `rseq` (ralt rempty rphone)

x = match pb "{V PHD BS 123-4567}"    
name = getField @"name" x       -- :: String
phone = getField @"phone" x     -- :: Maybe String
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
fulldate = [re|?P<date>....-..-..|]
score  = [re|?P<score>\d\d\d\d\.\d|]

-- Which rows contain dates?
c0 = map (contains fulldate) dat

-- Extract the column of single digits
c1 = map (extractOne female) dat

-- Extract the column of dates
c2 = map (extractOne fulldate) dat

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
line   = state <+> female <+> fulldate <+> score

-- we can use the combo regexp on each line
rows = map (extractOne line) dat

-- or we can use extractAll to extract the rows directly
rows' = extractAll line (concat dat)

-- or we can also get the columns this way (but it can be slow)
columns = match (rstar line) (concat dat)

--DAY	DESCRIPTION	HIGH/LOW	PRECIP	WIND	HUMIDITY	UV INDEX	SUNRISE	SUNSET	MOONRISE	MOONSET

day   = [re|MON|TUE|WED|THU|FRI|SAT|SUN|]
month = [re|JAN|FEB|MAR|APR|]
date  = [re|\d|\d\d|]
desc  = [re|Sunny|Partly Cloudy|Rain|Snow|Mostly Cloudy|]
temp  = [re|(\d|\d\d|\d\d\d)°|]
time  = [re|\d\d?:\d\d (am|pm)|]
prec  = [re|\d\d\d?%|]

multidesc = rstar (desc `rseq` rchar '/') `rseq` desc

mt :: forall n. KnownSymbol n => R '[n :=> 'Opt] 
mt = (rmark @n time) `ralt` [re|--|]

weather = day <+> month <+> date <+> multidesc <+> temp <+> temp <+> prec <+> prec <+> mt @"sunrise" <+> mt @"sunset" <+> mt @"moonrise" <+> mt @"moonset"

paris_weather = 
 ["SUN JAN 15 Rain/Snow     41°  34° 60% 83% 8:38 am 5:21 pm 9:12 pm 10:17 am",
  "WED JAN 18 Sunny         29°  20° 10% 70% 8:36 am 5:26 pm -- 11:38 am",
  "THU JAN 19 Partly Cloudy 29°  20° 10% 72% 8:35 am 5:27 pm 12:29 am 12:03 pm",
  "FRI JAN 20 Partly Cloudy 29°  21° 10% 68% 8:34 am 5:29 pm 1:30 am 12:29 pm",
  "SAT JAN 21 Sunny         32°  21° 10% 74% 8:33 am 5:30 pm 2:32 am 12:57 pm"]
-}
