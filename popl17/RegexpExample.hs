{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
{-# LANGUAGE DataKinds, KindSignatures, TypeApplications #-}

module RegexpExample where

import RegexpSet 
import RegexParser

import qualified Data.Set as Set

-- whitespace characters
ws = rchars (Set.fromList ['\n', '\r', ' ', '\t'])
-- newline characters
nl = rchars (Set.fromList ['\n', '\r'])
-- open brace
open  = rchars (Set.fromList ['{' , '\"'])
close = rchars (Set.fromList ['}' , '\"'])

line = [regex|.*=.*,|]
popl = [regex|booktitle${ws}*=${ws}*${open}POPL.*${close},|]
title = [regex|title${ws}*=${ws}*${open}(?P<name>.*)${close},${nl}|]

entry = [regex|article${open}.*{close}|]



rname  = [regex|[A-Z][a-z]*|]
d     = [regex|[0-9]|]
rphone = [regex|${d}${d}${d}-${d}${d}${d}${d}|]

pb    = [regex|?P<name>{rname}|]

x = match pb "sdfkdsfh"    -- :: Result '["email","name"]
name = getField @"name" x       -- :: Maybe [String]
--phone = getField @"phone" x     -- :: Maybe [String]
-- email = getField @"email" x     -- TypeError
