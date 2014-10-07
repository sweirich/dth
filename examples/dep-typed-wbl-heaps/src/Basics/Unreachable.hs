-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
--                                                                   --
-- GHC's current mechanism for checking pattern exhaustiveness are   --
-- not smart enough to use the type information from GADT pattern    --
-- matching. The result is that GHC complains about non-exhaustive   --
-- patterns even if some of them are unreachable due to type         --
-- restrictions. However, if we write down the constructors          --
-- explicitly in the inaccesible pattern matches then GHC will       --
-- reject them as unreachable code (quite rightly). The solution is  --
-- to write catch-all patterns. See #3927, #4139, #6124, #8970.      --
--                                                                   --
-- The solution I have addapted here is to create alias for          --
-- undefined. This has two goals. Firstly, it makes reading code     --
-- easier. Secondly, once the pattern exhaustiveness checking is     --
-- fixed I can easily locate all unreachable equations in this       --
-- project.                                                          --
-----------------------------------------------------------------------
{-# LANGUAGE NoImplicitPrelude #-}
module Basics.Unreachable where

import Prelude (undefined)

unreachable :: a
unreachable = undefined
