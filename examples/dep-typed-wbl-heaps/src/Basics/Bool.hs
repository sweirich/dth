-----------------------------------------------------------------------
-- Copyright: 2014, Jan Stolarek, Politechnika Łódzka                --
--                                                                   --
-- License: See LICENSE file in root of the repo                     --
-- Repo address: https://github.com/jstolarek/dep-typed-wbl-heaps-hs --
--                                                                   --
-- Definition of Bool datatype, which represents logical True and    --
-- False.                                                            --
-----------------------------------------------------------------------

{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE NoImplicitPrelude #-}
module Basics.Bool where

data Bool :: * where
  False :: Bool
  True  :: Bool
