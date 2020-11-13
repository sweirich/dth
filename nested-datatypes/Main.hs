module Main where

import Criterion.Main

import Nested

depth :: Int
depth = 20

bsum depth = bgroup ("sum" ++ show depth) [ bench "Tree"  $ whnf sum $ replicateTree (3::Int) depth
                , bench "NTree" $ whnf sum $ replicateNTree (3::Int) depth
                , bench "DTree" $ whnf sum $ replicateDTree (3::Int) depth
                , bench "FTree" $ whnf sum $ replicateFTree (3::Int) depth
                ]

beq depth = bgroup ("eq" ++ show depth) [
                  bench "Tree"  $ whnf (== replicateTree (3::Int) depth)  $ replicateTree (3::Int) depth
                , bench "NTree" $ whnf (== replicateNTree (3::Int) depth) $ replicateNTree (3::Int) depth
                , bench "DTree" $ whnf (== replicateDTree (3::Int) depth) $ replicateDTree (3::Int) depth
                , bench "FTree" $ whnf (== replicateFTree (3::Int) depth) $ replicateFTree (3::Int) depth
                ]


main = defaultMain [
    bsum 20
  , bsum 21    
  , bsum 22
  , bsum 23
  , beq 20
  , beq 21    
  , beq 22
  , beq 23
  ]
