{-# LANGUAGE GADTs, EmptyDataDecls, MultiParamTypeClasses, FunctionalDependencies, UndecidableInstances #-}

-- version due to Tim Sheard


-- size is number of arguments (must be nonzero)
-- fun is the type of the function to map across the list

data Nat fun dom rng where
 One  :: Nat (a -> b) [a] [b]
 Succ :: Nat x y z -> Nat (a -> x) [a] (y -> z)

defalt :: Nat a b c -> c
defalt One      = []
defalt (Succ n) = \ _ -> defalt n  

mapflat :: Nat a b c -> a -> (b -> c) -> (b -> c)
mapflat One f recall (x:xs) = f x : recall xs
mapflat One f recall [] = []
mapflat (Succ n) f recall (x:xs) = mapflat n (f x) (recall xs)
mapflat (Succ n) f recall [] = defalt (Succ n) 

zipWithN :: Nat a b c -> a -> b -> c
zipWithN n f x = mapflat n f (zipWithN n f) x


----------------------------------------------------------------------