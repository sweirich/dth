> {-# LANGUAGE TypeOperators, DataKinds, KindSignatures, GADTs, TypeFamilies, UndecidableInstances, ScopedTypeVariables, ExplicitForAll, PolyKinds #-}
> {-# LANGUAGE TemplateHaskell #-}

See Conrad Parker, "Type Level Instant Insanity"
http://www.haskell.org/wikiupload/d/dd/TMR-Issue8.pdf

An attempt to port this code to use the singletons library instead of MPTC+FD

> import Prelude hiding (all, flip, map, filter)

> import Data.Singletons.Prelude 
> import Data.Singletons.TH

> $(singletons [d|
>    
>     data Color = R -- Red
>            | G -- Green
>            | B -- Blue
>            | W -- White 
>        deriving (Eq, Show)
>
>     data Cube = Cube Color Color Color Color Color Color
>        deriving (Eq, Show)

>     -- Rotate a cube 90 degrees over its Z-axis, leaving up and down in place.
>     -- Singletons note: these type signatures are required
>     rot :: Cube -> Cube
>     rot (Cube u f r b l d) = Cube u r b l f d
> 
>
>     -- Twist a cube around the axis running from the upper-front-right 
>     -- corner to the back-left-down corner.
>     twist :: Cube -> Cube
>     twist (Cube u f r b l d) = Cube f r u l d b 
>
>     -- Exchange up and down, front and left, back and right.
>     cubeflip :: Cube -> Cube
>     cubeflip (Cube u f r b l d) = Cube d l b r f u

>     -- Singletons note: this must be polymorphic?!?
>     bind :: [ a ] -> ( a -> [ b ] ) -> [ b ]
>     bind l f = concatMap f l

>     -- Compute all 24 ways to orient a cube.
>     -- Singletons note: monads not supported, so have to rewrite list comprehension
>     -- at the type level in terms of list's bind and return
>     orientations :: Cube -> [ Cube ]
>     orientations c = bind  [c, rot c, rot (rot c), rot (rot (rot c))] $ \c' -> 
>                      bind  [c', twist c', twist (twist c')] $ \c'' -> 
>                      bind  [c'', cubeflip c''] $ \c''' -> [ c''']

>     -- Compute which faces of a cube are visible when placed in a pile.
>     visible :: Cube -> [ Color ]
>     visible (Cube u f r b l d) = [f, r, b, l]

>     -- Two cubes are compatible if they have different colours on every
>     -- visible face.
>  
>     -- Singletons note: (/=) comes directly from deriving Eq
>     -- is it a closed type function?
>     -- however, we need to define compat as a separate function so that 
>     -- we can add the type signature
>     compat :: (Color,Color) -> [Bool]
>     compat (x,x') = [x /= x']
> 
>     compatible :: Cube -> Cube -> Bool
>     compatible c c' = and (bind (zip (visible c) (visible c')) compat)
                        
>     -- Determine whether a cube can be added to pile of cubes, without
>     -- invalidating the solution.
>     allowed :: Cube -> [ Cube ] -> Bool
>     allowed c cs = and (bind cs (\c' -> [compatible c c']))

>     cubes :: [ Cube ]
>     cubes = [ Cube B G W G B R,  
>               Cube W G B W R R, 
>               Cube G W R B R R, 
>               Cube B R G G W W]

>     -- Return a list of all ways of orienting each cube such that no side of
>     --  the pile has two faces the same.
>  
>     solutions :: [Cube] -> [[Cube]]
>     solutions [] = [[]]
>     solutions (c : cs) = bind (solutions cs) $ \cs' ->
>                          bind (orientations c) $ \c' -> 
>                          if allowed c' cs' then [c' : cs'] else []

>     cubeBlue :: Cube
>     cubeBlue = Cube B B B B B B 

>     test1 :: [[Cube]]
>     test1 = solutions [cubeBlue, cubeBlue]

>     test :: [[Cube]]
>     test  = solutions cubes

>          |])

-- SCW: this code takes a *long* time to type check in ghci
-- in fact, perhaps an infinite amount of time; I killed it after about 30 mins.
-- but, how do I get GHC to show the answer?

> {- 


%We first test that solutions correctly finds no solutions for two entirely
%blue cubes:
%
%\begin{verbatim}
%*Main> :type solutions (u::Cons CubeBlue (Cons CubeBlue Nil))
%\end{verbatim}
%\eval{:type solutions (u::Cons CubeBlue (Cons CubeBlue Nil))}

Finally, we can solve the puzzle for the given cubes:

> -- type Cubes = (Cube1 ::: Cube2 ::: Cube3 ::: Cube4 ::: Nil)

%\begin{verbatim}
%*Main> :type solutions (u::Cubes)
%\end{verbatim}
%\eval{:type solutions (u::Cubes)}

\begin{verbatim}
*Main> :type solutions (u::Cubes)
\end{verbatim}

< solutions (u::Cubes) ::
< (:::)   ((:::) (Cube G B B R W G)  ((:::) (Cube R G R W B W)
<         ((:::) (Cube R W G B R R)  ((:::) (Cube W R W G G B) Nil))))
< ((:::)  ((:::) (Cube G B B W R G)  ((:::) (Cube W R G B W R)
<         ((:::) (Cube R G W R B R)  ((:::) (Cube B W R G G W) Nil))))
< ((:::)  ((:::) (Cube G W B B R G)  ((:::) (Cube R B G R W W)
<         ((:::) (Cube R R W G B R)  ((:::) (Cube W G R W G B) Nil))))
< ((:::)  ((:::) (Cube G R B B W G)  ((:::) (Cube W W R G B R)
<         ((:::) (Cube R B G W R R)  ((:::) (Cube B G W R G W) Nil))))
< ((:::)  ((:::) (Cube G R W B B G)  ((:::) (Cube R W B G R W)
<         ((:::) (Cube R B R W G R)  ((:::) (Cube W G G R W B) Nil))))
< ((:::)  ((:::) (Cube G W R B B G)  ((:::) (Cube W B W R G R)
<         ((:::) (Cube R R B G W R)  ((:::) (Cube B G G W R W) Nil))))
< ((:::)  ((:::) (Cube G B R W B G)  ((:::) (Cube R R W B G W)
<         ((:::) (Cube R G B R W R)  ((:::) (Cube W W G G R B) Nil))))
< ((:::)  ((:::) (Cube G B W R B G)  ((:::) (Cube W G B W R R)
<         ((:::) (Cube R W R B G R)  ((:::) (Cube B R G G W W) Nil))))
< Nil)))))))


Changing the order of backtracking steps changes the order of solutions.
For comparison, here is the solution generated by the pure Haskell version:

\begin{verbatim}
[["GBWRBG","WGBWRR","RWRBGR","BRGGWW"],
 ["GBRWBG","RRWBGW","RGBRWR","WWGGRB"],
 ["GWRBBG","WBWRGR","RRBGWR","BGGWRW"],
 ["GBBRWG","RGRWBW","RWGBRR","WRWGGB"],
 ["GRBBWG","WWRGBR","RBGWRR","BGWRGW"],
 ["GWBBRG","RBGRWW","RRWGBR","WGRWGB"],
 ["GBBWRG","WRGBWR","RGWRBR","BWRGGW"],
 ["GRWBBG","RWBGRW","RBRWGR","WGGRWB"]]
\end{verbatim}

> -}