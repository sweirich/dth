> {-# LANGUAGE TypeOperators, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, UndecidableInstances #-}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Type-Level Instant Insanity
%
% Conrad Parker <conrad@metadecks.org>, February 2007
%
% This file is literate Haskell.

\documentclass{tmr}
\usepackage{amsmath}
\usepackage{xspace}

% Processing instructions for lhs2TeX
%include polycode.fmt
%options ghci -fglasgow-exts -fallow-undecidable-instances

% LaTeX macros
\newcommand\HTS{the Haskell Type System\xspace}

\def\boldroman#1{\mbox{\boldmath $\mathrm{#1}$}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Type-Level Instant Insanity}
\author{Conrad Parker\email{conrad@@dl.kuis.kyoto-u.ac.jp}}
\begin{document}

%\maketitle

\begin{introduction}
We illustrate some of the techniques used to perform computations in \HTS
by presenting a complete type-level program.
Programming at this level is often considered an obscure art with little
practical value, but it need not be so.
We tame this magic for the purpose of practical Haskell programming.
\end{introduction}

\section{Overview}

This article discusses an implementation of Instant Insanity, an appropriately
named puzzle game. We will first familiarize ourselves with a straightforward
Haskell solution to the puzzle, and then translate that solution so
that it is evaluated by \HTS at compile time.
By discussing the implementation of a complete solution to a problem, we
necessarily provide more than just the flavour of programming in \HTS.

Rather than simply demonstrating clever tricks, we progressively introduce
useful type-level programming features.
We introduce constructs similar to the functions, lists, maps and filters of
conventional functional programming, and in so doing make clear the basic
techniques required to construct programs in this manner.
Only after building an understanding of the syntactical oddities and
transformations involved in programming in \HTS do we consider the practical
aspects of using these techniques in conventional Haskell programming.

Familiarity with the syntax of \HTS is a prerequisite for understanding the
details of general Haskell programming. What better way to build familiarity
with something than to hack it to bits?
Through this tutorial, we hope to show that \HTS is not as scary as it first
seems.



\newpage
\section{Textbook implementation}

In a discussion of problem-solving via back-tracking,
Bird and Wadler~\cite{bird-wadler} introduce the following puzzle,
\emph{Instant Insanity}:

\begin{quotation} \noindent
It consists of four cubes, with faces coloured blue, green, red or white.
The problem is to arrange the cubes in a vertical pile such that each
visible column of faces contains four distinct colours.
\end{quotation}

\noindent
The solution provided in Listing~\ref{BW-solution} stacks the cubes
one at a time, trying each possible orientation of each cube.

%When I first read it
%% (about a week ago while I was learning Haskell LOLZ!)
%I was quite inspired by its elegance:

\begin{listing}
\begin{verbatim}
cubes = ["BGWGBR", "WGBWRR", "GWRBRR", "BRGGWW"]

-- Rotate a cube 90 degrees over its Z-axis, leaving up and down in place.
rot [u, f, r, b, l, d] = [u, r, b, l, f, d]

-- Twist a cube around the axis running from the upper-front-right 
-- corner to the back-left-down corner.
twist [u, f, r, b, l, d] = [f, r, u, l, d, b]

-- Exchange up and down, front and left, back and right.
flip [u, f, r, b, l, d] = [d, l, b, r, f, u]

-- Compute all 24 ways to orient a cube.
orientations c = 
  [c''' | c' <- [c, rot c, rot (rot c), rot (rot (rot c))],
          c'' <- [c', twist c', twist (twist c')],
          c''' <- [c'', flip c'']]

-- Compute which faces of a cube are visible when placed in a pile.
visible [u, f, r, b, l, d] = [f, r, b, l]

-- Two cubes are compatible if they have different colours on every
-- visible face.
compatible c c' = and [x /= x' | (x, x') <- zip (visible c) (visible c')]

-- Determine whether a cube can be added to pile of cubes, without
-- invalidating the solution.
allowed c cs = and [compatible c c' | c' <- cs]

-- Return a list of all ways of orienting each cube such that no side of
-- the pile has two faces the same.
solutions [] = [[]]
solutions (c:cs) = [c' : cs' | cs' <- solutions cs,
                               c' <- orientations c,
                               allowed c' cs']

main = print $ solutions cubes
\end{verbatim}
\caption{The Bird-Wadler solution to Instant Insanity}
\label{BW-solution}
\end{listing}

Our task is to translate this solution into \HTS.

\section{Type-Level Implementation}

The Haskell Type System is a completely symbolic language with very few amenities.
You are swimming in a sea of atomic constants, like \boldroman{X}.
These aren't numeric constants; they do not hold a value. They simply exist,
and all you can do is create relations between them. If you want features like
numbers and arithmetic, or even boolean logic, then you have to create them yourself.

In order to discuss our implementation, we will treat \HTS as a programming
system in its own right. Although the keywords such as |data| and |class| are
named for their purpose in Haskell, when introducing them we will ignore that
purpose and provide an alternative interpretation within \HTS. Only after completing the
implementation of Instant Insanity will we relate these concepts back to
conventional Haskell programming.  

Of course, \HTS wasn't explicitly designed for programming, and there are some
limitations which we'll cover later. But for now, let's jump right in!

\subsection{Type system features}

This tutorial uses the Haskell98 type system extended with multi-parameter
type-classes and undecidable instances.
We need to enable some GHC extensions to play with this type-hackery:

\begin{verbatim}
$ ghci -fglasgow-exts -fallow-undecidable-instances
\end{verbatim}

\noindent
These are included in your GHC; you just need to pass the options to
enable them, as they were not part of the Haskell98 language specification.

\subsection{Flipping out}

We are going to declare new functions called |all|, |flip|, |map| and
|filter|, so we hide the versions in Prelude.

> import Prelude hiding (all, flip, map, filter)

\subsection{|undefined| (Bottom)}

As we are working in the type system we don't actually care about the values
of any of our variables, only their types. There is one special value which
is a member of every type (i.e.~it can be ``cast'' as any type we choose). For
historical reasons it is called \emph{bottom}, and in Haskell it is written
\boldroman{undefined}.
When it is typeset here, it looks like this: |undefined|.

For example:
\begin{verbatim}
*Main> :type undefined::Int
\end{verbatim}
\eval{:t undefined:: Int}
\bigskip\\
\noindent
This simply confirms that the type of the value |undefined::Int| is |Int|.

> u = undefined

To shorten expressions later in this article, we have abbreviated
\boldroman{undefined} (|undefined|) to the variable |u|.
This is often convenient when programming in \HTS.

\subsection{Simple types}

Ok, let's get started.

We note that there are four possible colours. Rather than using arbitrary
characters to represent colours, we make some type-safe definitions.
% Using 'strict' here is a bit misleading...
% Rather than using arbitrary lists as the data structure to represent a cube,
% we make a strictly defined |Cube|.

In this problem, the colours of the faces of cubes are \emph{atomic}. They
cannot be divided any further, and it is irrelevant to the problem to define
them in terms of any other values. The puzzle is no easier if the red faces
are pink instead.

In \HTS, we use the keyword |data| to introduce atomic constants:

> data R  -- Red
> data G  -- Green
> data B  -- Blue
> data W  -- White

These constants are concrete types, which means that it is possible to
instantiate variables in these types. However, as we have not given these
types any constructors, the only valid value for each is |undefined|.
We use them to represent atomic constants in \HTS.

We can check that |undefined| is a valid value of type |R|:

\begin{verbatim}
*Main> :type undefined::R
\end{verbatim}
\eval{:type undefined::R}

\subsection{Parameterized types}

A cube is a thing that can have six faces. In \HTS, we use the keyword
|data| to introduce such a thing:

> data Cube u f r b l d

Wait a minute -- didn't we just use the keyword |data| to introduce atomic
constants? Yes, and |Cube| is also atomic. That is to say, the concept of
\emph{a thing that can have six faces} is atomic, in the context of this
puzzle. No matter how big your hammer is or how frustrated you are, it's not
within the rules of the puzzle to break down a cube into something with
more, or fewer, faces.

So, |R|, |G|, |B|, |W| and |Cube| are all atomic, but they are different
\emph{kinds} of thing.

\begin{verbatim}
*Main> :kind R
\end{verbatim}
\eval{:kind R}

\begin{verbatim}
*Main> :kind Cube
\end{verbatim}
\eval{:kind Cube}
\bigskip\\

In \HTS, the word \emph{kind} is used to describe the structure of a type,
and types must be of the same kind in order to be used in the same way.

Whereas |R| is a concrete type that we could instantiate variables in,
|Cube| is not:
\begin{verbatim}
*Main> :type undefined :: Cube
<interactive>:1:13:
    Kind error: `Cube' is not applied to enough type arguments
    In an expression type signature: Cube
    In the expression: undefined :: Cube
\end{verbatim}

The |Cube| type needs to be applied to \emph{type arguments}, namely
|u f r b l d|.  If we substitute concrete types for these arguments,
the result is a concrete type. So, one way to think about |Cube| is
that it is like a function, but at the type level: it takes
\emph{types} as arguments and returns \emph{types}.  We say that
|Cube| is \emph{parameterized} over the type arguments |u f r b l
d|.

Now we can use the types we prepared earlier, |R|, |G|, |B|, |W|, as
type arguments to the type-level function |Cube| to produce concrete types:

\begin{verbatim}
*Main> :type undefined :: Cube R R R R R R  -- a red cube
\end{verbatim}
\eval{:type undefined :: Cube R R R R R R}

\begin{verbatim}
*Main> :type undefined :: Cube R G B R G B  -- a colourful cube
\end{verbatim}
\eval{:type undefined :: Cube R G B R G B}

\begin{verbatim}
*Main> :type undefined :: Cube B W G G R G  -- another cube
\end{verbatim}
\eval{:type undefined :: Cube B W G G R G}

\subsection{Type aliases}

Now we can define the actual cubes in our puzzle as ``outputs'' of the
type function |Cube|, and in order to write clear code (in \HTS) we will
create some handy aliases.
In \HTS, we use the keyword |type| to introduce type aliases:

A completely red cube:

> type CubeRed = Cube R R R R R R

A completely blue cube:

> type CubeBlue = Cube B B B B B B

The cubes available in the problem at hand:

\begin{verbatim}
cubes = ["BGWGBR", "WGBWRR", "GWRBRR", "BRGGWW"]
\end{verbatim}

> type Cube1 = Cube B G W G B R
> type Cube2 = Cube W G B W R R
> type Cube3 = Cube G W R B R R
> type Cube4 = Cube B R G G W W

\begin{verbatim}
*Main> :kind Cube1
\end{verbatim}
\eval{:kind Cube1}

We see that |Cube1| has the same \emph{kind} as the color red, |R|, has.
And indeed, |Cube1| is a concrete type:

\begin{verbatim}
*Main> :type undefined::Cube1
\end{verbatim}
\eval{:type undefined::Cube1}

\subsection{Multi-parameter type classes}

We would like to define the following transformations on |Cube|s:

\begin{verbatim}
rot [u, f, r, b, l, d] = [u, r, b, l, f, d]
twist [u, f, r, b, l, d] = [f, r, u, l, d, b]
flip [u, f, r, b, l, d] = [d, l, b, r, f, u]
\end{verbatim}

\noindent
In \HTS, we use the keyword |class| to introduce functions. At first, we
will simply introduce a collection of plain Haskell functions. These are
grouped under the parameterized type class |Transforms|:

> class Transforms u f r b l d where
>   rot   :: Cube u f r b l d -> Cube u r b l f d
>   twist :: Cube u f r b l d -> Cube f r u l d b
>   flip  :: Cube u f r b l d -> Cube d l b r f u

This collection of declarations defines an interface, and that
interface consists of three functions |rot|, |twist| and |flip|.
For example, |rot| takes a |Cube| as input, and outputs a different type
of |Cube|. The exact types of these |Cube|s are related to the class
parameters.

Two different substitutions of the |class| parameters would define different
interfaces, as the resulting types of the functions |rot|, |twist| and |flip|
would be different. Hence |Transforms| is actually a class constructor --
we can use it to generate new classes, but it is not itself a concrete class
definition.
Programming in \HTS, we are only interested in the types of these functions,
which are dictated by the |class| definition. Accordingly, we don't need to
specify anything about their implementation when we create an |instance|; we
can simply declare the functions to be |undefined|.

%multi-parameter type classes are enabled by the GHC option
%\tt-fglasgow-exts\rm.

For example, we could create an instance of |Transforms| which applies only
if all six parameters (faces of cubes) are green:

> instance Transforms G G G G G G where
>  rot = undefined
>  twist = undefined
>  flip = undefined

%It is for this reason that we pass the option
%\tt-fallow-undecidable-instances\rm{} to GHC.

However, there is no need to instantiate |Transforms| for every
possible combination of faces. We can fill in any or all parameters with
variables, which can represent any concrete type (of \emph{kind *}):

> instance Transforms u f r b l d where
>   rot   = undefined
>   twist = undefined
>   flip  = undefined

We are now able to evaluate some simple type transformations, such as:
\begin{verbatim}
*Main> :type              rot (undefined::Cube1)
\end{verbatim}
\eval{:type               rot (undefined::Cube1)}

\begin{verbatim}
*Main> :type        flip (rot (undefined::Cube1))
\end{verbatim}
\eval{:type         flip (rot (undefined::Cube1))}

\begin{verbatim}
*Main> :type twist (flip (rot (undefined::Cube1)))
\end{verbatim}
\eval{:type  twist (flip (rot (undefined::Cube1)))}
\bigskip\\
You can see that we can already perform some basic computations, entirely
in the type system.

Now, do you take the red cube, or the blue cube?

\subsection{Functional Dependencies}

So far we have seen how to construct simple types, and perform type
transformations that transform a parameterized type into a
differently parameterized type.

For this puzzle we will need some boolean algebra, so let's create it.
First we make the truth values:

> data True
> data False

The first boolean function we will need is |And| that relates three
values: two inputs and one output. We express the fact that the output |b| is
dependent on the two inputs |b1|, |b2| by adding the dependency annotation
|b1 b2 -> b|. We use a vertical bar to append this dependency annotation:

> class And b1 b2 b | b1 b2 -> b where
>   and :: b1 -> b2 -> b

We can define |And| by simply listing out its complete truth table:

> instance And True  True  True    where and = undefined
> instance And True  False False   where and = undefined
> instance And False True  False   where and = undefined
> instance And False False False   where and = undefined

When using functional dependencies in this way, we are doing logic
programming in \HTS, using |class| to introduce type-level functions and
using the last class parameter as the ``output.''

\subsection{Lists}

We can define lists in the type system using the following atoms:

> data Nil
> data Cons x xs

The data type |Nil| represents the empty list; the |Cons| data type
is used to append an element to a list. With this syntax, |Cons x
Nil| denotes a list containing only one element; we
can use |Cons| multiple times to build longer lists. However,
this quickly becomes difficult to read. For example, the list |[R,
G, B]| would be represented by \mbox{\tt Cons R (Cons G (Cons B
  Nil))\rm}.

GHC allows us to introduce an alternative infix notation to represent |Cons|.
Type-level infix operators must begin with a colon, so we choose |:::|
and define:

> data x ::: xs
>
> infixr 5 :::

The |infixr 5| here sets the precedence level; we make |:::| bind tightly so
that we do not need to use parentheses inside of lists.
Now the list |[R, G, B]| can be represented more clearly by
\mbox{\tt R ::: G ::: B ::: Nil\rm}.
%and the list of the empty list, |[[]]|, is simply \mbox{\tt Nil ::: Nil\rm}.

\subsection{Type constraints}

We can define recursive functions in \HTS using this representation of lists.
However, in order to do so we must use a
\emph{type constraint}. For a recursively defined list function, we use a type constraint to say that the value for |x ::: xs|
uses a recursive call on |xs|. In general, a type constraint is used to set
preconditions on a function; the given function definition is only valid
when the preconditions are met. By carefully constructing the constraints
you can set up a recursion, or call out to other type-level functions.

For example, to concatenate two arbitrary lists we would write:

> class ListConcat l1 l2 l | l1 l2 -> l where
>   listConcat :: l1 -> l2 -> l

> instance ListConcat Nil l l          where listConcat = undefined
> instance (ListConcat xs ys zs)
>   => ListConcat (x ::: xs) ys (x ::: zs)    where listConcat = undefined

\begin{verbatim}
*Main> :type listConcat (u:: R ::: G ::: B ::: Nil) (u:: W ::: Nil)
\end{verbatim}
\eval{:type listConcat (u:: R ::: G ::: B ::: Nil) (u:: W ::: Nil)}
\bigskip\\
Note that the type constraint, |ListConcat xs ys zs| justifies the
recursive call.

\subsection{Applyable type functions}

For this puzzle, we need to be able to do things like |flip| each of the
cubes in a list, so let's build towards something like |map|, at the type
level. First we will need a way of abstracting the application of a
type-level function, so we introduce a class |Apply|:

> class Apply f a b | f a -> b where
>   apply :: f -> a -> b

The |Apply| class takes a function |f| of one argument, and an argument |a|, and
returns the application of |f| to |a|.

Unfortunately, the functions |rot|, |twist|, and |flip| that we defined earlier
are not declared at the type level; they cannot be passed to our type-level
|Apply|. If we try to do so, we end up with:

\begin{verbatim}
*Main> :type apply rot (u::Cube1)
\end{verbatim}

< apply rot (u::Cube1) :: forall u f r b l d b1.
<   (Transforms u f r b l d,
<   Apply (Cube u f r b l d -> Cube u r b l f d) Cube1 b1) => b1



Instead, we need to create types to name each of these operations:

> data Rotation
> data Twist
> data Flip

We defined |Apply| as a parameterized interface. Let's instantiate it for
each of our transform types:

> instance Apply Rotation (Cube u f r b l d) (Cube u r b l f d)
>   where apply = undefined
> instance Apply Twist    (Cube u f r b l d) (Cube f r u l d b)
>   where apply = undefined
> instance Apply Flip     (Cube u f r b l d) (Cube d l b r f u)
>   where apply = undefined

With all these pieces in place, we can now apply our |Rotation|
function to an example cube:

\begin{verbatim}
*Main> :type apply (u::Rotation) (u::Cube1)
\end{verbatim}
\eval{:type apply (u::Rotation) (u::Cube1)}

\subsection{Map and Filter}

We can now create a function that recurses over a list and |Apply|s another
function |f| to each element. This is the type-level equivalent of
fthe |map| function from the Haskell Prelude.

> class Map f xs zs | f xs -> zs where
>   map :: f -> xs -> zs

If we call |Map| over the empty list, we get an empty list:

> instance Map f Nil Nil               where map = undefined

In the |Cons| case we use two type constraints: one to call |Apply| on
the head element, and one to call |Map| on the tail. The result will simply
join these two values. As we recurse down the list |x:::xs|, we build the
result |z:::zs|:

> instance (Apply f x z, Map f xs zs)
>   => Map f (x ::: xs) (z ::: zs)   where map = undefined

Once again, we show the |map| function in action, by mapping the
|Flip| operation on a list of two cubes:

\begin{verbatim}
*Main> :type map (u::Flip) (u:: Cube1 ::: (Cube2 ::: Nil))
\end{verbatim}
\begin{equation*}
\begin{split}
\Varid{map}&\;(\Varid{u}\mathbin{::}\Conid{Flip})\;(\Varid{u}\mathbin{::}
\Conid{Cube1}\mathbin{:::}(\Conid{Cube2}\mathbin{:::}\Conid{Nil}))\; \mathbin{::}\\
& (\mathbin{:::})\;(\Conid{Cube}\;\Conid{R}\;\Conid{B}\;\Conid{G}\;\Conid{W}\;\Conid{G}\;\Conid{B})\;((\mathbin{:::})\;(\Conid{Cube}\;\Conid{R}\;\Conid{R}\;\Conid{W}\;\Conid{B}\;\Conid{G}\;\Conid{W})\;\Conid{Nil})
\end{split}
\end{equation*}


%\eval{:type map (u::Flip) (u:: Cube1 ::: (Cube2 ::: Nil))}
%\bigskip\\
%LAYOUT%

We can build a |Filter| function similarly:

> class Filter f xs zs | f xs -> zs where
>   filter :: f -> xs -> zs

> instance Filter f Nil Nil            where filter = undefined
> instance (Apply f x b, Filter f xs ys, AppendIf b x ys zs)
>   => Filter f (x ::: xs) zs         where filter = undefined

Here we have introduced a third constraint, |AppendIf|, which takes
a boolean value |b|, a value x, and a list |ys|. The given value |x|
is appended to |ys| only if |b| is |True|, otherwise |ys| is
returned unaltered:

\label{AppendIf}

> class AppendIf b x ys zs | b x ys -> zs
> instance AppendIf True x ys (x ::: ys)
> instance AppendIf False x ys ys

Hence, |Filter| recurses down a list |x:::xs|, and builds the list |zs| by
appending only those values of |x| for which |f x| is |True|.

\subsection{List Comprehensions}

Unfortunately we cannot directly mimic list comprehensions in \HTS,
but we can translate the meaning of a given list comprehension using
the type-level list functions that we have defined.

For example, building a list of the possible orientations of a cube involves
appending a list of the possible applications of |flip|, so we will
need to be able to map over a list and append the original list. The
original list comprehension we are translating was:

\begin{verbatim}
orientations c 
  = [c''' | ...,  c''' <- [c'', flip c'']]
\end{verbatim}

We create a |MapAppend| class in order to compose |Map| and
|ListConcat|:

%\begin{align*}
%  MapAppend F [c, d]& \to [c, d] ++ Map F [c, d]
%                   & \to [c, d, Fc, Fd]
%\end{align*}

> class MapAppend f xs zs | f xs -> zs where
>   mapAppend :: f -> xs -> zs

The |MapAppend| class has two instances:

> instance MapAppend f Nil Nil           where mapAppend = undefined
> instance (Map f xs ys, ListConcat xs ys zs)
>   => MapAppend f xs zs                 where mapAppend = undefined

Further, we will need to be able to do the same twice for |twist|:

\begin{verbatim}
orientations c 
  = [c''' | ...,  c'' <- [c', twist c', twist (twist c')], ...]
\end{verbatim}

%\begin{align*}
%  MapAppend2 F [c, d]& \to [c, d] ++ Map F (MapAppend F [c, d]) \\
%                    & \to [c, d] ++ Map F [c, d, Fc, Fd] \\
%                    & \to [c, d, Fc, Fd, FFc, FFd]
%\end{align*}

> class MapAppend2 f xs zs | f xs -> zs where
>   mapAppend2 :: f -> xs -> zs

> instance MapAppend2 f Nil Nil          where mapAppend2 = undefined
> instance (Map f xs ys, MapAppend f ys ys', ListConcat xs ys' zs)
>   => MapAppend2 f xs zs                where mapAppend2 = undefined

and three times for |rot|:

\begin{verbatim}
orientations c 
  = [c''' | c' <- [c, rot c, rot (rot c), rot (rot (rot c))], ...]
\end{verbatim}

%\begin{align*}
%MapAppend3 F [c,d]& \to [c, d] ++ Map F (MapAppend2 F [c, d]) \\
%                 & \to [c, d] ++ Map F [c, d, Fc, Fd, FFc, FFd] \\
%                 & \to [c, d, Fc, Fd, FFc, FFd, FFFc, FFFd]
%\end{align*}

> class MapAppend3 f xs zs | f xs -> zs where
>   mapAppend3 :: f -> xs -> zs

> instance MapAppend3 f Nil Nil          where mapAppend3 = undefined
> instance (Map f xs ys, MapAppend2 f ys ys', ListConcat xs ys' zs)
>   => MapAppend3 f xs zs                where mapAppend3 = undefined

\subsection{Orientations}

The full list comprehension for generating all possible orientations of a
cube builds upon all combinations of |rot|, |twist| and |flip|:

\begin{verbatim}
orientations c = 
  [c''' | c' <- [c, rot c, rot (rot c), rot (rot (rot c))],
          c'' <- [c', twist c', twist (twist c')],
          c''' <- [c'', flip c'']]
\end{verbatim}

\noindent
We will implement Orientations as an |Apply|able type function. In turn, it
is defined in terms of applications of |Rotation|, |Twist| and |Flip|,
invoked via the various |MapAppend| functions:

> data Orientations
>
> instance (MapAppend Flip (c ::: Nil) fs, MapAppend2 Twist fs ts,
>           MapAppend3 Rotation ts zs)
>   => Apply Orientations c zs
>   where apply = undefined

For any |Cube|, this function generates the 24 possible orientations:

%\begin{verbatim}
%*Main> :type apply (u::Orientations) (u::Cube1)
%\end{verbatim}
%\eval{:type apply (u::Orientations) (u::Cube1)}

\begin{verbatim}
*Main> :type apply (u::Orientations) (u::Cube1)
\end{verbatim}

< apply (u::Orientations) (u::Cube1) ::
<  (:::) (Cube B G W G B R) ((:::) (Cube R B G W G B) 
< ((:::) (Cube G W B B R G) ((:::) (Cube B G R G B W) 
< ((:::) (Cube W B G R G B) ((:::) (Cube G R B B W G)
< ((:::) (Cube B W G B G R) ((:::) (Cube R G W G B B) 
< ((:::) (Cube G B B R W G) ((:::) (Cube B R G B G W) 
< ((:::) (Cube W G R G B B) ((:::) (Cube G B B W R G)
< ((:::) (Cube B G B G W R) ((:::) (Cube R W G B G B) 
< ((:::) (Cube G B R W B G) ((:::) (Cube B G B G R W) 
< ((:::) (Cube W R G B G B) ((:::) (Cube G B W R B G)
< ((:::) (Cube B B G W G R) ((:::) (Cube R G B G W B) 
< ((:::) (Cube G R W B B G) ((:::) (Cube B B G R G W) 
< ((:::) (Cube W G B G R B) ((:::) (Cube G W R B B G)
< Nil)))))))))))))))))))))))

\subsection{Stacking Cubes}

%Now we start to get more of a flavour of how type constraints are used as
%combinators when programming in \HTS.

Given two cubes |(Cube u1 f1 r1 b1 l1 d1)| |(Cube u2 f2 r2 b2 l2
d2)|, we now want to check that none of the corresponding visible
faces are the same colour: the front sides |f1| and |f2| are not
equal, and the right sides |r1| and |r2| are not equal, and so
on. In short, we want to determine whether:

\[(|f1| \neq |f2|) \wedge (|r1| \neq |r2|) \wedge (|b1| \neq |b2|) \wedge (|l1| \neq |l2|)\]

In order to do this, we will first need to define the  $\neq$ relation
for all four colours. Given two cubes, we can then apply this relations
to each pair of visible faces to get four boolean values. To check
that all of these are True, we will construct a list of those four values,
and then write a generic list function to check if all elements of a list
are True.

\subsection{Not Equal}

To define the $\neq$ relation, we introduce a new class:

> class NE x y b | x y -> b where
>   ne :: x -> y -> b

We are going to use |NE| to instantiate type comparisons for the faces of
our cube. Recall that these faces are of the atomic types |R|, |G|, |B|, |W|,
and we have not yet defined any relation between these atomic types.

> instance NE R R False   where ne = undefined
> instance NE R G True    where ne = undefined
> instance NE R B True    where ne = undefined
> instance NE R W True    where ne = undefined
> instance NE G R True    where ne = undefined
> instance NE G G False   where ne = undefined
> instance NE G B True    where ne = undefined
> instance NE G W True    where ne = undefined
> instance NE B R True    where ne = undefined
> instance NE B G True    where ne = undefined
> instance NE B B False   where ne = undefined
> instance NE B W True    where ne = undefined
> instance NE W R True    where ne = undefined
> instance NE W G True    where ne = undefined
> instance NE W B True    where ne = undefined
> instance NE W W False   where ne = undefined

Note that our class |NE| is very different from the class |Eq| defined in
Haskell:

\begin{verbatim}
*Main> :info Eq
class Eq a where
  (==) :: a -> a -> Bool
  (/=) :: a -> a -> Bool
        -- Imported from GHC.Base
...
\end{verbatim}

Whereas |Eq| is used to describe types for which it is possible to compare
\emph{instances} for equality, |NE| directly compares types.

\par\break
\subsection{All}

Now, we define a function |all| to check if all elements of a list
are True.

> class All l b | l -> b where
>   all :: l -> b
>
> instance               All Nil True                where all = undefined
> instance               All (False ::: xs) False   where all = undefined
> instance (All xs b) => All (True ::: xs) b        where all = undefined

The constraint |(All xs b) => All (True ::: xs) b|
says that the output |b| of |All (True ::: xs) b| has the same value as
the output |b| of |All xs b|; ie. that if the head of the list is |True|,
then the value of |All| is determined by the rest of the list.

Once again, we can check that |all| behaves as we expect:

\begin{verbatim}
*Main> :type all (u::Nil)
\end{verbatim}
\eval{:type all (u::Nil)}

\begin{verbatim}
*Main> :type all (u:: False ::: Nil)
\end{verbatim}
\eval{:type all (u:: False ::: Nil)}

\begin{verbatim}
*Main> :type all (u:: True ::: False ::: Nil)
\end{verbatim}
\eval{:type all (u:: True ::: False ::: Nil)}

\begin{verbatim}
*Main> :type all (u:: True ::: True ::: True ::: Nil)
\end{verbatim}
\eval{:type all (u:: True ::: True ::: True ::: Nil)}

\subsection{Compatible}

We can now write the compatibility check in the \HTS, that
corresponds to the original \texttt{compatible} function:

\begin{verbatim}
visible [u, f, r, b, l, d] = [f, r, b, l]

compatible c c' = 
  and [x /= x' | (x, x') <- zip (visible c) (visible c')]
\end{verbatim}

\noindent
We introduce a new |Compatible| class. It should check that no
corresponding visible faces are the same colour.

> class Compatible c1 c2 b | c1 c2 -> b where
>   compatible :: c1 -> c2 -> b

We will do this by evaluating the relationship |NE| for each pair of
corresponding visible faces, giving four booleans |bF|, |bR|, |bB|, and |bL|.
Whether or not the two |Cube|s are
compatible is then determined by |All (bF ::: bR ::: bB ::: bL ::: Nil)|.

> instance (NE f1 f2 bF, NE r1 r2 bR, NE b1 b2 bB, NE l1 l2 bL,
>           All (bF ::: bR ::: bB ::: bL ::: Nil) b)
>   => Compatible (Cube u1 f1 r1 b1 l1 d1) (Cube u2 f2 r2 b2 l2 d2) b
>  where compatible = undefined

A completely red cube is obviously compatible with a completely blue cube:

\begin{verbatim}
*Main> :type compatible (u::Cube R R R R R R) (u::Cube B B B B B B)
\end{verbatim}
\eval{:type compatible (u::Cube R R R R R R) (u::Cube B B B B B B)}
\bigskip\\
whereas if we paint their front sides green then they are no longer
compatible:

\begin{verbatim}
*Main> :type compatible (u::Cube R R G R R R) (u::Cube B B G B B B)
\end{verbatim}
\eval{:type compatible (u::Cube R R G R R R) (u::Cube B B G B B B)}

\subsection{Allowed}

The above |Compatible| class checks a cube for compatibility with another
single cube. In the puzzle, a cube needs to be compatible with all the other
cubes in the pile.

\begin{verbatim}
allowed c cs = and [compatible c c' | c' <- cs]
\end{verbatim}

\noindent
We write a class to check for compatibility with each of a list of cubes.
This class generalizes |Compatible| over lists:

> class Allowed c cs b | c cs -> b where
>   allowed :: c -> cs -> b
> instance Allowed c Nil True where allowed = undefined
>
> instance (Compatible c y b1, Allowed c ys b2, And b1 b2 b)
>   => Allowed c (y ::: ys) b where allowed = undefined

%\begin{verbatim}
%*Main> :type allowed (u::CubeRed) (u:: CubeRed ::: Nil)
%\end{verbatim}
%\eval{:type allowed (u::CubeRed) (u:: CubeRed ::: Nil)}

%\begin{verbatim}
%*Main> :type allowed (u::CubeRed) (u:: CubeBlue ::: Nil)
%\end{verbatim}
%\eval{:type allowed (u::CubeRed) (u:: CubeBlue ::: Nil)}

Sure enough, we can now test the |allowed| function:

\begin{verbatim}
*Main> :type allowed (u::CubeRed) (u:: CubeBlue ::: CubeRed ::: Nil)
\end{verbatim}
\eval{:type allowed (u::CubeRed) (u:: CubeBlue ::: CubeRed ::: Nil)}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{Solution}

We are now ready to tackle the implementation of |solutions|:

\begin{verbatim}
solutions [] = [[]]
solutions (c:cs) = [c' : cs' | cs' <- solutions cs,
                               c' <- orientations c,
                               allowed c' cs']
\end{verbatim}

\noindent
We will create a corresponding class |Solutions|, which takes a list of
|Cube|s as input, and returns a list of possible solutions, where each solution is a list
of |Cube|s in allowed orientations.

> class Solutions cs ss | cs -> ss where
>   solutions :: cs -> ss

The base case for |Solutions| is the list containing the empty list, |[[]]|, which we
represent by |Nil ::: Nil|. The recursive step considers all orientations of
the topmost |Cube|:

> instance Solutions Nil (Nil ::: Nil)
>   where solutions = undefined
> instance (Solutions cs sols, Apply Orientations c os,
>           AllowedCombinations os sols zs)
>   => Solutions (c ::: cs) zs
>   where solutions = undefined

The |AllowedCombinations| class recurses across the solutions so far, checking each
against the given orientations.

> class AllowedCombinations os sols zs | os sols -> zs
> instance AllowedCombinations os Nil Nil
> instance (AllowedCombinations os sols as, MatchingOrientations os s bs,
>           ListConcat as bs zs)
>   => AllowedCombinations os (s ::: sols) zs

Finally, the |MatchingOrientations| class recurses across the orientations of the new cube, checking
each against a particular solution |sol|.

> class MatchingOrientations os sol zs | os sol -> zs
> instance MatchingOrientations Nil sol Nil
> instance (MatchingOrientations os sol as,
>           Allowed o sol b, AppendIf b (o ::: sol) as zs)
>   => MatchingOrientations (o ::: os) sol zs

If the orientation is allowed, then the combination |o| is added to
the existing solutions |sol|, by forming the type |o ::: sol|.

Note that we have not been able to make use of the previously defined
|Filter| because it requires a one-argument |Apply|able function. As we
lack currying, we are unable to construct such a function on the fly.
However, we can make use of the more generic |AppendIf| (defined on page
\pageref{AppendIf}) to handle the filtering constraint.

%We first test that solutions correctly finds no solutions for two entirely
%blue cubes:
%
%\begin{verbatim}
%*Main> :type solutions (u::Cons CubeBlue (Cons CubeBlue Nil))
%\end{verbatim}
%\eval{:type solutions (u::Cons CubeBlue (Cons CubeBlue Nil))}

Finally, we can solve the puzzle for the given cubes:

> type Cubes = (Cube1 ::: Cube2 ::: Cube3 ::: Cube4 ::: Nil)

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


\section{Using types in Haskell}
\label{Haskell}

Now that we've seen how to use \HTS to solve a puzzle, let's review what it
was actually designed for: ensuring that your programs make sense. The
syntax of \HTS lets you tell the compiler what your program must or must not
do, while also giving you enough flexibility to implement useful shared and
extensible interfaces.
%It is more powerful than the na\"ive view of a type system as as simply some
%"metadata attached to values".

Let's review the features of \HTS from a Haskell programming perspective.

\subsection{Keywords}

%\emph{|undefined| (Bottom)

The most straightforward way to define your own types is with the keyword
\emph{data}. You can use this to define simple types or to introduce
structured records.

\emph{Type aliases} are a handy form of abbreviation; for example the Prelude
provides |type Rational = Ratio Integer|, to make code that manipulates
rational numbers easier to read and write; under the hood, code that works
with |Rational|s is actually dealing with the |Ratio Integer| type.
This is different from |newtype| which declares an entirely new type that
cannot be used in the same contexts.

\emph{Parameterized type-classes}, introduced by the keyword |class|, are
used to provide common interfaces for existing types. These interfaces are
composed of \emph{methods}, which may be functions or constant values. An
|instance| of a type-class simply provides an implementation of the class
methods. You can also provide default methods in a |class| declaration,
which are used unless overridden in an |instance|.  

\subsection{Haskell98 features}

\emph{Parameterized types} are used to wrap types in general interfaces.
You use this technique when you want to ensure that you can't accidentally
use two variants of a parameterized type in the same call; \HTS ensures that
they are incompatible. You can also use this to create tainted versions of
existing types, in order to quarantine data that has come from untrusted
sources.

\emph{Type constraints}, introduced by |=>|, are often used to provide
sensible pre-conditions.
For example, the Haskell Prelude declares the type-class |Real| with the
constraint \mbox{|class (Num a, Ord a) => Real a|}, which expresses that you
can only try to implement the interface for |Real| for types which are
numeric and have an ordering; \HTS first ensures that that you have already
implemented |Num| and |Ord|.

When reading Haskell code, you will notice that type constraints can occur
in data and function definitions, not just in class instances.

Type constraints can also be used more creatively to encode post-conditions,
if these conditions are encoded into the function types.
For example, Kyselyov's Dependently Typed Append~\cite{oleg-dtype-append},
implements a list append with the assurance that the length of the output
list is the sum of the lengths of the input list.

\subsection{Extensions}

Some of the language features used in this tutorial are not part of the
Haskell98 specification, but are widely supported by Haskell compilers.
When building with GHC, these extensions can be enabled with the options
\tt\mbox{-fglasgow-exts}\rm~\cite{ghc-exts}.

The simplest of these extensions is the use of |data| types with no
constructors, such as

> data Red
> data Blue

As these types can only contain the value |undefined|, they are not much use
on their own. However, they can be used to construct other, more complex
types, and can be used as \emph{phantom types}~\cite{wiki-phantom}.

\emph{Multi-parameter type-classes} allow you to specify an interface which
can behave differently for each combination of ``input'' types. This is usually
used together with \emph{functional dependencies}~\cite{hallgren}, which make
it easier for the type-checker to infer type relationships, and make the
code easier to read. We enable the GHC option
\tt\mbox{-fundecidable-instances}\rm~\cite{ghc-exts}
to allow general recursion at the type-level.

GHC allows empty class declarations (with a warning), so the definitions in
this tutorial which specify |where something = undefined| are actually
unnecessary. However, we left them in in order to retain some semblance of
connection to conventional Haskell programming.

\section{Conclusion}

We have seen how to use \HTS as a programming language to solve a given
problem. Of course, its real purpose is not to solve problems directly, but
to express constraints on the behaviour of a system in Haskell. The type
level features we have seen allow us to express the pre- and post-conditions
of functions. By expressing these constraints in the type system, the compiler
statically verifies that the produced code operates as required, without
the need for run-time checks.

We reiterate that familiarity with the syntax of \HTS is a prerequisite for
general Haskell programming.
With a solid understanding of type and type-class parameterization, type
constraints and dependencies, you should be well on your way to understanding
the interfaces of interesting and useful types.

This tutorial introduced the most widely used type-level features in general
Haskell programming, extending Haskell98 with multi-parameter
type-classes and undecidable instances.
If you wish to go further with type-level programming there are many
interesting extensions to \HTS~\cite{ghc-exts}, and more advanced type systems
research explores topics like program verification and proof carrying code.
~\cite{wiki-types, oleg-types}.

%What better way to build familiarity with something than to hack it to bits?
Please enjoy hacking in \HTS, and wield it wisely in your program designs.

\section{Acknowledgements}

Thanks to Simon Horman, Patryk Zadarnowski, Shane Stephens and Wouter
Swierstra for their feedback on drafts of this article.

\section{About the author}

Conrad Parker (kfish on \#haskell) is a PhD student at Kyoto University.
Originally from Sydney, he graduated from UNSW with degrees in
Mathematics and Computer Engineering.
Hobbies include computer music and Japanese language.

\bibliography{instant-insanity}

\end{document}