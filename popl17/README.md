Example code to accompany POPL 2017 keynote "The influence of Dependent Types"

The code featured in the talk can be found in `RegexpDependent.hs`. This file
requires GHC 8.0.1 to compile as well as the HEAD implementation of
the [singletons library](https://github.com/goldfirere/singletons).

    Regexp.hs            Non-dependently typed implementation
    RegexpDependent.hs   "Dependently-typed" implementation 
    RegexpTest.hs        unit tests 
    RegexpParser.hs      template haskell-based parser 
    RegexpExample.hs     top-level examples

