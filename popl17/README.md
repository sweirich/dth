Example code to accompany POPL 2017 keynote "The influence of Dependent Types"

The code featured in the talk can be found in `src/RegexpDependent.hs`. These files
require GHC 8.0.1 to compile as well as the HEAD implementation of
the [singletons library](https://github.com/goldfirere/singletons).

    src/RegexpDependent.hs   Dependently-typed implementation 
    src/RegexpTest.hs        Unit tests 
    src/RegexpParser.hs      Template haskell-based parser 
    src/Regexp.hs            Non-dependently typed implementation
    RegexpExample.hs         Top-level example

