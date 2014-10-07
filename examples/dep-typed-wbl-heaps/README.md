Weight-biased leftist heaps verified in Haskell using dependent types
=====================================================================

(Note: the upstream repo is located [here]
(https://github.com/jstolarek/dep-typed-wbl-heaps-hs))

This folder contains implementation of weight-biased leftist heap data
structure verified in Haskell using dependent types. This package is
intended to be a tutorial and technology demonstration. It is not
intended to be used in real-world applications (but if you find such a
use please let me know).

Weight-biased leftist heap is a binary tree that satisfies two
invariants:

  1. Priority invariant: priority of every node is higher than
     priority of its children. (This property is true for heaps in
     general).

  2. Rank invariant: for every node size of its left child is not
     smaller than the size of its right child.

These two invariants give us a data structure that provides O(1)
access to element with the highest priority and O(log2 n) insert and
merge operations. See chapter 3 of Chris Okasaki's "Purely Functional
Data Structures" for more discussion.

The main purpose of this implementation is to explain how proofs of
the two above invariants are constructed in Haskell. (The ideas
convey to other languages with dependent types.) You'll find lots of
comments in the source code. I assume that you already have been
exposed to basics of proofs with dependent types. In particular
you should be familiar with:

  * the concept of data-as-evidence as described in "Why Dependent
    Types Matter" paper. All the ideas here are taken from that
    paper

  * singleton types as described in "Dependently Typed Programming
    with Singletons" paper. I don't make heavy use of singletons but
    you should understand why do we need encodings like singleton
    types in Haskell

  * basics of formal reasoning (including refl). See online lecture
    notes for the [Computer Aided Formal Reasoning course by Thorsten
    Altenkirch](http://www.cs.nott.ac.uk/~txa/g53cfr/)

You should begin studying of this repo by getting familiar with
modules in `Basics` directory. Then go to `TwoPassMerge` directory and
begin with `NoProofs` module followed by `RankProof` and
`PriorityProof` (in any order) and finish with `CombinedProofs`. Then
move to `SinglePassMerge` and study the modules in the same order as
earlier. Alternatively, you might want to look at the single-pass
merge variant right after studying the two-pass implementation.

## Requirements and conventions

  * This code has been tested with GHC 7.6.3 and GHC 7.8.3. It only
    depends on `base` library. No other dependencies are required.

  * I'm not relying on anything from `Prelude` except for
    `undefined` function.

  * I'm using GADT syntax for all data types, even if they are
    ordinary ADTs.

  * Whenever I say "See #XYZV" I'm referring to GHC bug report number
    located under address `http://hackage.haskell.org/trac/ghc/ticket/XYZV`.

## License

See LICENSE file in the root of the repository.

## See also

I originally implemented verified weight-biased leftist heap in
Agda. This implementation is available
[here](https://github.com/jstolarek/dep-typed-wbl-heaps).

I also wrote a [companion blog post]
(http://lambda.jstolarek.com/2014/10/weight-biased-leftist-heaps-verified-in-haskell-using-dependent-types/).

## Author

This code was contributed to DTH repo by [Jan Stolarek]
(http://ics.p.lodz.pl/~stolarek) from Politechnika Łódzka,
Łódź, Poland.
