What are Dependent Types and what are they good for?

Robin Milner famously introduced us to the idea that "well-typed programs do
not go wrong" and functional programmers have been experiencing the practical
implications of this slogan for the past forty-five years. Milner's type
system and inference algorithm are still in daily use and provide the basis
for the type systems of the ML and Haskell programming languages.

Dependent type systems extend Milner's foundation to more expressive
contexts. Their key feature, that types can express relationships between
program values, enables new safe programs to be well-typed and new "wrong"
programs to be ruled out. New programming languages such as Idris and Agda,
and new extensions to Haskell have adopted these ideas, redefining the the
role of the type checker and the practice of programming.

In this talk, I will provide a gentle introduction to the world of dependent
types: from the success stories that programmers can enjoy today to the
research advances that are coming in future languages.
