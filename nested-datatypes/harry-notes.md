# Harry's Notes on Nested.lhs

- I wonder if the nested data-type angle is the right one? From my perspective this is a really nice
  exploration of how to constrain a data structure, but I think if you wanted it to be "about"
  nested data-types we'd need a couple more examples of useful ones.
- The part about FTree seems like it's either out of order or needs more explanation. You presented
  NTree and DTree, and I thought we'd start trying to decide which was better---instead we start
  talking about FTree. I think the main problem is that since we can't infer the height, FTree is
  just much more cumbersome to use than the other options. Maybe you can explain a bit about other
  places this approach is used, and why it works well in those cases?
- Probably rename the ITree example. Wouldn't want angry letters from certain fans of co-inductive
  free monads.
- I like the discussion about polymorphic recursion, you could potentially say even more there. In
  general that's something that I definitely haven't read/seen enough about.
- You could make this a little bit more beginner-friendly by expanding on datatype promotion,
  singletons etc.
