# bitstream: bit stream accumulate / dump

Need a datatype that you can stuff bits into, and then later
extract bits out of, in arbitrary-length chunks.

For example

    make a bs
    0010 -> bs
    0001000001 -> bs
    take 6 from bs (-> 001000)
    take 7 from bs (-> 0100000)
    take 1 from bs (-> 1)
    bs is empty (true)

## Questions

* Should the bitstream be arbitrary (growing) size,
  or should it have a maximum capacity?

* What should the datatypes passed in and out look like?

* What methods should I have?

* How much do I care about performance?

## Hints

* Look to implement standard Rust datatype methods such as
  `len()`, `is_empty()`, etc.
  
* Use `Option` and `Result` wisely.

* If you want, use "const generics". But probably a `Vec` is
  easier.

* Implement sensible traits: for example `Debug`, `Clone`.

* You may want an `Error` type.
