# bit_arith — the boolean algebra against arithmetic

Where the two languages of a word meet on one value: a sum decomposed
as meet plus join (`AddAndOr`), the join as meet plus difference
(`OrAndXor`), the carry named (`AddAndXor`), disjoint sums needing no
reduction (`AddIsOr`/`AddIsXor` and the iff), the order laws of the
lattice (`AndLessEq`/`OrLessEq` and their sharp forms), the all-ones
mask's VALUE, the complement as arithmetic (`ValNot`, `NegOneIsNotZero`,
the complement-in-the-ring laws), and disjunction as the sum of
conjunction and difference (`OrXorGen`).

Reads bits through `words/word_bits` and states values over
`words/machine_word`'s substrate.
