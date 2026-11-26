# bitwise_algebra — the pointwise boolean algebra

The equational laws of `word_and`/`word_or`/`word_xor`/`word_not`: symmetry,
associativity, units, idempotents and refl laws for each operator, De
Morgan (the complement swapping the two lattices), the all-ones mask
against both algebras, the complement laws (`NotNot`, `XorNot`), and
the difference as an equality test (`XorEqZero`).

Every law is proved by reading bits through `words/word_bits`' projections
and closing with bit extensionality — the chapter has no arithmetic
of its own. Where the algebra MEETS arithmetic (a sum as meet plus
join, order against the lattice) is `words/bit_arith`'s subject.

The paired zero and all-ones-mask laws establish one operand order by
bits and obtain the other by symmetry. Complement proofs read the bit
interface through `word_bits.BitNot`.
