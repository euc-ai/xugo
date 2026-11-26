# word_bits — the reading face of the term-level word

Position `i` of a value `x` is `word_bit(i, x) ⇔ nat_odd(div(x, 2^i))`.
It is a fact about the number alone; a width enters when a statement
bounds the value or truncates the positions it reads.

The chapter develops the digit table (`bit_value` and its parity
reading), the bit tables of zero, one and powers of two (`BitPowTwo`),
bits of a remainder or quotient, the top-bit threshold, vanishing of
low and high windows, and bounded and unbounded bit extensionality.
`BitsEqAll` turns agreement at every position into equality of values.
The exponent bounds come from `nat_order.LessThanPowTwoSelf` and
`nat_order.PowTwoMonotone`.

The common finite-window construction is `word_of_bits`. Its range
law `WordOfBitsBound` and reading law `BitOfBitSet` are proved here.
The unary and binary bitwise windows are this construction at the
position predicates selected by their boolean operations
(`BitwiseUnaryAsBits`, `BitwiseBinaryAsBits`). Their range and
projection laws then follow from the common construction.

The operator interfaces are `BitOfAnd`, `BitOfOr` and `BitOfXor`,
which read the width-free binary operations, and `BitNot`, which reads
the complement inside its explicit width. Consumers of these operators
can work with their bit tables directly.

The constants are minted in `words/machine_word`. The equational algebra
lives in `words/bitwise_algebra`, the arithmetic interpretation in
`words/bit_arith`, the finite-set and weighted-sum interpretation in
`words/bit_set`, and the signed interpretation in `words/signed_word`.
