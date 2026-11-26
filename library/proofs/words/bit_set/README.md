# bit_set — a word's places as a set

The set builder `word_of_bits` and the membership reading of `word_bit`: what
the builder computes, the bit set at 0 and 1, finiteness, the bitwise
operations as set operations, reading a word back off its place set
(`EqByBitSet`, with the bounded and mask forms), and the builder as a
weight sum (`WordOfBitsAsSum` and the word forms).

The chapter connects the bit representation to finite sets and weighted
sums: `WordOfBitsAsSum` identifies the builder with the sum of the
selected powers of two, and `WordOfBitsAsWordFinite` reduces a finite
set's weight sum to its low window.
