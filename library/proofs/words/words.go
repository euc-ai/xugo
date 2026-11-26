// Package words is the aggregator for the machine-word chapters.
//
// A machine word of width n is its unsigned VALUE — an ordinary `num` —
// and the width is an ordinary `num` variable. There is no type of
// words: an operation that needs the width takes it as an argument,
// and reduces mod `2^n` where a type would have bounded the value. So
// a statement quantifies over the width — one theorem where a width
// carried in a type would need one per width — computes with it, and
// keeps only the guards the mathematics asks for.
//
// A word speaks two languages, arithmetic mod `2^n` and the bits of its
// binary expansion, and that double life is what the domain is about:
// every chapter picks one of the two faces, or bridges them.
//
// - machine_word — the definitional substrate, and the value face: the
// arithmetic operations, the bit reader `word_bit`, the set builder
// `word_of_bits` and the bitwise operations are defined here, with the
// value face's own theory — its round trips, congruences and
// quantifier transports, and the ring laws of width-n arithmetic,
// which hold at every width with no range guard because each
// arithmetic operation reads an unreduced input through its residue.
// - word_bits — the reading face: the digit table, positions and
// windows, the window combinators, the operators projected to
// single bits, bit extensionality.
// - bitwise_algebra — the pointwise boolean algebra: the equational laws of
// word_and/word_or/word_xor/word_not, De Morgan, masks, the complement laws.
// - bit_arith — the algebra against arithmetic: sums decomposed over
// the lattice, the carry, order against meet and join, the
// complement as arithmetic.
// - bit_set — a word's places as a set: the set builder, membership,
// the operations as set operations, the builder as a weight sum.
// - signed_word — the two's-complement reading: `int_of_word` takes a value
// to the integer it stands for — itself in the low half of the range,
// itself less the whole range in the high half — and `word_of_int`
// takes an integer back to its remainder at the range; the
// correspondence between the two, the bounds each respects, and how
// the reading carries the ring operations.
//
// The domain sits above `nat_num` and below nothing: a word is a
// number, and its arithmetic is ℕ's modular arithmetic. Where a
// chapter reaches further it is for its own face — a word's places are
// a set, so the builder is defined over `sets` and bit_set reads finite
// sets and Σ over ℕ; the signed reading lands in ℤ, so signed stands on
// `int_num`. The domain is placed by subject rather than by stratum,
// as `cartesian` is — the chapters below it are the substrate its
// constants are defined over, not chapters about words.
package words

import (
	_ "github.com/euc-ai/xugo/library/proofs/words/bit_arith"
	_ "github.com/euc-ai/xugo/library/proofs/words/bit_set"
	_ "github.com/euc-ai/xugo/library/proofs/words/bitwise_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/words/machine_word"
	_ "github.com/euc-ai/xugo/library/proofs/words/signed_word"
	_ "github.com/euc-ai/xugo/library/proofs/words/word_bits"
)
