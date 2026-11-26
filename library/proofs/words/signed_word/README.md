# signed_word — the two's-complement reading of a term-level word

A word of width `n` here is its unsigned value — an ordinary `num` —
and this chapter reads it SIGNED: a value in the low half of the range
is itself, a value in the high half is itself less the whole range.
`int_of_word` is that reading, landing in ℤ; `word_of_int` is the map back — an
integer's Euclidean remainder at the range, read as a value. The
chapter is the correspondence between them and the bounds each
respects: the reading in terms of the value and the top bit, the
half-open range it never leaves, when two words share a reading, what
survives the round trips in each order, how the reading carries the
ring operations, and the C-semantics limits (`INT_MIN`, `INT_MAX`,
`UINT_MAX`) as ground values.

## The member map

- **ival.go** — the reading itself. Its case form (`IntOfWordByCases`)
  and closed form (`IntOfWordByTopBit`, transposed as `ValByTopBit`); the
  sign law (`TopBitIsNegative`) and the top-bit test in ℤ
  (`TopBitByIntValue`); the half-range window (`IntOfWordBound`) and the
  congruence to the unsigned value (`IntOfWordValCong`); when two words
  share a reading (`EqByIntOfWordCong`, `EqByIntOfWord`) and the reading at zero
  (`IntOfWordZero`, `IntOfWordEqZero`); the ring operations read signed
  (`CongAdd`, `CongSub`, `CongNeg`, `CongMul`) and the complement
  identity (`IntOfWordNot`).
- **iword.go** — the ℤ→word constructor. Its value on embedded
  numbers (`WordOfIntOfNum`), its image — the source's remainder by the
  range (`WordOfIntImage`, the one equation through which every claim
  about the constructor crosses back into ℤ), the congruence of the
  round trip (`IntRoundTripCong`), invariance under the remainder
  (`WordOfIntRem`);
  the correspondence: when two integers build one word
  (`WordOfIntEq`), the two round trips (`WordRoundTrip`,
  `IntRoundTripInRange`) and the Galois test (`IntOfWordEqByWordOfIntInRange`);
  the constructor as a ring map (`WordOfIntSum`, `WordOfIntDiff`,
  `WordOfIntNeg`, `WordOfIntProduct`).
- **limits.go** — the C-semantics limits. INT_MIN's value, word
  form and bit table (`IntMinValue`, `IntMinAsWord`, `IntMinBits`),
  INT_MAX's word form (`IntMaxAsWord`), UINT_MAX's value and bound
  (`UintMaxValue`, `ValLessEqUintMax`); the limits read back
  (`IntOfWordIntMin`, `IntOfWordIntMax`), the two-limit bound on every
  reading (`IntOfWordBetweenLimits`), and the ground readings at the
  window's inner edge (`IntOfWordOne`, `IntOfWordEqMinusOne`).

## The definitional layer (definitions.go)

	int_of_word  : num → num → int    int_of_word(n, x)  = COND(nat_mod(x, 2^n) < 2^(n-1),
	                                                &(nat_mod(x, 2^n)),
	                                                &(nat_mod(x, 2^n)) - int_pow(&2, n))
	word_of_int : num → int → num    word_of_int(n, x) = num_of_int(int_rem(x, int_pow(&2, n)))

`int_of_word` reads its argument through the residue — the same
congruence-preservation the machine_word chapter's arithmetic operations
carry — so the range bound and the congruence laws hold for ALL inputs
and land free of range guards (the sign law keeps its width guard: a
top place needs a positive width to sit in).
`word_of_int` needs no outer reduction: `int_rem` is Euclidean, so its
remainder is already the reduced value.
