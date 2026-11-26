// ival.go — the signed reading: its case form and closed form, the
// sign law it exists to make true, the half-range window it never
// leaves, its congruence to the unsigned value, when two words share a
// reading, the reading at zero, and how the reading carries the ring
// operations and the complement.
//
// Every claim about the reading is settled among the NUMBERS — where
// words/machine_word's bit and residue algebra lives — and carried across
// the embedding, where `int_of_num` preserves order, sums and powers:
// `int_of_word` reads its argument through the residue nat_mod(w, 2ⁿ), so a
// bound or a sign claimed of it is a fact about that residue. The one
// place a width guard carries content is the top place n − 1 reaching
// back up to n; a member with no guard at all pays instead with a
// width-zero case, where the residue vanishes and the reading is zero.
//
// Both width-zero branches rewrite n to 0 before finishing. That
// rewrite renames the resident bound hypothesis, so the closure's
// `Fact` no longer names it and the branch re-addresses it by text
// (`a.Hyp("w < nat_pow(2, 0)")`); the sites are marked "re-addressed".

package signed_word

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/words/bit_arith"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The signed reading
// ---------------------------------------------------------------------------

// IntOfWordByCases — the signed reading of a value already below the width,
// by the case it falls in. The definition splits on the same half-range
// bound and its branches are already the two integers written here, so
// what has to be proved is smaller than the statement looks: under the
// range guard the residue forgets nothing (nat_div_mod.ModLessThan), and
// the one remaining difference is the LANGUAGE the guard is asked in —
// the definition asks it of the numbers, the statement of the integers.
// The embedding carries ℕ's power to ℤ's and ℕ's strict order to ℤ's,
// so it is one guard, and the conditionals differ in nothing at all.
var IntOfWordByCases = intOfWordByCasesThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordByCases",
	Key:  "prop_780fad24975b242f",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "int_of_word(n, w) = COND(w < int_pow(2, n - 1), int_of_num(w), w - int_pow(2, n))",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			// The definition rides in as a PREMISE rather than being
			// opened on the goal: the close rewrites under it and the two
			// resident equivalences at once — the file's one member where
			// nothing is left after the definition to deduce about.
			intOfWordDef := a.Ctx().ConstDefNormalized("int_of_word")
			two := a.Ctx().Numeral(2)
			width := a.Term("nat_pow(2, n)")

			collapse := a.Have(
				"below the width the reduction forgets nothing",
				"rem(w, nat_pow(2, n)) = w",
				By(wBound, At(nat_div_mod.ModLessThan, w, width)))

			sameGuard := a.Have(
				"the bound is one number on either side of the embedding, so lying below it is one guard",
				"w < nat_pow(2, n - 1) ⇔ w < int_pow(2, n - 1)",
				By(
					At(int_pow.OfNumPow, two, a.Term("n - 1")),
					At(int_embed.OfNumLt, w, a.Term("nat_pow(2, n - 1)"))))

			a.Show(
				"with one guard for the two, unfolding the reading "+
					"leaves conditionals that differ in nothing at all",
				By(Normalized, collapse, sameGuard, intOfWordDef))
		}),
})}

// TopBitIsNegative — the top bit is the sign: the chapter's title
// sentence, STRONG in the value (no range guard: a bit below the width
// survives the reduction, so both sides of the ⇔ only ever see the
// residue).
//
// The two halves of the argument meet at the half-range threshold. On
// the bit side, word_bits.BitWord carries the top bit past the
// reduction and word_bits.MsbVal identifies it with the residue
// reaching half the range. On the sign side, the reading's two branches
// have their signs on their faces: below the threshold it is the
// residue's own image, never negative (int_embed.EmbedNonneg); at or
// above it, the residue less the WHOLE range, and the residue never
// reaches the whole range (Division's bound), so the difference falls
// short of zero (int_real_lift.SubNonneg through the order dualities).
var TopBitIsNegative = topBitIsNegativeThm{family.Add(registry.ProofEntry{
	Name: "TopBitIsNegative",
	Key:  "prop_9bb581eee9b2b165",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "word_bit(n - 1, w) ⇔ int_of_word(n, w) < 0",
		},
		func(a *Argument, n, w Term, widthPos Fact) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			two := a.Ctx().Numeral(2)
			topPlace := a.Term("n - 1")
			width := a.Term("nat_pow(2, n)")
			halfNat := a.Term("nat_pow(2, n - 1)")
			res := a.Term("rem(w, nat_pow(2, n))")
			resInt := a.Term("int_of_num(rem(w, nat_pow(2, n)))")
			wholeRange := a.Term("int_pow(2, n)")
			corrected := a.Term("rem(w, nat_pow(2, n)) - int_pow(2, n)")
			zero := a.TermAs[Int]("0")

			rBound := a.Have(
				"the range, a power of two, is never zero, so the residue sits below it",
				"rem(w, nat_pow(2, n)) < nat_pow(2, n)",
				By(At(nat_arith.PowTwoNonzero, n), At(nat_div_mod.Division, w, width)))
			topInside := a.Have(
				"a positive width keeps its top place inside itself",
				"n - 1 < n",
				By(
					widthPos,
					At(nat_order.PosIffNonzero, n),
					nat_order.OneLessEqIffPos,
					At(nat_monus.SucOfSubOne, n),
					At(nat_order.SucLessEqIffLessThan, topPlace, n),
					nat_order.LessEqRefl))
			defRead := a.Have(
				"the bit, read off its definition",
				"word_bit(n - 1, w) ⇔ nat_odd(div(w, nat_pow(2, n - 1)))",
				By(wordBitDef))
			sameBit := a.Have(
				"so the top bit, sitting inside the width, survives the reduction",
				"word_bit(n - 1, w) ⇔ word_bit(n - 1, rem(w, nat_pow(2, n)))",
				// BitWord is grounded at the width alone; its bit and value
				// slots close by unification against defRead's reading.
				By(topInside, defRead, At(word_bits.BitWord, n)))
			threshold := a.Have(
				"and the top bit is the residue reaching half the range",
				"nat_pow(2, n - 1) ≤ rem(w, nat_pow(2, n)) ⇔ word_bit(n - 1, w)",
				By(widthPos, rBound, sameBit, At(word_bits.MsbVal, n, res)))

			embedBound := a.Have(
				"the residue's bound, carried into ℤ",
				"rem(w, nat_pow(2, n)) < int_pow(2, n)",
				By(rBound, At(int_pow.OfNumPow, two, n), At(int_embed.OfNumLt, res, width)))
			negative := a.Have(
				"so a residue that has the whole range taken from it lands below zero",
				"rem(w, nat_pow(2, n)) - int_pow(2, n) < 0",
				By(
					embedBound,
					At(int_real_lift.SubNonneg, resInt, wholeRange),
					At(int_real_lift.NotLessThan, corrected, zero),
					At(int_real_lift.NotLessThan, resInt, wholeRange)))
			nonneg := a.Have(
				"while a residue left as its own image never does",
				"¬(int_of_num(rem(w, nat_pow(2, n))) < 0)",
				By(At(int_embed.EmbedNonneg, res), int_real_lift.NotLessThan))

			a.Show(
				"the top bit is precisely the question of which of the two readings the residue gets",
				Unfold(IntOfWordDef),
				By(
					nonneg,
					threshold,
					negative,
					// ¬(res < half) ⇔ half ≤ res — the reading's guard and the
					// bit's threshold as one question.
					At(nat_order.NotLessThan, res, halfNat)))
		}),
})}

// IntOfWordBound — the signed reading never leaves ⟦−2ⁿ⁻¹, 2ⁿ⁻¹⟭, with no
// guard at all: the residue is always in range, and at width zero it
// vanishes, the reading is zero, and the window is the unit one
// around it.
//
// On a positive width the two bounds are read off the reading's two
// branches, each needing only one of them argued. Below the threshold
// the reading is the residue's image: under the ceiling by the guard
// carried across the embedding, over the floor by being an image at
// all. At or above it the reading is the residue less the WHOLE range,
// and the two bounds are the two things the residue is known to do —
// it has reached half the range (the guard) and it never reaches all
// of it (Division's bound). What joins them is that the whole range is
// the half range twice over: a power is doubled by raising the
// exponent one place, and the positive width is what gives it a place
// to be raised from.
var IntOfWordBound = intOfWordBoundThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordBound",
	Key:  "prop_49ec5843ce1b1be0",
	Build: family.Theorem(
		"∀n w:num. -int_pow(2, n - 1) ≤ int_of_word(n, w) ∧ int_of_word(n, w) < int_pow(2, n - 1)",
		func(a *Argument, n, w Term) {
			one, two := a.Ctx().Numeral(1), a.Ctx().Numeral(2)
			topPlace := a.Term("n - 1")
			width := a.Term("nat_pow(2, n)")
			halfNat := a.Term("nat_pow(2, n - 1)")
			res := a.Term("rem(w, nat_pow(2, n))")

			notZero := a.Unless(
				a.Term("n = 0"),
				"n = 0: the residue vanishes and the reading is zero, inside the unit window",
				Given(func(z *Argument, isZero Fact) {
					z.Do(Unfold(IntOfWordDef))
					z.Show(
						"the residue at modulus one is zero, whose image sits in ⟦-1, 1⟭",
						ByArith(Normalized, isZero, At(nat_div_mod.ModOne, w), nat_arith.NatPow, int_pow.PowClauses))
				}))

			widthPos := a.Have(
				"a nonzero width is at least one",
				"1 ≤ n",
				By(notZero, At(nat_order.PosIffNonzero, n), nat_order.OneLessEqIffPos))
			doubling := a.Have(
				"the whole range is the half range twice over — the width has a place to raise the power from",
				"nat_pow(2, n) = nat_pow(2, n - 1) + nat_pow(2, n - 1)",
				ByArith(
					Normalized,
					widthPos,
					At(nat_monus.SubAddCancel, n, one), // (n - 1) + 1 = n
					At(nat_arith.Add1, topPlace),       // suc(n - 1) = (n - 1) + 1
					// Bare — its ∀-form closes the goal at the install.
					nat_arith.PowTwoSuc)) // 2ᵏ + 2ᵏ = 2^suc(k), at the top place

			a.Cases(a.Term("rem(w, nat_pow(2, n)) < nat_pow(2, n - 1)"))
			a.When(
				"below half the range the reading is the residue's image: under "+
					"the ceiling by the guard, over the floor by being an image at all",
				func(b *Argument, below Fact) {
					reading := b.Have(
						"the reading is the residue itself",
						"int_of_word(n, w) = rem(w, nat_pow(2, n))",
						Unfold(IntOfWordDef),
						By(below))
					b.Do(reading.Rw())
					b.Do(SplitConj(
						Case(
							"over the floor: no image is negative — least of all below minus the half range's",
							ByArith(At(int_embed.EmbedNonneg, res), At(int_embed.EmbedNonneg, halfNat))),
						Case(
							"under the ceiling: the guard, carried across the embedding",
							By(below, At(int_pow.OfNumPow, two, topPlace), At(int_embed.OfNumLt, res, halfNat))),
					))
				})
			a.Otherwise(
				"at or above it the reading is the residue less the whole "+
					"range: half the range in hand, the whole still out of reach",
				func(b *Argument, above Fact) {
					reading := b.Have(
						"past the threshold the reading is the residue less the whole range",
						"int_of_word(n, w) = rem(w, nat_pow(2, n)) - int_pow(2, n)",
						Unfold(IntOfWordDef),
						By(above))
					reachesN := b.Have(
						"topped up by half the range the residue reaches the whole, having reached half already",
						"nat_pow(2, n) ≤ rem(w, nat_pow(2, n)) + nat_pow(2, n - 1)",
						ByArith(above, doubling))
					reaches := b.Have(
						"and the embedding carries the sum and the order across",
						"int_of_num(nat_pow(2, n)) ≤ int_of_num(rem(w, nat_pow(2, n))) + int_of_num(nat_pow(2, n - 1))",
						// Neither law is grounded: both land as rewrites,
						// the sum going under one coercion, the order down
						// to ℕ's own.
						By(reachesN, int_embed.OfNumAdd, int_embed.OfNumLe))
					shortN := b.Have(
						"while the residue falls short of the range, a power of "+
							"two and never zero, so short of half and the whole together",
						"rem(w, nat_pow(2, n)) < nat_pow(2, n - 1) + nat_pow(2, n)",
						ByArith(At(nat_arith.PowTwoNonzero, n), At(nat_div_mod.Division, w, width)))
					short := b.Have(
						"carried across the embedding the same way",
						"int_of_num(rem(w, nat_pow(2, n))) < int_of_num(nat_pow(2, n - 1)) + int_of_num(nat_pow(2, n))",
						By(shortN, int_embed.OfNumAdd, int_embed.OfNumLt))
					b.Do(reading.Rw())
					b.Do(SplitConj(
						Case(
							"over the floor: the residue reaches the whole range "+
								"topped up by half, so the difference clears minus a half",
							ByArith(reaches)),
						Case(
							"under the ceiling: the residue is short of half and "+
								"the whole together, so the difference is short of a half",
							ByArith(short)),
					))
				})
		}),
})}

// TopBitByIntValue — the top-bit test, read in ℤ: under the range
// guard, the bit at the top place is set exactly when the value's
// image reaches the embedded half range. word_bits.MsbVal settles
// the same question among the NUMBERS; the whole content here is
// undoing the transport — the bound is one number raised in ℕ and then
// embedded or embedded and then raised, and a comparison between two
// images is the numbers' own. At width zero the guard pins the value
// to zero, and both sides are false: the zero word has no bits, and
// one exceeds no image of zero.
var TopBitByIntValue = topBitByIntValueThm{family.Add(registry.ProofEntry{
	Name: "TopBitByIntValue",
	Key:  "prop_37f5fdf33c61a31b",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "word_bit(n - 1, w) ⇔ int_pow(2, n - 1) ≤ w",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			notZero := a.Unless(
				a.Term("n = 0"),
				"n = 0: the only word below the unit range is zero "+
					"— no bit to read, and one exceeds no image of zero",
				Given(func(z *Argument, isZero Fact) {
					z.Do(isZero.Rw())
					zeroWord := z.Have(
						"below the unit range the word is zero",
						"w = 0",
						// Re-addressed: see the file header.
						ByArith(z.Hyp("w < nat_pow(2, 0)"), nat_arith.NatPow))
					z.Do(zeroWord.Rw())
					z.Do(Unfold(machine_word.WordBitDef))
					z.Show(
						"every quotient of zero is zero, zero is even, and one exceeds zero's image on neither side",
						ByArith(Normalized, nat_div_mod.ZeroDiv, nat_parity.NatOdd, nat_arith.NatPow))
				}))

			widthPos := a.Have(
				"a nonzero width is at least one",
				"1 ≤ n",
				By(notZero, At(nat_order.PosIffNonzero, n), nat_order.OneLessEqIffPos))
			msb := a.Have(
				"the top bit is the half-range threshold, read on the value",
				"nat_pow(2, n - 1) ≤ w ⇔ word_bit(n - 1, w)",
				By(widthPos, wBound, At(word_bits.MsbVal, n, w)))
			bridge := a.Have(
				"the bound is one number, raised in ℕ and then embedded or embedded and then raised",
				"nat_pow(2, n - 1) = int_pow(2, n - 1)",
				By(int_pow.OfNumPow))
			order := a.Have(
				"and comparing two images compares the numbers themselves",
				"nat_pow(2, n - 1) ≤ int_of_num(w) ⇔ nat_pow(2, n - 1) ≤ w",
				By(int_embed.OfNumLe))

			a.Show(
				"undo the transport, and what remains is the threshold among the numbers",
				By(msb, bridge, order))
		}),
})}

// ---------------------------------------------------------------------------
// The signed reading in closed form
// ---------------------------------------------------------------------------
//
// int_of_word's definition splits the range in half: below half the range a
// value is worth itself, above it the whole range is given away to the
// negatives. Naming the digit the top bit stands for absorbs that split
// into one expression — the correction a value suffers is always the
// range times that digit, the range itself where the bit is set and
// nothing where it is clear. Two members: the reading as the value less
// the top-bit-weighted range, and the same equation transposed to
// recover the value from the reading.

// IntOfWordByTopBit — the signed reading in closed form: an in-range value
// reads as itself, less the whole range weighted by its top bit.
//
// The proof makes the definition's case split explicit again. In range
// the residue int_of_word reads is the value itself, and everything then
// turns on one claim: a value falls short of half the range exactly
// when its top bit is clear — word_bits.MsbVal read through ℕ's order
// duality. Each branch is then a single step of ℤ arithmetic: a set bit
// weights the range by one, a clear bit weights it by nothing, and
// taking nothing away leaves the value. MsbVal speaks only of positive
// widths; at width zero the only in-range value is 0 and both sides
// compute to int_of_num(0) by the zero clauses.
var IntOfWordByTopBit = intOfWordByTopBitThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordByTopBit",
	Key:  "prop_1e95f0fdffdf899",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "int_of_word(n, w) = w - int_pow(2, n) * bit_value(word_bit(n - 1, w))",
		},
		func(a *Argument, n, w Term, small Fact) {
			// Assuming (not Unless): the main line wants the POSITIVE
			// form 1 ≤ n resident — MsbVal consumes it directly, where
			// the siblings' n = 0 split would cost the bridge back.
			widthPos := a.Assuming(
				a.Term("1 ≤ n"),
				"width zero: the only in-range value is 0, and both sides compute to 0",
				Given(func(a *Argument, tooNarrow Fact) {
					zero := a.Ctx().Numeral(0)
					one := a.Ctx().Numeral(1)
					two := a.Ctx().Numeral(2)

					zeroWidth := a.Have(
						"a width that is not at least 1 is zero",
						"n = 0",
						By(tooNarrow, At(nat_order.OneLessEqIffPos, n), nat_order.PosIffNonzero))
					// ↦ every n in the goal and the hypotheses becomes 0
					a.Do(zeroWidth.Rw())
					zeroWord := a.Have(
						"and below nat_pow(2, 0) = 1 the only value is zero",
						"w = 0",
						// Re-addressed: see the file header.
						By(
							Normalized,
							a.Hyp("w < nat_pow(2, 0)"),
							nat_arith.NatPow,
							nat_arith.OneIsSucZero,
							At(nat_order.LessThanSucIffLessEq, w, zero),
							At(nat_order.LessEqZeroClause, w)))
					// ↦ int_of_word(0, 0) = int_of_num(0) - int_pow(int_of_num(2), 0) * int_of_num(bit_value(word_bit(0 - 1, 0)))
					a.Do(
						zeroWord.Rw(),
						Unfold(IntOfWordDef),
						Unfold(machine_word.WordBitDef),
						Unfold(machine_word.BitValueDef))
					a.Show(
						"with every argument a numeral, the zero clauses compute both sides to 0",
						By(
							nat_arith.NatPow,
							nat_arith.OneIsSucZero,
							nat_div_mod.ZeroMod,
							nat_div_mod.ZeroDiv,
							nat_parity.NatOdd,
							nat_order.ZeroLessThanSuc,
							At(nat_monus.SubEqZero, zero, one),
							At(nat_order.ZeroLessEq, one),
							At(int_pow.OfNumPow, two, zero),
							int_real_lift.MulRightZero,
							int_real_lift.SubRightZero))
				}))

			residue := a.Have(
				"in range, the residue the reading takes is the value itself",
				"rem(w, nat_pow(2, n)) = w",
				By(small, At(nat_div_mod.ModLessThan, w, a.Term("nat_pow(2, n)"))))
			// Unfolding int_of_word brings in rem(w, nat_pow(2, n)) three
			// times, and the equation collapses each to w:
			// ↦ COND(w < nat_pow(2, n - 1), int_of_num(w), int_of_num(w) - int_pow(int_of_num(2), n))
			// = int_of_num(w) - int_pow(int_of_num(2), n) * int_of_num(bit_value(word_bit(n - 1, w)))
			a.Do(Unfold(IntOfWordDef), residue.Rw())

			// MsbVal goes in bare, the two resident order facts picking
			// the instance out. Grounding it fully works too (the sign
			// and threshold members above do exactly that); what fails
			// is the HALF-grounded form — a width-only specialization
			// leaves an install the refuter cannot finish.
			threshold := a.Have(
				"the top bit is the half-range threshold, read on the value",
				"nat_pow(2, n - 1) ≤ w ⇔ word_bit(n - 1, w)",
				By(small, widthPos, word_bits.MsbVal))
			guard := a.Have(
				"so, through ℕ's order duality, the reading's guard is the top bit",
				"w < nat_pow(2, n - 1) ⇔ ¬word_bit(n - 1, w)",
				By(threshold, At(nat_order.NotLessEq, a.Term("nat_pow(2, n - 1)"), w)))
			// ↦ COND(¬word_bit(n - 1, w), int_of_num(w), int_of_num(w) - int_pow(int_of_num(2), n))
			// = int_of_num(w) - int_pow(int_of_num(2), n) * int_of_num(bit_value(word_bit(n - 1, w)))
			a.Do(guard.Rw())

			a.Cases(a.Term("word_bit(n - 1, w)"))
			a.When(
				"the top bit is set: the reading gives the whole range away — and a set bit weights it by one",
				func(b *Argument, set Fact) {
					// ↦ int_of_num(w) - int_pow(int_of_num(2), n) = int_of_num(w) - int_pow(int_of_num(2), n) * int_of_num(1)
					b.Show(
						"the set bit settles both guards, and a set bit weights the range by one",
						Unfold(machine_word.BitValueDef),
						By(set, int_real_lift.MulRightIdentity))
				})
			a.Otherwise(
				"the top bit is clear: the reading is the value "+
					"itself — and a clear bit weights the range by nothing",
				func(b *Argument, clear Fact) {
					// ↦ int_of_num(w) = int_of_num(w) - int_pow(int_of_num(2), n) * int_of_num(0)
					b.Show(
						"the clear bit settles both guards, and a clear bit weights the range by nothing",
						Unfold(machine_word.BitValueDef),
						By(clear, int_real_lift.MulRightZero, int_real_lift.SubRightZero))
				})
		}),
})}

// ValByTopBit — the closed form transposed: the value is the signed
// reading with the correction restored. `IntOfWordByTopBit` says the same
// equation from the other side — the correction stands subtracted there
// and added here — so nothing about words is at stake, and restoring a
// taken-away difference is a law of ℤ.
var ValByTopBit = valByTopBitThm{family.Add(registry.ProofEntry{
	Name: "ValByTopBit",
	Key:  "prop_b177e5c2705ea5c0",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "w = int_of_word(n, w) + int_pow(2, n) * bit_value(word_bit(n - 1, w))",
		},
		func(a *Argument, n, w Term, small Fact) {
			// The value the bits spell, read in ℤ; and the correction the
			// reading applies to it — the whole range, weighted by the
			// top bit.
			unsigned := a.TermAs[Int]("w")
			correction := a.Term("int_pow(2, n) * bit_value(word_bit(n - 1, w))")

			a.Show(
				"the reading takes the correction away, so the value is what putting it back recovers",
				By(
					small,
					// int_of_word(n, w) = unsigned - correction
					At(IntOfWordByTopBit, n, w),
					// unsigned - correction + correction = unsigned
					At(int_real_lift.SubAddRight, unsigned, correction)))
		}),
})}

// ---------------------------------------------------------------------------
// The two readings modulo the range
// ---------------------------------------------------------------------------

// IntOfWordValCong — the signed reading and the value are congruent modulo
// the range, at EVERY width and value: no range guard is owed, and at
// width zero everything is congruent mod 1. Two facts feed the definition's case
// split. The embedded residue is congruent to the embedded value — ℕ's
// own congruence, carried across the embedding — and the modulus itself
// is congruent to zero. The low half of the range IS the embedded
// residue; the high half differs from it by exactly one modulus, which
// subtracting the zero-congruent modulus preserves.
var IntOfWordValCong = intOfWordValCongThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordValCong",
	Key:  "prop_691a75f4174a49fb",
	Build: family.Theorem(
		"∀n w:num. int_of_word(n, w) ≡ w (mod int_pow(2, n))",
		func(a *Argument, n, w Term) {
			two := a.Ctx().Numeral(2)
			size := a.Term("nat_pow(2, n)")                       // the range, in ℕ
			residue := a.Term("rem(w, nat_pow(2, n))")            // the residue the reading takes
			embRes := a.Term("int_of_num(rem(w, nat_pow(2, n)))") // the same residue, read in ℤ
			embVal := a.TermAs[Int]("w")                          // the value, read in ℤ
			modulus := a.Term("int_pow(2, n)")                    // the range, in ℤ
			intZero := a.TermAs[Int]("0")

			cross := a.Have(
				"the residue is congruent to the value in ℕ already; "+
					"the embedding carries that to ℤ, at the ℤ-side modulus",
				"rem(w, nat_pow(2, n)) ≡ w (mod int_pow(2, n))",
				By(
					// nat_mod(w, nat_pow(2, n)) is congruent to w mod nat_pow(2, n)
					At(nat_congruence.ResidueCongruent, w, size),
					// which read in ℤ is embRes ≡ embVal (mod int_of_num(nat_pow(2, n)))
					At(int_congruence.OfNumCongruent, residue, w, size),
					// and the embedded ℕ range is the ℤ one
					At(int_pow.OfNumPow, two, n)))

			modZero := a.Have(
				"the modulus itself is congruent to zero — it exceeds 0 by exactly one copy of itself",
				"int_pow(2, n) ≡ 0 (mod int_pow(2, n))",
				By(
					// modulus ≡ int_of_num(0) ⇔ ∃d. modulus - int_of_num(0) = modulus * d
					At(int_congruence.CongruentIffMultiple, modulus, intZero, modulus),
					// modulus - int_of_num(0) = modulus
					At(int_real_lift.SubRightZero, modulus),
					// modulus * int_of_num(1) = modulus — the copy exhibited
					At(int_real_lift.MulRightIdentity, modulus)))

			// ↦ COND(nat_mod(w, nat_pow(2, n)) < nat_pow(2, n - 1), embRes, embRes - modulus)
			// ≡ int_of_num(w) (mod int_pow(int_of_num(2), n))
			a.Do(Unfold(IntOfWordDef))

			a.Cases(a.Term("rem(w, nat_pow(2, n)) < nat_pow(2, n - 1)"))
			a.When(
				"low half: the reading IS the embedded residue, and the crossing is exactly the claim",
				func(a *Argument, inLow Fact) {
					a.Show(
						"the guard selects the first branch",
						By(inLow, cross))
				})
			a.Otherwise(
				"high half: the reading is the residue less one modulus, and "+
					"subtracting the zero-congruent modulus preserves the crossing",
				// ↦ embRes - modulus ≡ int_of_num(w) (mod modulus)
				By(
					cross,
					modZero,
					// embRes - modulus ≡ embVal - int_of_num(0), from cross and modZero
					At(int_congruence.SubCongruent, embRes, embVal, modulus, intZero, modulus),
					int_real_lift.SubRightZero))
		}),
})}

// ---------------------------------------------------------------------------
// When two words share a signed reading
// ---------------------------------------------------------------------------
//
// The signed reading loses nothing: on values already below the width,
// two readings are congruent modulo the range exactly when the values
// are equal, and equal outright exactly when the values are. The
// congruence form comes first — the reading and the value leave the
// same remainder (IntOfWordValCong above), so the question descends to when
// two VALUES are congruent, and below the width a value is its own
// residue. The equality form travels one direction of the congruence
// and gets the other for free, equal values having equal readings.

// EqByIntOfWordCong — two in-range values are equal exactly when their
// signed readings are congruent modulo the range: the reading loses
// nothing, even taken only up to congruence.
//
// The argument runs through the unsigned images. Two in-range values
// are equal exactly when their images in ℤ are congruent — below the
// width a value is its own residue (nat_div_mod.ModLessThan), ℕ's
// congruence is an equality of residues by its definition, and the
// embedding carries that congruence to ℤ at the ℤ-side modulus
// (int_congruence.OfNumCongruent, the range raised on either side of the
// embedding by int_pow.OfNumPow). And each reading leaves the same
// remainder as its own image (IntOfWordValCong above), so the readings are
// congruent exactly when the images are: a congruence modulo the range
// is an equality of remainders (int_congruence.CongruentIffSameRem),
// taken at the four pairs in play — each reading against its own
// image, then the two readings and the two images against each other.
// Read that way every premise is an equation or an equivalence, and
// what closes each step is the premises rewriting into each other, not
// a search.
var EqByIntOfWordCong = eqByIntOfWordCongThm{family.Add(registry.ProofEntry{
	Name: "EqByIntOfWordCong",
	Key:  "prop_6114a98cc2a6e6f4",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
			},
			Conclusion: "v = w ⇔ int_of_word(n, v) ≡ int_of_word(n, w) (mod int_pow(2, n))",
		},
		func(a *Argument, n, v, w Term, vBound, wBound Fact) {
			two := a.Ctx().Numeral(2)
			width := a.Term("nat_pow(2, n)")
			modulus := a.Term("int_pow(2, n)")
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")

			// The four integers the argument compares: the two readings
			// and the two images.
			ivalV, ivalW := a.Term("int_of_word(n, v)"), a.Term("int_of_word(n, w)")
			imageV, imageW := a.TermAs[Int]("v"), a.TermAs[Int]("w")

			unsigned := a.Have(
				"two in-range values are equal exactly when their images in ℤ are congruent modulo the range",
				"v = w ⇔ v ≡ w (mod int_pow(2, n))",
				By(
					Normalized,
					vBound,
					wBound,
					// the modulus is one range, raised in ℕ and then
					// embedded or embedded and then raised
					At(int_pow.OfNumPow, two, n),
					// &v ≡ &w at the embedded range is ℕ's own congruence
					At(int_congruence.OfNumCongruent, v, w, width),
					// which is an equality of residues, by definition
					natCongDef,
					// and below the width each value IS its residue
					At(nat_div_mod.ModLessThan, v, width),
					At(nat_div_mod.ModLessThan, w, width)))

			a.Show(
				"each reading leaves the same remainder as its own image, "+
					"so the readings are congruent exactly when the images are",
				By(
					unsigned,
					At(IntOfWordValCong, n, v), // int_of_word(n, v) ≡ int_of_num(v) (mod modulus)
					At(IntOfWordValCong, n, w), // and the same at w
					// Congruence modulo the range is equality of remainders
					// modulo it, at the four pairs in play.
					At(int_congruence.CongruentIffSameRem, ivalV, imageV, modulus),
					At(int_congruence.CongruentIffSameRem, ivalW, imageW, modulus),
					At(int_congruence.CongruentIffSameRem, ivalV, ivalW, modulus),
					At(int_congruence.CongruentIffSameRem, imageV, imageW, modulus)))
		}),
})}

// EqByIntOfWord — the signed reading is injective on the range: two in-range
// values are equal exactly when their readings are.
//
// This is `EqByIntOfWordCong` with the modulus taken away, and taking it
// away is cheap, because only one direction of that congruence is
// travelled. Equal readings leave equal remainders, so they are
// congruent readings, and the congruence carries them to equal values.
// The converse asks nothing at all: `int_of_word` is a function, so equal
// values have equal readings.
var EqByIntOfWord = eqByIntOfWordThm{family.Add(registry.ProofEntry{
	Name: "EqByIntOfWord",
	Key:  "prop_72deda560b43bb89",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
			},
			Conclusion: "int_of_word(n, v) = int_of_word(n, w) ⇔ v = w",
		},
		func(a *Argument, n, v, w Term, vBound, wBound Fact) {
			// Both premises are equivalences and the two readings meet
			// only by substitution, so what closes this is the pair
			// simplifying into the goal, not a refutation.
			a.Show(
				"equal readings leave equal remainders, so they are congruent readings "+
					"and the values are equal; and equal values have equal readings",
				By(
					vBound,
					wBound,
					// v = w ⇔ int_of_word(n, v) ≡ int_of_word(n, w) (mod int_pow(&2, n))
					At(EqByIntOfWordCong, n, v, w),
					// and that congruence is an equality of remainders
					At(int_congruence.CongruentIffSameRem,
						a.Term("int_of_word(n, v)"), a.Term("int_of_word(n, w)"),
						a.Term("int_pow(2, n)"))))
		}),
})}

// ---------------------------------------------------------------------------
// The reading at zero
// ---------------------------------------------------------------------------
//
// At zero the reading is zero with no guard at all, and with the
// equality form above it makes the zero test: a value in range reads
// as zero exactly when it is zero.

// IntOfWordZero — zero reads as zero, at every width. No guard is owed:
// zero's residue is zero at any modulus — width zero included, where
// the range is 1 and the residue vanishes the same way.
//
// Unfolding the reading, the one thing that needs saying is that the
// half-range threshold lies above zero at all: it is a power of two,
// which never vanishes (`nat_arith.PowTwoNonzero`). With that, zero's
// residue sits below the threshold and the reading is the residue's
// own image.
var IntOfWordZero = intOfWordZeroThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordZero",
	Key:  "prop_7335f8beaa4d17af",
	Build: family.Theorem(
		"∀n:num. 0 = int_of_word(n, 0)",
		func(a *Argument, n Term) {
			topPlace := a.Term("n - 1")
			half := a.Term("nat_pow(2, n - 1)")

			// ↦ int_of_num(0) = COND(nat_mod(0, nat_pow(2, n)) < nat_pow(2, n - 1),
			// int_of_num(nat_mod(0, nat_pow(2, n))),
			// int_of_num(nat_mod(0, nat_pow(2, n))) - int_pow(int_of_num(2), n))
			a.Do(Unfold(IntOfWordDef))

			a.Show(
				"zero's residue is zero, below the positive threshold, "+
					"where the reading is the residue's own image",
				By(
					At(nat_arith.PowTwoNonzero, topPlace),
					At(nat_order.PosIffNonzero, half),
					// nat_mod(0, ·) = 0 — left bare: it lands as the rewrite
					// that collapses the residue everywhere it appears.
					nat_div_mod.ZeroMod))
		}),
})}

// IntOfWordEqZero — the zero test: a value in range reads as zero exactly
// when it is zero.
//
// `EqByIntOfWord` says the reading tells in-range values apart, and
// `IntOfWordZero` names what zero reads as — so asked against zero, the
// injectivity IS this statement. The only fact the instance owes is
// that zero is in range at every width: a power of two is positive.
var IntOfWordEqZero = intOfWordEqZeroThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordEqZero",
	Key:  "prop_de2049579dd7080b",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "0 = int_of_word(n, w) ⇔ w = 0",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			width := a.Term("nat_pow(2, n)")

			a.Show(
				"zero is in range at every width: a value reads as zero exactly when "+
					"it reads as zero does, and the reading tells in-range values apart",
				By(
					wBound,
					At(nat_arith.PowTwoNonzero, n),
					At(nat_order.PosIffNonzero, width),
					// int_of_word(n, w) = int_of_word(n, 0) ⇔ w = 0
					At(EqByIntOfWord, n, w, a.Ctx().Numeral(0)),
					// int_of_num(0) = int_of_word(n, 0)
					At(IntOfWordZero, n)))
		}),
})}

// ---------------------------------------------------------------------------
// The ring operations, read signed
// ---------------------------------------------------------------------------
//
// One descent serves all four congruence laws. The reading is congruent
// to its argument's image (`IntOfWordValCong`), so both sides of every claim
// come down to images of numbers; the word operation is a reduction, and
// a reduction is congruent to what it reduced (the residue congruence,
// or the val-face group law); and ℤ's congruence respects the ring
// operations. What joins the pieces is always the same computational
// reading: a congruence modulo the range is an equality of remainders,
// so a chain of congruences is a chain of equations. The complement
// identity has no modulus on its face, and it is recovered from the
// congruence the same way the constructor's round trip was: both sides
// keep to the reading's half-open window, the window is narrower than
// the range, and a congruence over a gap smaller than its modulus is an
// equality.

// CongAdd — the sum's reading is congruent to the sum of the readings,
// modulo the range, at every width and ALL inputs: no guard, because the
// reading and the operation both work through the residue.
//
// Both sides descend to images. The sum's word is the reduction of the
// raw sum, so its image is congruent to `&x + &y` — ℕ's residue
// congruence carried across the embedding, the embedding splitting the
// sum and raising the range. And each reading is congruent to its own
// image (`IntOfWordValCong`), so the readings' sum is congruent to the same
// `&x + &y` — ℤ's congruence respecting addition. Read as equalities of
// remainders, the two descents meet in the middle.
var CongAdd = congAddThm{family.Add(registry.ProofEntry{
	Name: "CongAdd",
	Key:  "prop_77872031607949aa",
	Build: family.Theorem(
		"∀n x y:num. "+
			"    int_of_word(n, word_add(n, x, y)) ≡ "+
			"    (int_of_word(n, x) + int_of_word(n, y)) (mod int_pow(2, n))",
		func(a *Argument, n, x, y Term) {
			two := a.Ctx().Numeral(2)
			size := a.Term("nat_pow(2, n)")
			rawSum := a.Term("x + y")
			residue := a.Term("rem(x + y, nat_pow(2, n))")
			modulus := a.Term("int_pow(2, n)")

			// The four integers the chain runs through: the sum's
			// reading, its image, the images' sum, the readings' sum.
			readOp := a.Term("int_of_word(n, word_add(n, x, y))")
			embOp := a.Term("int_of_num(word_add(n, x, y))")
			embSum := a.Term("int_of_num(x) + y")
			readSum := a.Term("int_of_word(n, x) + int_of_word(n, y)")

			image := a.Have(
				"the sum's word is the reduced raw sum, whose image is congruent to the images' sum",
				"word_add(n, x, y) ≡ x + &y (mod int_pow(2, n))",
				// ↦ &(nat_mod(x + y, 2ⁿ)) ≡ &x + &y (mod int_pow(&2, n))
				Unfold(machine_word.WordAddDef),
				By(
					// nat_mod(x + y, 2ⁿ) ≡ x + y, in ℕ
					At(nat_congruence.ResidueCongruent, rawSum, size),
					// which read in ℤ is the images' congruence at the embedded range
					At(int_congruence.OfNumCongruent, residue, rawSum, size),
					// the range, raised in ℕ then embedded or embedded then raised
					At(int_pow.OfNumPow, two, n),
					// and the embedding splits the sum
					At(int_embed.OfNumAdd, x, y)))
			readings := a.Have(
				"and each reading is congruent to its own image, so "+
					"the readings' sum is congruent to the images' sum",
				"int_of_word(n, x) + int_of_word(n, y) ≡ x + &y (mod int_pow(2, n))",
				By(
					At(IntOfWordValCong, n, x),
					At(IntOfWordValCong, n, y),
					At(int_congruence.AddCongruent,
						a.Term("int_of_word(n, x)"), a.TermAs[Int]("x"),
						a.Term("int_of_word(n, y)"), a.TermAs[Int]("y"), modulus)))
			a.Show(
				"the two descents share the images' sum, and read as "+
					"equalities of remainders they chain into the claim",
				By(
					image,
					readings,
					// the sum's reading descends to its image
					At(IntOfWordValCong, n, a.Term("word_add(n, x, y)")),
					// each congruence in play, as an equality of remainders
					At(int_congruence.CongruentIffSameRem, readOp, embOp, modulus),
					At(int_congruence.CongruentIffSameRem, embOp, embSum, modulus),
					At(int_congruence.CongruentIffSameRem, readSum, embSum, modulus),
					At(int_congruence.CongruentIffSameRem, readOp, readSum, modulus)))
		}),
})}

// CongMul — the product's reading is congruent to the product of the
// readings: `CongAdd`'s multiplicative twin, the same two descents with
// the embedding splitting a product and ℤ's congruence respecting
// multiplication.
var CongMul = congMulThm{family.Add(registry.ProofEntry{
	Name: "CongMul",
	Key:  "prop_803e5296cce96d20",
	Build: family.Theorem(
		"∀n x y:num. "+
			"    int_of_word(n, word_mul(n, x, y)) ≡ "+
			"    (int_of_word(n, x) * int_of_word(n, y)) (mod int_pow(2, n))",
		func(a *Argument, n, x, y Term) {
			two := a.Ctx().Numeral(2)
			size := a.Term("nat_pow(2, n)")
			rawProduct := a.Term("x * y")
			residue := a.Term("rem(x * y, nat_pow(2, n))")
			modulus := a.Term("int_pow(2, n)")

			readOp := a.Term("int_of_word(n, word_mul(n, x, y))")
			embOp := a.Term("int_of_num(word_mul(n, x, y))")
			embProduct := a.Term("int_of_num(x) * y")
			readProduct := a.Term("int_of_word(n, x) * int_of_word(n, y)")

			image := a.Have(
				"the product's word is the reduced raw product, whose image is congruent to the images' product",
				"word_mul(n, x, y) ≡ x * &y (mod int_pow(2, n))",
				// ↦ &(nat_mod(x * y, 2ⁿ)) ≡ &x * &y (mod int_pow(&2, n))
				Unfold(machine_word.WordMulDef),
				By(
					At(nat_congruence.ResidueCongruent, rawProduct, size),
					At(int_congruence.OfNumCongruent, residue, rawProduct, size),
					At(int_pow.OfNumPow, two, n),
					At(int_embed.OfNumMul, x, y)))
			readings := a.Have(
				"and each reading is congruent to its own image, so the "+
					"readings' product is congruent to the images' product",
				"int_of_word(n, x) * int_of_word(n, y) ≡ x * &y (mod int_pow(2, n))",
				By(
					At(IntOfWordValCong, n, x),
					At(IntOfWordValCong, n, y),
					At(int_congruence.MulCongruent,
						a.Term("int_of_word(n, x)"), a.TermAs[Int]("x"),
						a.Term("int_of_word(n, y)"), a.TermAs[Int]("y"), modulus)))
			a.Show(
				"the two descents share the images' product, and read "+
					"as equalities of remainders they chain into the claim",
				By(
					image,
					readings,
					At(IntOfWordValCong, n, a.Term("word_mul(n, x, y)")),
					At(int_congruence.CongruentIffSameRem, readOp, embOp, modulus),
					At(int_congruence.CongruentIffSameRem, embOp, embProduct, modulus),
					At(int_congruence.CongruentIffSameRem, readProduct, embProduct, modulus),
					At(int_congruence.CongruentIffSameRem, readOp, readProduct, modulus)))
		}),
})}

// CongNeg — the negation's reading is congruent to the negated reading.
// The val-face group law says the negation tops its word up to a
// multiple of the range (`machine_word.CongNeg`); crossed into ℤ and combined
// with the two readings' descents, that makes the negation's reading and
// the plain reading sum to zero modulo the range — which IS the claim,
// because a difference from a negation is that sum: read through
// `CongruentIffMultiple`, both congruences exhibit the same multiple.
var CongNeg = congNegThm{family.Add(registry.ProofEntry{
	Name: "CongNeg",
	Key:  "prop_c2e9c07e14da98f5",
	Build: family.Theorem(
		"∀n x:num. int_of_word(n, word_neg(n, x)) ≡ -int_of_word(n, x) (mod int_pow(2, n))",
		func(a *Argument, n, x Term) {
			two, zero := a.Ctx().Numeral(2), a.Ctx().Numeral(0)
			size := a.Term("nat_pow(2, n)")
			modulus := a.Term("int_pow(2, n)")
			intZero := a.TermAs[Int]("0")

			negWord := a.Term("word_neg(n, x)")
			readNeg := a.Term("int_of_word(n, word_neg(n, x))")
			readX := a.Term("int_of_word(n, x)")
			readSum := a.Term("int_of_word(n, word_neg(n, x)) + int_of_word(n, x)")
			embSum := a.Term("word_neg(n, x) + int_of_num(x)")

			crossNeg := a.Have(
				"a word beside its negation sums to zero modulo the "+
					"range; the embedding carries that to ℤ, splitting the sum",
				"word_neg(n, x) + &x ≡ 0 (mod int_pow(2, n))",
				By(
					At(machine_word.CongNeg, n, x),
					At(int_congruence.OfNumCongruent, a.Term("word_neg(n, x) + x"), zero, size),
					At(int_embed.OfNumAdd, negWord, x),
					At(int_pow.OfNumPow, two, n)))
			sumZero := a.Have(
				"each reading is congruent to its image, so the two readings sum to zero modulo the range as well",
				"int_of_word(n, word_neg(n, x)) + int_of_word(n, x) ≡ 0 (mod int_pow(2, n))",
				By(
					crossNeg,
					At(IntOfWordValCong, n, negWord),
					At(IntOfWordValCong, n, x),
					At(int_congruence.AddCongruent,
						readNeg, a.Term("int_of_num(word_neg(n, x))"),
						readX, a.TermAs[Int]("x"), modulus),
					At(int_congruence.CongruentIffSameRem, readSum, embSum, modulus),
					At(int_congruence.CongruentIffSameRem, embSum, intZero, modulus),
					At(int_congruence.CongruentIffSameRem, readSum, intZero, modulus)))
			a.Show(
				"summing to zero and being congruent to the negation "+
					"exhibit one and the same multiple of the range",
				By(
					sumZero,
					// readSum ≡ 0 ⇔ ∃d. readSum - 0 = range · d
					At(int_congruence.CongruentIffMultiple, readSum, intZero, modulus),
					// readNeg ≡ -readX ⇔ ∃d. readNeg - -readX = range · d
					At(int_congruence.CongruentIffMultiple, readNeg,
						a.Term("int_neg(int_of_word(n, x))"), modulus),
					// and the two differences are one term: x - -y = x + y,
					At(int_real_lift.SubRightNeg, readNeg, readX),
					// while taking zero away takes nothing.
					int_real_lift.SubRightZero))
		}),
})}

// CongSub — the difference's reading is congruent to the difference of
// the readings. Nothing new is proved about words: `word_sub` is by
// definition addition of the negation, so `CongAdd` and `CongNeg`
// compose under the congruence, and what remains is ℤ bookkeeping —
// adding a negation IS subtracting.
var CongSub = congSubThm{family.Add(registry.ProofEntry{
	Name: "CongSub",
	Key:  "prop_a2645c886b1f14ed",
	Build: family.Theorem(
		"∀n x y:num. "+
			"    int_of_word(n, word_sub(n, x, y)) ≡ "+
			"    (int_of_word(n, x) - int_of_word(n, y)) (mod int_pow(2, n))",
		func(a *Argument, n, x, y Term) {
			modulus := a.Term("int_pow(2, n)")

			readSub := a.Term("int_of_word(n, word_sub(n, x, y))")
			readX := a.Term("int_of_word(n, x)")
			readNegY := a.Term("int_of_word(n, word_neg(n, y))")
			negReadY := a.Term("int_neg(int_of_word(n, y))")
			sumForm := a.Term("int_of_word(n, x) + int_of_word(n, word_neg(n, y))")
			negAddForm := a.Term("int_of_word(n, x) + int_neg(int_of_word(n, y))")
			subForm := a.Term("int_of_word(n, x) - int_of_word(n, y)")

			viaAdd := a.Have(
				"a difference is addition of the negation, so its "+
					"reading is congruent to x's reading plus the negation's",
				"int_of_word(n, word_sub(n, x, y)) ≡ "+
					"int_of_word(n, x) + int_of_word(n, word_neg(n, y)) (mod int_pow(2, n))",
				// ↦ int_of_word(n, word_add(n, x, word_neg(n, y))) ≡ …, which is CongAdd's
				// own instance and closes at its ∀-form install.
				Unfold(machine_word.WordSubDef),
				By(CongAdd))
			negReading := a.Have(
				"and the negation's reading is congruent to the negated reading",
				"int_of_word(n, word_neg(n, y)) ≡ int_neg(int_of_word(n, y)) (mod int_pow(2, n))",
				// The law's ∀-form absorbs its own instance at the install.
				By(CongNeg))
			subAsNegAdd := a.Have(
				"in ℤ, adding the negation is subtracting: the group laws restore x after the detour",
				"int_of_word(n, x) - int_of_word(n, y) = int_of_word(n, x) + int_neg(int_of_word(n, y))",
				By(
					// x - y = s ⇔ x = s + y, at s the neg-add form
					At(int_real_lift.EqSubRightAdd, readX, a.Term("int_of_word(n, y)"), negAddForm),
					// (x + -y) + y = x + (-y + y) = x + 0 = x
					At(int_real_lift.AddAssoc, readX, negReadY, a.Term("int_of_word(n, y)")),
					At(int_real_lift.AddLeftInverse, a.Term("int_of_word(n, y)")),
					int_real_lift.AddRightIdentity))
			a.Show(
				"compose the two laws under the congruence and read the sum back as the difference",
				By(
					viaAdd,
					negReading,
					subAsNegAdd,
					// x's reading stays put while the negation leg advances
					At(int_congruence.AddCongruent, readX, readX, readNegY, negReadY, modulus),
					At(int_congruence.CongruentIffSameRem, readX, readX, modulus),
					At(int_congruence.CongruentIffSameRem, readSub, sumForm, modulus),
					At(int_congruence.CongruentIffSameRem, sumForm, negAddForm, modulus),
					At(int_congruence.CongruentIffSameRem, readSub, subForm, modulus)))
		}),
})}

// ---------------------------------------------------------------------------
// The complement identity
// ---------------------------------------------------------------------------

// IntOfWordNot — the complement reads as the negated reading stepped one
// back, for every x, at every positive width. The guard is load-bearing:
// at width zero the left side is -1 and the right is 0.
//
// The complement only reads bits below the width, so it cannot tell x
// from its residue; on the residue it computes outright to the mask less
// the residue (`bit_arith.ValNot`), which puts the complement, the residue
// and one place between them at the range exactly. Crossed into ℤ, that
// sum makes the two sides of the claim congruent modulo the range — the
// same multiple witnesses the sum vanishing and the difference being a
// multiple. And both sides keep to the reading's half-open window, whose
// full width is the range, so the congruence over a smaller gap is an
// equality.
var IntOfWordNot = intOfWordNotThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordNot",
	Key:  "prop_5197ff650def2ab5",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "-(int_of_word(n, x) + 1) = int_of_word(n, word_not(n, x))",
		},
		func(a *Argument, n, x Term, widthPos Fact) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			one := a.Ctx().Numeral(1)

			size := a.Term("nat_pow(2, n)")
			topMask := a.Term("nat_pow(2, n) - 1")
			residue := a.Term("rem(x, nat_pow(2, n))")
			modulus := a.Term("int_pow(2, n)")
			halfRange := a.Term("int_pow(2, n - 1)")
			intZero, intOne := a.TermAs[Int]("0"), a.TermAs[Int]("1")
			notOp := a.Term("(λa:bool. ¬a)") // the window combinator's ¬, as word_not's definition applies it

			complement := a.Term("word_not(n, x)")
			readNot := a.Term("int_of_word(n, word_not(n, x))")
			readX := a.Term("int_of_word(n, x)")
			stepped := a.Term("int_of_word(n, x) + 1")
			negStepped := a.Term("-(int_of_word(n, x) + 1)")
			readSum := a.Term("int_of_word(n, word_not(n, x)) + (int_of_word(n, x) + 1)")
			embSum := a.Term("word_not(n, x) + (rem(x, nat_pow(2, n)) + int_of_num(1))")

			bitsAgree := a.Have(
				"the complement reads only bits below the width, and those cannot tell x from its residue",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ word_bit(k, word_not(n, rem(x, nat_pow(2, n))))",
				Derive(func(b *Argument) {
					k := b.Fix()
					// ↦ word_bit(k, word_bitwise_unary(n, ¬, x)) ⇔ word_bit(k, word_bitwise_unary(n, ¬, nat_mod(x, 2ⁿ)))
					b.Do(Unfold(machine_word.WordNotDef))
					defRead := b.Have(
						"the bit, read off its definition",
						"word_bit(k, x) ⇔ nat_odd(div(x, nat_pow(2, k)))",
						By(wordBitDef))
					b.Show(
						"either combinator holds k exactly when k sits below the width "+
							"and x leaves it clear — the reduction changes neither part",
						By(
							defRead,
							At(word_bits.BitwiseUnaryProjection, n, notOp, x, k),
							At(word_bits.BitwiseUnaryProjection, n, notOp, residue, k),
							word_bits.BitWord))
				}))
			residueRead := a.Have(
				"so the complement cannot tell x from its residue",
				"word_not(n, x) = word_not(n, rem(x, nat_pow(2, n)))",
				By(bitsAgree, At(word_bits.BitsEqAll, complement, a.Term("word_not(n, rem(x, nat_pow(2, n)))"))))

			// The range, a power of two, is never zero: nat_pow(2, n) ≠ 0.
			nz := At(nat_arith.PowTwoNonzero, n)
			rBound := a.Have(
				"so the residue sits below the range",
				"rem(x, nat_pow(2, n)) < nat_pow(2, n)",
				By(nz, At(nat_div_mod.Division, x, size)))
			notVal := a.Have(
				"and on the residue the complement computes outright: the mask less the residue",
				"word_not(n, x) = nat_pow(2, n) - 1 - rem(x, nat_pow(2, n))",
				By(residueRead, rBound, At(bit_arith.ValNot, n, residue)))
			nSum := a.Have(
				"so the complement, the residue and one place between them come "+
					"to the range exactly — the monus cancellations count it out",
				"word_not(n, x) + (rem(x, nat_pow(2, n)) + 1) = nat_pow(2, n)",
				By(
					nz,
					rBound,
					notVal,
					// the residue keeps to the mask: r < 2ⁿ = suc(2ⁿ - 1)
					At(nat_monus.SucOfSubOne, size),
					At(nat_order.LessThanSucIffLessEq, residue, topMask),
					// so taking it off the mask and putting it back cancels,
					At(nat_monus.SubAddCancel, topMask, residue),
					// as does the mask's own missing place,
					At(nat_monus.SubAddCancel, size, one),
					At(nat_order.PosIffNonzero, size),
					At(nat_order.OneLessEqIffPos, size),
					// once the sum is grouped around the complement.
					At(nat_arith.AddAssoc, complement, residue, one)))
			iSum := a.Have(
				"the embedding splits that sum place by place, so in ℤ the three images come to the range as well",
				"word_not(n, x) + (rem(x, nat_pow(2, n)) + &1) = int_pow(2, n)",
				// Bare: the ∀-law rewrites both nested sums where they stand.
				By(int_embed.OfNumAdd, nSum, int_pow.OfNumPow))

			congV := a.Have(
				"x's reading is congruent to its residue's image — the reading works through the residue",
				"int_of_word(n, x) ≡ rem(x, nat_pow(2, n)) (mod int_pow(2, n))",
				By(
					At(IntOfWordValCong, n, x),
					At(nat_congruence.ResidueCongruent, x, size),
					At(int_congruence.OfNumCongruent, residue, x, size),
					int_pow.OfNumPow,
					At(int_congruence.CongruentIffSameRem, readX, a.TermAs[Int]("x"), modulus),
					At(
						int_congruence.CongruentIffSameRem,
						a.Term("int_of_num(rem(x, nat_pow(2, n)))"),
						a.TermAs[Int]("x"),
						modulus),
					At(
						int_congruence.CongruentIffSameRem, readX, a.Term("int_of_num(rem(x, nat_pow(2, n)))"), modulus)))
			modZero := a.Have(
				"the range itself is congruent to zero — it exceeds zero by exactly one copy of itself",
				"int_pow(2, n) ≡ 0 (mod int_pow(2, n))",
				By(
					At(int_congruence.CongruentIffMultiple, modulus, intZero, modulus),
					int_real_lift.SubRightZero,
					At(int_real_lift.MulRightIdentity, modulus)))
			sumZero := a.Have(
				"so the complement's reading, x's reading and one place sum to zero modulo the range",
				"int_of_word(n, word_not(n, x)) + (int_of_word(n, x) + 1) ≡ 0 (mod int_pow(2, n))",
				By(
					iSum,
					modZero,
					congV,
					At(IntOfWordValCong, n, complement),
					At(int_congruence.AddCongruent,
						readNot, a.Term("int_of_num(word_not(n, x))"),
						stepped, a.Term("int_of_num(rem(x, nat_pow(2, n))) + int_of_num(1)"), modulus),
					At(int_congruence.AddCongruent,
						readX, a.Term("int_of_num(rem(x, nat_pow(2, n)))"),
						intOne, intOne, modulus),
					At(int_congruence.CongruentIffSameRem, intOne, intOne, modulus),
					At(int_congruence.CongruentIffSameRem, readSum, embSum, modulus),
					At(int_congruence.CongruentIffSameRem, modulus, intZero, modulus),
					At(int_congruence.CongruentIffSameRem, readSum, intZero, modulus)))
			congLR := a.Have(
				"summing to zero makes the two sides of the claim congruent — one multiple witnesses both",
				"int_of_word(n, word_not(n, x)) ≡ -(int_of_word(n, x) + 1) (mod int_pow(2, n))",
				By(
					sumZero,
					At(int_congruence.CongruentIffMultiple, readSum, intZero, modulus),
					At(int_congruence.CongruentIffMultiple, readNot, negStepped, modulus),
					At(int_real_lift.SubRightNeg, readNot, stepped),
					int_real_lift.SubRightZero))

			doublingNat := rangeDoubling(a, widthPos)
			doubling := a.Have(
				"and the embedding carries the doubling across",
				"int_pow(2, n) = int_pow(2, n - 1) + int_pow(2, n - 1)",
				By(doublingNat, int_embed.OfNumAdd, int_pow.OfNumPow))
			span := a.Have(
				"both sides keep to the reading's half-open window, so "+
					"neither stands a full doubled half-range from the other",
				"-(int_of_word(n, x) + 1) - (int_pow(2, n - 1) + int_pow(2, n - 1)) < "+
					"int_of_word(n, word_not(n, x)) ∧ "+
					"int_of_word(n, word_not(n, x)) < "+
					"-(int_of_word(n, x) + int_of_num(1)) + (int_pow(2, n - 1) + int_pow(2, n - 1)) ∧ "+
					"int_of_num(0) < int_pow(2, n - 1) + int_pow(2, n - 1)",
				// The half range is NAMED for the close: the linear closer
				// works over opaque quantities and a power is not one of
				// them.
				ByArith(
					DenotedAs("halfRange", halfRange),
					At(IntOfWordBound, n, x),
					At(IntOfWordBound, n, complement)))
			gap := a.Have(
				"so their difference is smaller than the range",
				"|int_of_word(n, word_not(n, x)) - -(int_of_word(n, x) + 1)| < int_pow(2, n)",
				By(doubling, span, At(int_real_lift.AbsBetween, negStepped, readNot, modulus)))
			a.Show(
				"and a congruence over a gap smaller than its modulus is an equality",
				By(gap, congLR, At(int_congruence.EqOfSmallDifference, readNot, negStepped, modulus)))
		}),
})}
