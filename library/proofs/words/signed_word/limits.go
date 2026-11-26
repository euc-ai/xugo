// limits.go — the C semantics' extremal constants of a width — the
// limit words as ground values, and their signed readings: INT_MIN's
// value, word form and bit table, INT_MAX's word form, UINT_MAX's
// value and bound; then the limits read back through the round trip,
// the two-limit bound on every reading, and the ground readings at
// the window's inner edge (the reading of 1, and the words that read
// as −1).

package signed_word

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_congruence"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_embed"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/words/bit_arith"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The limit words as ground values
// ---------------------------------------------------------------------------
//
// The C semantics' extremal constants of a width, read through the
// chapter's constructor. One argument carries the INT_MIN members:
// −2ⁿ⁻¹ and +2ⁿ⁻¹ differ by exactly one range — the doubling
// 2ⁿ = 2ⁿ⁻¹ + 2ⁿ⁻¹, which is where the width guard earns its keep (at
// n = 0 the built word is 0 and the half range is 1) — so the
// constructor cannot tell them apart, and on the embedded half range
// it computes outright. BitPowTwo then identifies the top place in
// INT_MIN's bit table.

// rangeDoubling derives the width guard's one dividend — the whole
// range is the half range twice over: 1 ≤ n gives the power a place to
// be raised from, and raising by one place doubles. Callable only at a
// fix literally named n — the claim texts pin the name, so a parameter
// would promise a generality the literal-text contract cannot deliver.
func rangeDoubling(a *Argument, widthPos Fact) Fact {
	n := a.Term("n")
	one := a.Ctx().Numeral(1)
	topPlace := a.Term("n - 1")
	return a.Have(
		"the whole range is the half range twice over — the width has a place to raise the power from",
		"nat_pow(2, n) = nat_pow(2, n - 1) + nat_pow(2, n - 1)",
		By(
			widthPos,
			At(nat_monus.SubAddCancel, n, one), // (n - 1) + 1 = n
			At(nat_arith.Add1, topPlace),       // suc(n - 1) = (n - 1) + 1
			// Bare — its ∀-form closes the goal at the install.
			nat_arith.PowTwoSuc)) // 2ᵏ + 2ᵏ = 2^suc(k), at the top place
}

// halfPositive derives that the half range is positive — a power of
// two never vanishes, at any width, the top place n − 1 included.
// Callable only at a fix literally named n, as rangeDoubling.
func halfPositive(a *Argument) Fact {
	topPlace := a.Term("n - 1")
	halfNat := a.Term("nat_pow(2, n - 1)")
	return a.Have(
		"the half range is a power of two, so it does not vanish — which on ℕ is to lie above zero",
		"0 < nat_pow(2, n - 1)",
		By(At(nat_arith.PowTwoNonzero, topPlace), At(nat_order.PosIffNonzero, halfNat)))
}

// halfBelowRange turns the doubling into the strict bound the residue
// collapse wants: positive and doubled is strictly more.
func halfBelowRange(a *Argument, doubling Fact) Fact {
	zero := a.Ctx().Numeral(0)
	halfNat := a.Term("nat_pow(2, n - 1)")
	halfPos := halfPositive(a)
	return a.Have(
		"topped up by its positive self, the half range moves "+
			"strictly up — to the whole range, by the doubling",
		"nat_pow(2, n - 1) < nat_pow(2, n)",
		By(
			halfPos,
			doubling,
			nat_order.LessEqRefl,
			// h ≤ h ∧ 0 < h ⇒ h + 0 < h + h
			At(nat_order.LessEqLessThanAdd2, halfNat, zero, halfNat, halfNat),
			// bare: h + 0 ↦ h on the left
			nat_arith.AddZero))
}

// IntMinValue — INT_MIN's value IS the half range: the word built from
// −2ⁿ⁻¹ is the number 2ⁿ⁻¹. The guard is load-bearing — at n = 0 the
// built word is 0 and the half range is 1.
//
// The two sources differ by exactly one range — the doubling, carried
// into ℤ, cancels −2ⁿ⁻¹ against half of 2ⁿ and leaves the other half —
// so they are congruent and build one word (`WordOfIntEq`). On the
// embedded half range the constructor is the unsigned reduction
// (`WordOfIntOfNum`), and below the range — the doubling again, read as a
// strict bound — the residue forgets nothing.
var IntMinValue = intMinValueThm{family.Add(registry.ProofEntry{
	Name: "IntMinValue",
	Key:  "prop_9e0e4d3059deabb0",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "word_of_int(n, -int_pow(2, n - 1)) = nat_pow(2, n - 1)",
		},
		func(a *Argument, n Term, widthPos Fact) {
			half := a.Term("int_pow(2, n - 1)")
			negHalf := a.Term("-int_pow(2, n - 1)")
			halfNat := a.Term("nat_pow(2, n - 1)")
			halfImage := a.Term("int_of_num(nat_pow(2, n - 1))")
			width := a.Term("nat_pow(2, n)")
			modulus := a.Term("int_pow(2, n)")
			intZero := a.TermAs[Int]("0")
			// the two sides of the stepping-up congruence below
			steppedUp := a.Term("-int_pow(2, n - 1) + int_pow(2, n)")
			steppedZero := a.Term("-int_pow(2, n - 1) + 0")

			doublingNat := rangeDoubling(a, widthPos)
			doubling := a.Have(
				"and the embedding carries the doubling across, the powers crossing by themselves",
				"int_pow(2, n) = int_pow(2, n - 1) + int_pow(2, n - 1)",
				By(doublingNat, int_embed.OfNumAdd, int_pow.OfNumPow))
			modZero := a.Have(
				"the range itself is congruent to zero — it exceeds 0 by exactly one copy of itself",
				"int_pow(2, n) ≡ 0 (mod int_pow(2, n))",
				By(
					// modulus ≡ int_of_num(0) ⇔ ∃d. modulus - int_of_num(0) = modulus * d
					At(int_congruence.CongruentIffMultiple, modulus, intZero, modulus),
					// modulus - int_of_num(0) = modulus
					int_real_lift.SubRightZero,
					// modulus * int_of_num(1) = modulus — the copy exhibited
					At(int_real_lift.MulRightIdentity, modulus)))
			neutralize := a.Have(
				"one range up from INT_MIN is the half range: the doubling "+
					"splits the range, the group laws cancel the inverse half",
				"-int_pow(2, n - 1) + int_pow(2, n) = nat_pow(2, n - 1)",
				By(
					doubling,
					// -h + (h + h) = (-h + h) + h
					At(int_real_lift.AddAssoc, negHalf, half, half),
					// -h + h = int_of_num(0)
					At(int_real_lift.AddLeftInverse, half),
					// int_of_num(0) + h = h
					At(int_real_lift.AddLeftIdentity, half),
					// bare: &(nat_pow(2, n - 1)) and int_pow(&2, n - 1) identified
					int_pow.OfNumPow))
			cong := a.Have(
				"so INT_MIN is congruent to the embedded half range — stepping "+
					"both by the zero-congruent range carries one onto the other",
				"-int_pow(2, n - 1) ≡ nat_pow(2, n - 1) (mod int_pow(2, n))",
				By(
					neutralize,
					modZero,
					// -h ≡ -h ⇒ modulus ≡ int_of_num(0) ⇒ -h + modulus ≡ -h + int_of_num(0)
					At(int_congruence.AddCongruent, negHalf, negHalf, modulus, intZero, modulus),
					// -h ≡ -h, read as its (reflexive) equality of remainders
					At(int_congruence.CongruentIffSameRem, negHalf, negHalf, modulus),
					// -h + int_of_num(0) = -h
					At(int_real_lift.AddRightIdentity, negHalf),
					// the stepped congruence and the claim, each as an
					// equality of remainders — the two resident equations
					// chain them into one another
					At(int_congruence.CongruentIffSameRem, steppedUp, steppedZero, modulus),
					At(int_congruence.CongruentIffSameRem, negHalf, halfImage, modulus)))
			sameWord := a.Have(
				"and congruent sources build one word",
				"word_of_int(n, -int_pow(2, n - 1)) = word_of_int(n, nat_pow(2, n - 1))",
				// The equivalence goes in bare: its ∀-form absorbs the
				// resident congruence and lands as the equality of builds.
				By(cong, WordOfIntEq))

			halfLt := halfBelowRange(a, doublingNat)
			a.Show(
				"on the embedded half range the constructor is the unsigned "+
					"reduction, and below the range the residue forgets nothing",
				By(
					sameWord,
					halfLt,
					// word_of_int(n, int_of_num(nat_pow(2, n - 1))) = nat_mod(nat_pow(2, n - 1), nat_pow(2, n))
					At(WordOfIntOfNum, n, halfNat),
					// nat_mod(nat_pow(2, n - 1), nat_pow(2, n)) = nat_pow(2, n - 1)
					At(nat_div_mod.ModLessThan, halfNat, width)))
		}),
})}

// IntMinAsWord — the built word, spelled as word(2ⁿ⁻¹) — the nat_mod
// is word(·)'s translation and is not reducible away in the statement.
// Nothing new is proved: the value member says the word is the half
// range, and the same residue collapse that closed it, read the other
// way, says the half range is what the nat_mod spells.
var IntMinAsWord = intMinAsWordThm{family.Add(registry.ProofEntry{
	Name: "IntMinAsWord",
	Key:  "prop_6b85bdbc11a9e06f",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "word_of_int(n, -int_pow(2, n - 1)) = rem(nat_pow(2, n - 1), nat_pow(2, n))",
		},
		func(a *Argument, n Term, widthPos Fact) {
			halfNat := a.Term("nat_pow(2, n - 1)")
			width := a.Term("nat_pow(2, n)")

			doublingNat := rangeDoubling(a, widthPos)
			halfLt := halfBelowRange(a, doublingNat)
			a.Show(
				"the built word is the half range, which below the range is "+
					"its own residue — the nat_mod spells it, forgetting nothing",
				By(
					halfLt,
					widthPos,
					// word_of_int(n, -int_pow(int_of_num(2), n - 1)) = nat_pow(2, n - 1)
					At(IntMinValue, n),
					// nat_mod(nat_pow(2, n - 1), nat_pow(2, n)) = nat_pow(2, n - 1)
					At(nat_div_mod.ModLessThan, halfNat, width)))
		}),
})}

// IntMaxAsWord — INT_MAX's word, in word(·) form: built
// from 2ⁿ⁻¹ − 1, it is word(2ⁿ⁻¹ − 1). The source is NONNEGATIVE —
// the half range is at least one at every width, the guard included
// for the chapter's uniform limit shape — so the subtraction happens
// among the numbers, crosses back through the embedding, and the
// constructor on an embedded number is the unsigned reduction
// (`WordOfIntOfNum`). Mind the two subtractions: the ℤ side's is genuine,
// the ℕ side's is monus — benign exactly because 1 ≤ 2ⁿ⁻¹.
var IntMaxAsWord = intMaxAsWordThm{family.Add(registry.ProofEntry{
	Name: "IntMaxAsWord",
	Key:  "prop_9262a6b8da044d5b",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n:num.",
			Conclusion: "word_of_int(n, int_pow(2, n - 1) - 1) = rem(nat_pow(2, n - 1) - 1, nat_pow(2, n))",
		},
		func(a *Argument, n Term) {
			one := a.Ctx().Numeral(1)
			halfNat := a.Term("nat_pow(2, n - 1)")

			halfPos := halfPositive(a)
			crossing := a.Have(
				"with at least one to take, the subtraction happens among the numbers and crosses back as an image",
				"int_pow(2, n - 1) - 1 = nat_pow(2, n - 1) - 1",
				By(
					halfPos,
					// 1 ≤ nat_pow(2, n - 1) — positivity, read as the guard
					At(nat_order.OneLessEqIffPos, halfNat),
					// 1 ≤ h ⇒ &h - &1 = &(h - 1)
					At(int_embed.OfNumSub, one, halfNat),
					// bare: &(nat_pow(2, n - 1)) and int_pow(&2, n - 1) identified
					int_pow.OfNumPow))
			a.Show(
				"and on the embedded number the constructor is the unsigned reduction — the nat_mod form exactly",
				// WordOfIntOfNum goes in bare: its ∀-form lands as the rewrite
				// computing the build of the crossed source.
				By(crossing, WordOfIntOfNum))
		}),
})}

// UintMaxValue — UINT_MAX is its own value: the mask 2ⁿ − 1 is its own
// residue by the range. Fully unguarded — at n = 0 the mask is 0 and
// every residue mod 1 is 0.
//
// The range does not vanish, so the mask — one short of it — sits
// strictly below it: suc(2ⁿ − 1) = 2ⁿ counts the missing one back, and
// a value below the modulus is its own residue.
var UintMaxValue = uintMaxValueThm{family.Add(registry.ProofEntry{
	Name: "UintMaxValue",
	Key:  "prop_4bc816ce906fe3",
	Build: family.Theorem(
		"∀n:num. rem(nat_pow(2, n) - 1, nat_pow(2, n)) = nat_pow(2, n) - 1",
		func(a *Argument, n Term) {
			width := a.Term("nat_pow(2, n)")
			mask := a.Term("nat_pow(2, n) - 1")

			maskLt := a.Have(
				"the range, a power of two, is never zero, so the mask — one short of it — sits strictly below it",
				"nat_pow(2, n) - 1 < nat_pow(2, n)",
				By(
					At(nat_arith.PowTwoNonzero, n),
					// suc(2ⁿ - 1) = 2ⁿ
					At(nat_monus.SucOfSubOne, width),
					// mask < 2ⁿ ⇔ suc(mask) ≤ 2ⁿ
					At(nat_order.SucLessEqIffLessThan, mask, width),
					// bare: 2ⁿ ≤ 2ⁿ closes the step
					nat_order.LessEqRefl))
			a.Show(
				"and below the range the residue forgets nothing",
				By(maskLt, At(nat_div_mod.ModLessThan, mask, width)))
		}),
})}

// ValLessEqUintMax — every in-range value sits at or below UINT_MAX,
// the bound stated in its word(·) form, the mask under nat_mod. One cite of
// `UintMaxValue` reads the nat_mod away; what is left is that strictly
// below the range is at most one short of it — the range being
// suc(2ⁿ − 1), a strict bound by it is a weak bound by its predecessor.
var ValLessEqUintMax = valLessEqUintMaxThm{family.Add(registry.ProofEntry{
	Name: "ValLessEqUintMax",
	Key:  "prop_db48468dca5b27d6",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "w ≤ rem(nat_pow(2, n) - 1, nat_pow(2, n))",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			width := a.Term("nat_pow(2, n)")
			mask := a.Term("nat_pow(2, n) - 1")

			a.Show(
				"the bound's nat_mod is the mask, and strictly below suc(mask) is at most the mask",
				By(
					// the never-vanishing range is suc of the mask
					At(nat_arith.PowTwoNonzero, n),
					wBound,
					// bare: the equation lands as the rewrite collapsing the nat_mod
					UintMaxValue,
					// suc(2ⁿ - 1) = 2ⁿ
					At(nat_monus.SucOfSubOne, width),
					// w < suc(mask) ⇔ w ≤ mask
					At(nat_order.LessThanSucIffLessEq, w, mask)))
		}),
})}

// IntMinBits — INT_MIN holds exactly its top bit: IntMinValue reads
// its word as the half range, and BitPowTwo reads that power's bit table.
var IntMinBits = intMinBitsThm{family.Add(registry.ProofEntry{
	Name: "IntMinBits",
	Key:  "prop_9f72e00da18e65d6",
	Build: family.Theorem(
		Statement{
			Binders: "∀n i:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "i = n - 1 ⇔ word_bit(i, word_of_int(n, -int_pow(2, n - 1)))",
		},
		func(a *Argument, n, i *Expr[Nat], widthPos Fact) {
			a.Show(
				"INT_MIN is the power of two at the top place",
				By(widthPos, IntMinValue.At(n), word_bits.BitPowTwo))
		}),
})}

// ---------------------------------------------------------------------------
// The limits, read back
// ---------------------------------------------------------------------------
//
// The window's two limits read back, and the readings at the window's
// inner edge. The engine is `IntRoundTripInRange`: an integer of the
// half-open window builds into a word that reads back as itself, so a
// limit's reading is settled the moment the limit is shown to LIE in
// the window. What varies member to member is only how much of the
// window survives at small widths: the floor needs the width guard
// (at width zero it is −1, outside the unit window), the ceiling does
// not (at width zero it IS the window's single point).

// IntOfWordIntMin — the window's floor reads back exactly: at a positive
// width, −2ⁿ⁻¹ built into a word and read again is −2ⁿ⁻¹. The guard is
// load-bearing — at width zero the floor is −1 and the only reading is
// 0.
//
// One cite of `IntRoundTripInRange` at the floor itself does it, and
// the floor's membership in the window is the cheapest there is: it
// meets its own lower bound by reflexivity, and it lies under the
// ceiling because the half range is positive — a power of two among
// the numbers, carried into ℤ by the embedding, and negated below
// zero.
var IntOfWordIntMin = intOfWordIntMinThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordIntMin",
	Key:  "prop_199fc8af68123a5b",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "-int_pow(2, n - 1) = int_of_word(n, word_of_int(n, -int_pow(2, n - 1)))",
		},
		func(a *Argument, n Term, widthPos Fact) {
			two := a.Ctx().Numeral(2)
			zeroNat := a.Ctx().Numeral(0)
			topPlace := a.Term("n - 1")
			halfNat := a.Term("nat_pow(2, n - 1)")
			half := a.Term("int_pow(2, n - 1)")
			floor := a.Term("-int_pow(2, n - 1)")
			intZero := a.TermAs[Int]("0")

			posNat := halfPositive(a)
			ceiling := a.Have(
				"carried into ℤ and negated, that puts the floor strictly under the ceiling",
				"-int_pow(2, n - 1) < int_pow(2, n - 1)",
				By(
					posNat,
					At(int_embed.OfNumLt, zeroNat, halfNat),
					At(int_pow.OfNumPow, two, topPlace),
					At(int_real_lift.LessEqOfLessThan, intZero, half),
					At(int_real_lift.LessEqNeg2, half, intZero),
					int_real_lift.NegZero,
					At(int_real_lift.LessEqLessThanTrans, floor, intZero, half)))
			a.Show(
				"the floor meets its own bound by reflexivity, so "+
					"it lies in the window, where the round trip is exact",
				By(widthPos, ceiling, At(int_real_lift.LessEqRefl, floor), At(IntRoundTripInRange, n, floor)))
		}),
})}

// IntOfWordIntMax — the window's ceiling steps one back and reads back
// exactly, at EVERY width: 2ⁿ⁻¹ − 1 built into a word and read again
// is 2ⁿ⁻¹ − 1. No guard is owed — at width zero the half range is the
// empty power 1, so the limit is 1 − 1 = 0, the built word is the
// zero word, and the reading is 0.
//
// On a positive width, one cite of `IntRoundTripInRange` at 2ⁿ⁻¹ − 1:
// under the ceiling because stepping one back steps DOWN (zero is
// less than one), and over the floor because the positive half range
// reaches its predecessor from zero, while the negated half range
// hangs below zero — the discreteness of ℤ turning "positive" into
// "at least one".
var IntOfWordIntMax = intOfWordIntMaxThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordIntMax",
	Key:  "prop_d238f2f686c8a07a",
	Build: family.Theorem(
		"∀n:num. int_of_word(n, word_of_int(n, int_pow(2, n - 1) - 1)) = int_pow(2, n - 1) - 1",
		func(a *Argument, n Term) {
			two := a.Ctx().Numeral(2)
			zeroNat := a.Ctx().Numeral(0)
			topPlace := a.Term("n - 1")
			halfNat := a.Term("nat_pow(2, n - 1)")
			half := a.Term("int_pow(2, n - 1)")
			limit := a.Term("int_pow(2, n - 1) - 1")
			floor := a.Term("-int_pow(2, n - 1)")
			intZero, intOne := a.TermAs[Int]("0"), a.TermAs[Int]("1")

			notZero := a.Unless(
				a.Term("n = 0"),
				"n = 0: the half range is the empty power 1, the limit is "+
					"the vanished difference 1 - 1, and both sides compute to it",
				Given(func(z *Argument, isZero Fact) {
					// ↦ every n in the goal becomes 0, and the reading opens
					z.Do(isZero.Rw(), Unfold(IntOfWordDef))
					monus := z.Have(
						"ℕ's monus truncates the empty width's top place to zero",
						"0 - 1 = 0",
						By(nat_monus.SubEqZero, nat_order.ZeroLessEq))
					z.Do(monus.Subst())
					widthEq := z.Have(
						"so the range in play is the empty power, one",
						"nat_pow(2, 0) = 1",
						By(nat_arith.NatPow))
					z.Do(widthEq.Subst())
					pow := z.Have(
						"as is its ℤ twin",
						"int_pow(2, 0) = 1",
						By(int_pow.PowClauses))
					z.Do(pow.Subst())
					z.Show(
						"every residue at modulus one is zero, which sits below one, "+
							"so the reading is zero — the vanished difference on the right",
						By(
							Normalized,
							nat_div_mod.ModOne,
							nat_arith.OneIsSucZero,
							nat_order.ZeroLessThanSuc,
							int_real_lift.SubRefl))
				}))

			widthPos := a.Have(
				"a nonzero width is at least one",
				"1 ≤ n",
				By(notZero, At(nat_order.PosIffNonzero, n), nat_order.OneLessEqIffPos))
			posNat := halfPositive(a)
			posInt := a.Have(
				"carried into ℤ by the embedding",
				"0 < int_pow(2, n - 1)",
				By(posNat, At(int_embed.OfNumLt, zeroNat, halfNat), At(int_pow.OfNumPow, two, topPlace)))
			floorBound := a.Have(
				"positive on a discrete line means at least one, so the limit is "+
					"still not negative — while the negated half range hangs below zero",
				"-int_pow(2, n - 1) ≤ int_pow(2, n - 1) - 1",
				By(
					posInt,
					At(int_embed.Discrete, intZero, half),
					At(int_real_lift.AddLeftIdentity, intOne),
					At(int_real_lift.SubNonneg, half, intOne),
					At(int_real_lift.LessEqNeg2, half, intZero),
					int_real_lift.NegZero,
					At(int_real_lift.LessEqOfLessThan, intZero, half),
					At(int_real_lift.LessEqTrans, floor, intZero, limit)))
			ceiling := a.Have(
				"and stepping one back steps down, so the limit sits strictly under the ceiling",
				"int_pow(2, n - 1) - 1 < int_pow(2, n - 1)",
				By(
					At(int_real_lift.LessThanSubAddRight, half, intOne, half),
					At(int_real_lift.LessThanSelfAddRight, half, intOne),
					int_real_lift.ZeroLessThanOne))
			a.Show(
				"so the limit lies in the window, where the round trip is exact",
				By(widthPos, floorBound, ceiling, At(IntRoundTripInRange, n, limit)))
		}),
})}

// IntOfWordBetweenLimits — every reading sits between the two limits'
// readings, at every width and value: the sharpest form of the
// window bound, stated against the limits AS READ rather than as
// integers, so it survives even where the floor's own round trip
// does not.
//
// `IntOfWordIntMax` above rewrites the upper limit's reading into
// 2ⁿ⁻¹ − 1 with no guard, and `IntOfWordBound`'s strict ceiling lands one
// under it by ℤ's discreteness; the lower limit's reading rewrites by
// `IntOfWordIntMin` where the width guard holds, and is `IntOfWordBound`'s own
// floor. At width zero the case collapses instead of weakening: every
// reading is int_of_num(0), so both bounds are 0 ≤ 0.
var IntOfWordBetweenLimits = intOfWordBetweenLimitsThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordBetweenLimits",
	Key:  "prop_bd71d71d4ed46e51",
	Build: family.Theorem(
		"∀n w:num. "+
			"    int_of_word(n, w) ≤ int_of_word(n, word_of_int(n, int_pow(2, n - 1) - 1)) ∧ "+
			"    int_of_word(n, word_of_int(n, -int_pow(2, n - 1))) ≤ int_of_word(n, w)",
		func(a *Argument, n, w Term) {
			a.Cases(a.Term("n = 0"))
			a.When(
				"n = 0: every width-zero reading is 0, and both bounds are 0 ≤ 0",
				func(z *Argument, isZero Fact) {
					// ↦ every n in the goal becomes 0
					z.Do(isZero.Rw())
					monus := z.Have(
						"ℕ's monus truncates the empty width's top place to zero",
						"0 - 1 = 0",
						By(nat_monus.SubEqZero, nat_order.ZeroLessEq))
					z.Do(monus.Subst())
					unit := z.Have(
						"the range in play is the empty power, one",
						"nat_pow(2, 0) = 1",
						By(nat_arith.NatPow))
					// The reading opens spelling the top place 0 - 1 and the
					// range nat_pow(2, 0) afresh; the two equations reduce
					// every range in sight to 1.
					z.Do(Unfold(IntOfWordDef), monus.Rw(), unit.Rw())
					z.Show(
						"every residue at modulus one is zero, below one, "+
							"so all three readings are 0 — and 0 ≤ 0 twice over",
						By(nat_div_mod.ModOne, nat_arith.OneIsSucZero, nat_order.ZeroLessThanSuc, int_real_lift.LessEqRefl))
				})
			a.Otherwise(
				"1 ≤ n: the limits' readings rewrite to the window's "+
					"edges, and IntOfWordBound holds every reading between them",
				func(b *Argument, notZero Fact) {
					reading := b.Term("int_of_word(n, w)")
					half := b.Term("int_pow(2, n - 1)")
					intOne := b.TermAs[Int]("1")

					widthPos := b.Have(
						"a nonzero width is at least one",
						"1 ≤ n",
						By(notZero, At(nat_order.PosIffNonzero, n), nat_order.OneLessEqIffPos))
					b.Do(SplitConj(
						Case(
							"under the upper limit: the strict ceiling on a discrete line is "+
								"to sit at or under the predecessor — the upper limit's reading",
							By(
								IntOfWordIntMax,
								At(IntOfWordBound, n, w),
								At(int_embed.Discrete, reading, half),
								At(int_real_lift.LessEqSubAddLeft, reading, half, intOne))),
						Case(
							"over the lower limit: under the width guard the lower limit reads as "+
								"the floor itself, which IntOfWordBound puts at or under every reading",
							By(widthPos, IntOfWordIntMin, At(IntOfWordBound, n, w))),
					))
				})
		}),
})}

// IntOfWordOne — the reading of 1 flips sign exactly at width one: at
// n = 1 the word 1 IS the sign bit and reads −1; at every wider width
// the residue 1 sits in the low half and reads as itself.
//
// The split is on the width. At n = 1 everything is a numeral and the
// reading computes: the residue is 1, the half range is the empty
// power 1, the guard 1 < 1 fails, and the reading is 1 − 2 = −1 — the
// one ℤ subtraction crossed through ℕ's 2 − 1 = 1. At n ≥ 2 the half
// range doubles at least once above the bottom, so it clears 2 and the
// guard 1 < 2ⁿ⁻¹ holds: the residue — 1 survives the reduction, the
// range clearing 2 as well — reads as its own image.
var IntOfWordOne = intOfWordOneThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordOne",
	Key:  "prop_a60b247866841c22",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num.",
			Hypotheses: []string{
				"1 ≤ n",
			},
			Conclusion: "int_of_word(n, 1) = COND(1 = n, -int_of_num(1), 1)",
		},
		func(a *Argument, n Term, widthPos Fact) {
			a.Cases(a.Term("n = 1"))
			a.When(
				"n = 1: the word 1 is the sign bit — the guard 1 < 1 fails and the reading is 1 - 2 = -1",
				func(z *Argument, isOne Fact) {
					one, two := z.Ctx().Numeral(1), z.Ctx().Numeral(2)
					intOne, intTwo := z.TermAs[Int]("1"), z.TermAs[Int]("2")

					// ↦ every n becomes 1, and the reading opens; the
					// statement's COND settles to -1 by its refl guard.
					z.Do(isOne.Rw(), Unfold(IntOfWordDef))
					monus := z.Have(
						"the top place of width one is the bottom",
						"1 - 1 = 0",
						By(nat_monus.SubRefl))
					z.Do(monus.Subst())
					widthEq := z.Have(
						"the range is 2",
						"nat_pow(2, 1) = 2",
						By(nat_arith.PowOne))
					z.Do(widthEq.Subst())
					halfRange := z.Have(
						"and the half range is the empty power, one",
						"nat_pow(2, 0) = 1",
						By(nat_arith.NatPow))
					z.Do(halfRange.Subst())
					residue := z.Have(
						"below the range, 1 is its own residue",
						"rem(1, 2) = 1",
						By(
							At(nat_div_mod.ModLessThan, one, two),
							nat_arith.Two,
							At(nat_order.LessThanSucIffLessEq, one, one),
							nat_order.LessEqRefl))
					z.Do(residue.Subst())
					pow := z.Have(
						"the range again, on ℤ's side of the embedding",
						"int_pow(2, 1) = 2",
						By(Normalized, widthEq, At(int_pow.OfNumPow, two, one)))
					z.Do(pow.Subst())
					stepBack := z.Have(
						"one place under 2 is 1 — successors telling each other apart",
						"2 - 1 = 1",
						By(At(nat_monus.SucOfSubOne, two), nat_arith.Two, At(peano.SucNotZero, one), peano.SucInjective))
					corrected := z.Have(
						"so the corrected branch computes: crossed into ℤ, 1 - 2 is the negated 2 - 1",
						"1 - &2 = -int_of_num(1)",
						By(
							Normalized,
							stepBack,
							At(int_embed.OfNumSub, one, two),
							nat_arith.Two,
							At(nat_order.LessThanSucIffLessEq, one, one),
							nat_order.LessEqRefl,
							At(nat_order.LessEqOfLessThan, one, two),
							At(int_real_lift.NegSub, intTwo, intOne)))
					z.Show(
						"the guard 1 < 1 fails, so the reading is the corrected branch",
						By(corrected, nat_order.LessThanIrrefl))
				})
			a.Otherwise(
				"2 ≤ n: the half range doubles above the bottom, so "+
					"it clears 2 and the residue 1 reads as its own image",
				func(b *Argument, notOne Fact) {
					one := b.Ctx().Numeral(1)
					topPlace := b.Term("n - 1")
					halfNat := b.Term("nat_pow(2, n - 1)")
					under := b.Term("nat_pow(2, (n - 1) - 1)")
					width := b.Term("nat_pow(2, n)")

					twoLe := b.Have(
						"at least 1 and not 1 is more than 1 — the width clears 2",
						"2 ≤ n",
						By(
							Normalized,
							notOne,
							widthPos,
							At(nat_order.LessEqSplit, one, n),
							nat_arith.Two,
							At(nat_order.SucLessEqIffLessThan, one, n)))
					oneLeTop := b.Have(
						"so the top place is itself a positive width",
						"1 ≤ n - 1",
						By(
							Normalized,
							twoLe,
							widthPos,
							At(nat_monus.SucOfSubOne, n),
							At(nat_order.PosIffNonzero, n),
							nat_order.OneLessEqIffPos,
							nat_arith.Two,
							At(nat_order.SucLessEqSucIff, one, topPlace)))
					underPlace := b.Term("(n - 1) - 1")
					doublingTop := b.Have(
						"with a place to be raised from, the half range is itself a doubling",
						"nat_pow(2, n - 1) = nat_pow(2, (n - 1) - 1) + nat_pow(2, (n - 1) - 1)",
						By(
							oneLeTop,
							At(nat_monus.SubAddCancel, topPlace, one), // ((n-1) - 1) + 1 = n - 1
							At(nat_arith.Add1, underPlace),            // suc((n-1) - 1) = ((n-1) - 1) + 1
							// Bare — its ∀-form closes the goal at the install.
							nat_arith.PowTwoSuc)) // 2ᵏ + 2ᵏ = 2^suc(k), one place under the top
					underPos := b.Have(
						"of a power of two, which is at least one",
						"1 ≤ nat_pow(2, (n - 1) - 1)",
						By(
							At(nat_arith.PowTwoNonzero, underPlace),
							At(nat_order.PosIffNonzero, under),
							nat_order.OneLessEqIffPos))
					guard := b.Have(
						"so the half range clears 2 = 1 + 1, and the reading's guard 1 < 2ⁿ⁻¹ holds",
						"1 < nat_pow(2, n - 1)",
						By(
							underPos,
							doublingTop,
							At(nat_order.SucLessEqIffLessThan, one,
								b.Term("nat_pow(2, (n - 1) - 1) + nat_pow(2, (n - 1) - 1)")),
							At(nat_order.LessEqAdd2, one, one, under, under),
							nat_arith.Two,
							nat_arith.Add1))
					doubling := rangeDoubling(b, widthPos)
					inRange := b.Have(
						"so 1 lies below the whole range as well, riding the chain through the half",
						"1 < nat_pow(2, n)",
						By(
							guard,
							doubling,
							At(nat_order.LessEqAdd, halfNat, halfNat),
							At(nat_order.LessThanLessEqTrans, one, halfNat, width)))
					residue := b.Have(
						"below the range, 1 is its own residue",
						"rem(1, nat_pow(2, n)) = 1",
						By(inRange, At(nat_div_mod.ModLessThan, one, width)))
					// The reading opens on the residue, which the equation
					// collapses to 1; the guard then selects the uncorrected
					// branch, and the width not being 1 settles the
					// statement's own COND to int_of_num(1).
					b.Show(
						"unfolding the reading, the residue's image is 1 — the uncorrected branch",
						Unfold(IntOfWordDef),
						residue.Rw(),
						By(guard, notOne))
				})
		}),
})}

// IntOfWordEqMinusOne — the words that read −1 are exactly the all-ones
// word: for an in-range value at a positive width, the reading is −1
// precisely when the value is word_neg(n, 1) = 2ⁿ − 1.
//
// The reading tells in-range values apart (`EqByIntOfWord`), so the whole
// content is naming the one in-range value that DOES read −1. It is
// the top value 2ⁿ − 1 — `bit_arith.ValNegOne`'s value for word_neg(n, 1) —
// and its reading computes: the top value is its own residue, it sits
// at or above the half range (the doubling), so the reading is the
// corrected branch, and taking the whole range from the embedded
// 2ⁿ − 1 leaves exactly −1.
var IntOfWordEqMinusOne = intOfWordEqMinusOneThm{family.Add(registry.ProofEntry{
	Name: "IntOfWordEqMinusOne",
	Key:  "prop_3afc9a572c6bfb2f",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"1 ≤ n",
				"w < nat_pow(2, n)",
			},
			Conclusion: "-1 = int_of_word(n, w) ⇔ w = word_neg(n, 1)",
		},
		func(a *Argument, n, w Term, widthPos, wBound Fact) {
			one, two := a.Ctx().Numeral(1), a.Ctx().Numeral(2)
			topPlace := a.Term("n - 1")
			width := a.Term("nat_pow(2, n)")
			top := a.Term("nat_pow(2, n) - 1")
			halfNat := a.Term("nat_pow(2, n - 1)")
			modulus := a.Term("int_pow(2, n)")
			rangeLessOne := a.Term("int_pow(2, n) - 1")
			intOne := a.TermAs[Int]("1")
			negIntOne := a.Term("-int_of_num(1)")
			negOnePlusRange := a.Term("-1 + int_pow(2, n)")

			rangePos := a.Have(
				"the range is a power of two, so it is at least one",
				"1 ≤ nat_pow(2, n)",
				By(At(nat_arith.PowTwoNonzero, n), At(nat_order.PosIffNonzero, width), nat_order.OneLessEqIffPos))
			topInside := a.Have(
				"so its predecessor, the top value, steps back inside it",
				"nat_pow(2, n) - 1 < nat_pow(2, n)",
				By(
					rangePos,
					At(nat_monus.SubAddCancel, width, one),
					At(nat_arith.Add1, top),
					At(nat_order.LessThanSucIffLessEq, top, top),
					nat_order.LessEqRefl))
			residue := a.Have(
				"where it is its own residue",
				"rem(nat_pow(2, n) - 1, nat_pow(2, n)) = nat_pow(2, n) - 1",
				By(topInside, At(nat_div_mod.ModLessThan, top, width)))
			halfPos := a.Have(
				"the half range is a power of two as well, at least one",
				"1 ≤ nat_pow(2, n - 1)",
				By(
					At(nat_arith.PowTwoNonzero, topPlace),
					At(nat_order.PosIffNonzero, halfNat),
					nat_order.OneLessEqIffPos))
			doubling := rangeDoubling(a, widthPos)
			aboveHalf := a.Have(
				"half the range topped up by one keeps within the doubled "+
					"half, so the top value sits at or above the half range",
				"nat_pow(2, n - 1) ≤ nat_pow(2, n) - 1",
				By(
					rangePos,
					halfPos,
					doubling,
					At(nat_monus.SucOfSubOne, width),
					At(nat_order.PosIffNonzero, width),
					nat_order.OneLessEqIffPos,
					At(nat_order.SucLessEqSucIff, halfNat, top),
					nat_arith.Add1,
					At(nat_order.LessEqAdd2, halfNat, one, halfNat, halfNat),
					nat_order.LessEqRefl))
			topImage := a.Have(
				"the top value's image is the range's, one step down — the crossing is exact inside the range",
				"nat_pow(2, n) - 1 = int_pow(2, n) - 1",
				By(rangePos, At(int_embed.OfNumSub, one, width), At(int_pow.OfNumPow, two, n)))
			restored := a.Have(
				"and taking the whole range from it leaves exactly -1 "+
					"— ℤ's group laws restore the range after the detour",
				"(int_pow(2, n) - 1) - int_pow(2, n) = -1",
				By(
					At(int_real_lift.EqSubRightAdd, rangeLessOne, modulus, negIntOne),
					At(int_real_lift.EqSubRightAdd, modulus, intOne, negOnePlusRange),
					At(int_real_lift.AddSym, negOnePlusRange, intOne),
					At(int_real_lift.AddSym, negIntOne, modulus),
					At(int_real_lift.AddAssoc, intOne, negIntOne, modulus),
					At(int_real_lift.AddRightInverse, intOne),
					int_real_lift.AddLeftIdentity))
			// The reading opens on the top value's residue, and the three
			// equations rewrite the corrected branch — the residue into
			// the top value, its image into the ℤ difference, and the
			// difference less the range into -1.
			maxRead := a.Have(
				"so the top value reads -1: its residue is itself, at or "+
					"above the half range, and the corrected branch computes",
				"int_of_word(n, nat_pow(2, n) - 1) = -1",
				Unfold(IntOfWordDef),
				residue.Rw(),
				topImage.Rw(),
				restored.Rw(),
				By(aboveHalf, At(nat_order.NotLessThan, top, halfNat)))
			a.Show(
				"the reading tells in-range values apart, so reading -1 is being "+
					"the top value, the all-ones word, which is what negating 1 builds",
				By(wBound, topInside, maxRead, bit_arith.ValNegOne, At(EqByIntOfWord, n, w, top)))
		}),
})}
