// word_bits.go — the chapter's bit face: a word read one bit at a time.
//
// Bit projection and extensionality read values one position at a
// time. The set builder supplies the common range and bit table for
// finite-window combinators.

package word_bits

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The bits face of the term-level word
// ---------------------------------------------------------------------------
//
// the bits face of the term-level word: word_bit reads position i of the
// VALUE, `word_bit(i, x) = nat_odd(nat_div(x, 2^i))`, and is WIDTH-FREE — which bit of
// x is set is a fact about x alone. The width enters a member here
// solely through the range guards: `1 ≤ n` never carries content (it is
// bound and ignored), and `x < 2^n` is live precisely where a bit position
// is measured against the width (BitTrivial, BitGuard). Everything else is
// the definition read through nat_div_mod's quotient algebra and
// nat_parity's parity of the quotient: a bit is set iff dividing by its
// place value leaves an odd quotient.

// BitLsb — the val-face form: the lowest bit is the value's
// own parity. At position zero the place value is 2^0 = 1, and
// dividing by one changes nothing — read here off DivMult at divisor
// one.
var BitLsb = bitLsbThm{family.Add(registry.ProofEntry{
	Name: "BitLsb",
	Key:  "prop_34af23d5b57e9cce",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x:num.",
			Conclusion: "nat_odd(x) ⇔ word_bit(0, x)",
		},
		func(a *Argument, x Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			one := a.Ctx().Numeral(1)
			divOne := a.Have(
				"dividing by one changes nothing",
				"div(x, 1) = x",
				By(nat_arith.OneNotZero, At(nat_div_mod.DivMult, one, x), nat_arith.OneMul))
			a.Show(
				"at position zero the place value is one, and the bit reads the value's own parity",
				By(Normalized, wordBitDef, nat_arith.NatPow, divOne))
		}),
})}

// BitPowTwo — a power of two holds exactly its own bit position:
// the quotient below it is even, at it is one, and a higher set bit
// would contradict the power's bound by its double.
var BitPowTwo = bitPowTwoThm{family.Add(registry.ProofEntry{
	Name: "BitPowTwo",
	Key:  "prop_e7cf672817793e1e",
	Build: family.Theorem(
		"∀i k:num. word_bit(k, nat_pow(2, i)) ⇔ k = i",
		func(a *Argument, i, k *Expr[Nat]) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")

			a.Cases(a.Term("k < i"))
			a.When(
				"k < i: below the place the quotient is the gap's power — even, so the bit is clear",
				func(c *Argument, below Fact) {
					_, gap := c.Obtain(
						"the strict gap realizes i as k plus a successor",
						"∃d:num. i = k + suc(d)",
						By(below, nat_order.LessThanExists))
					quot := c.Have(
						"the quotient at k is the gap's power",
						"div(nat_pow(2, i), nat_pow(2, k)) = nat_pow(2, suc(d))",
						By(
							nat_arith.PowTwoNonzero.At(k),
							gap,
							nat_arith.PowAdd.At(c.Ctx().Nat(2), k, c.TermAs[Nat]("suc(d)")),
							nat_div_mod.DivMult.At(
								c.TermAs[Nat]("nat_pow(2, k)"), c.TermAs[Nat]("nat_pow(2, suc(d))"))))
					even := c.Have(
						"and a power of two at a positive exponent is even",
						"nat_even(nat_pow(2, suc(d)))",
						// EvenDouble supplies the even base after multiplying by one.
						By(
							nat_parity.EvenPow.At(c.Ctx().Nat(2), c.TermAs[Nat]("suc(d)")),
							nat_parity.EvenDouble.At(c.Ctx().Nat(1)),
							nat_arith.MulOne,
							peano.SucNotZero))
					c.Show(
						"an even quotient is a clear bit, and the place is not k",
						By(even, below, quot, nat_parity.OddIffNotEven, nat_order.LessThanIrrefl, wordBitDef))
				})
			a.Otherwise(
				"¬(k < i): at the place or past it",
				func(c *Argument, outWin Fact) {
					c.Cases(c.Term("k = i"))
					c.When(
						"k = i: at the place itself the quotient is one, and one is odd",
						func(d *Argument, atEdge Fact) {
							d.Show(
								"an odd quotient is a set bit, and the place is k",
								By(
									nat_parity.NatOdd,
									nat_arith.OneIsSucZero,
									atEdge,
									nat_arith.PowTwoNonzero.At(i),
									nat_div_mod.DivRefl.At(d.TermAs[Nat]("nat_pow(2, i)")),
									wordBitDef))
						})
					c.Otherwise(
						"k ≠ i: past the place — a held place would lie below suc(i), and k does not",
						func(d *Argument, offEdge Fact) {
							powI := d.TermAs[Nat]("nat_pow(2, i)")
							pos := d.Have(
								"the power is positive, being never zero",
								"0 < nat_pow(2, i)",
								By(nat_arith.PowTwoNonzero.At(i), nat_order.PosIffNonzero))
							half := d.Have(
								"the power sits strictly below its own double",
								"nat_pow(2, i) < nat_pow(2, suc(i))",
								By(
									pos,
									nat_order.LessEqRefl,
									nat_order.LessEqLessThanAdd2.At(
										powI, d.Ctx().Nat(0), powI, powI),
									nat_arith.AddZero.At(powI),
									nat_arith.PowTwoSuc))
							capped := d.Have(
								"so every place the power holds lies below suc(i)",
								"∀j:num. word_bit(j, nat_pow(2, i)) ⇒ j < suc(i)",
								// The bound grounds at the claim's own place.
								By(half, BitBelowBound))
							d.Show(
								"a held k would sit below suc(i), that is at most i — and both ways below i are shut",
								By(offEdge, outWin, capped.At(k), nat_order.LessThanSucIffLessEq, nat_order.LessEqSplit))
						})
				})
		}),
})}

// BitTrivial — the val-face form: a bounded value has no
// bits at or beyond its width. This is the one member whose range
// guard is the argument itself: past the width the place value outruns
// the value (monotonicity through the guard), the quotient vanishes,
// and zero is even.
var BitTrivial = bitTrivialThm{family.Add(registry.ProofEntry{
	Name: "BitTrivial",
	Key:  "prop_84c6cacf67120954",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w i:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "¬(n ≤ i) ∨ ¬word_bit(i, w)",
		},
		func(a *Argument, n, w, i Term, wBound Fact) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			placeValue := a.Term("nat_pow(2, i)")
			outrun := a.Have(
				"at or past the width, the place value outruns the value",
				"n ≤ i ⇒ w < nat_pow(2, i)",
				Derive(func(b *Argument) {
					le := b.Assume()
					b.Do(By(
						le,
						wBound,
						At(nat_order.PowTwoMonotone, n, i),
						At(nat_order.LessThanLessEqTrans,
							w, a.Term("nat_pow(2, n)"), placeValue)))
				}))
			vanish := a.Have(
				"so the quotient there vanishes",
				"n ≤ i ⇒ div(w, nat_pow(2, i)) = 0",
				Derive(func(b *Argument) {
					le := b.Assume()
					b.Do(By(le, outrun, At(nat_arith.PowTwoNonzero, i), At(nat_div_mod.DivEqZero, w, placeValue)))
				}))
			a.Show(
				"and zero is even, so no bit is set there",
				By(Normalized, vanish, wordBitDef, nat_parity.NatOdd))
		}),
})}

// BitGuard — the val-face form: on a bounded value, the bit
// predicate carries its own range guard — a set bit is a bit the width
// admits. Propositional once BitTrivial says the bits at or past the
// width are clear: the failed guard IS BitTrivial's antecedent, read
// through order duality.
var BitGuard = bitGuardThm{family.Add(registry.ProofEntry{
	Name: "BitGuard",
	Key:  "prop_2e5fd0f1e2862561",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x i:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_bit(i, x) ⇔ i < n ∧ word_bit(i, x)",
		},
		func(a *Argument, n, x, i Term, xBound Fact) {
			a.Show(
				"a bit the width rejects is clear, and the guard absorbs into the conjunction",
				By(xBound, At(BitTrivial, n, x, i), nat_order.NotLessThan))
		}),
})}

// BitWordZero — the val-face form: the zero word has no
// bits. Every quotient of zero is zero, and zero is even.
var BitWordZero = bitWordZeroThm{family.Add(registry.ProofEntry{
	Name: "BitWordZero",
	Key:  "prop_2c4280fe719c2a56",
	Build: family.Theorem(
		Statement{
			Binders:    "∀i:num.",
			Conclusion: "¬word_bit(i, 0)",
		},
		func(a *Argument, i Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			a.Show(
				"every quotient of zero is zero, and zero is even",
				By(Normalized, wordBitDef, At(nat_div_mod.ZeroDiv, a.Term("nat_pow(2, i)")), nat_parity.NatOdd))
		}),
})}

// BitWordOne — the val-face form: the word one has exactly
// its lowest bit. At position zero the bit reads one's own parity; at
// a nonzero position the place value is already at least two, one's
// quotient vanishes, and zero is even.
var BitWordOne = bitWordOneThm{family.Add(registry.ProofEntry{
	Name: "BitWordOne",
	Key:  "prop_49c9140a72ddef2b",
	Build: family.Theorem(
		Statement{
			Binders:    "∀i:num.",
			Conclusion: "i = 0 ⇔ word_bit(i, 1)",
		},
		func(a *Argument, i Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			one := a.Ctx().Numeral(1)
			placeValue := a.Term("nat_pow(2, i)")
			nonzero := a.Unless(
				a.Term("i = 0"),
				"i = 0: the bit reads one's own parity, and one is odd",
				Given(func(z *Argument, isZero Fact) {
					oddOne := z.Have(
						"one is odd",
						"nat_odd(1)",
						By(nat_parity.NatOdd, nat_arith.OneIsSucZero))
					selfDiv := z.Have(
						"one divided by one is one",
						"div(1, 1) = 1",
						By(nat_arith.OneNotZero, At(nat_div_mod.DivRefl, one)))
					z.Show(
						"at position zero the place value is one",
						By(isZero, wordBitDef, nat_arith.NatPow, selfDiv, oddOne))
				}))
			twoLe := a.Have(
				"so its place value, a positive power of two, is at least two",
				"2 ≤ nat_pow(2, i)",
				By(nonzero, nat_order.PosIffNonzero, At(nat_order.LessEqSelfPow, a.Term("2"), i)))
			oneShort := a.Have(
				"which one falls short of",
				"1 < nat_pow(2, i)",
				By(twoLe, nat_arith.Two, At(nat_order.SucLessEqIffLessThan, one, placeValue)))
			vanish := a.Have(
				"so one's quotient there vanishes",
				"div(1, nat_pow(2, i)) = 0",
				By(oneShort, At(nat_arith.PowTwoNonzero, i), At(nat_div_mod.DivEqZero, one, placeValue)))
			a.Show(
				"and zero is even — both sides fail together",
				By(nonzero, vanish, wordBitDef, nat_parity.NatOdd))
		}),
})}

// ---------------------------------------------------------------------------
// Bits of a reduction
// ---------------------------------------------------------------------------
//
// Both members spend nat_div_mod.DivMod — dividing a residue is reducing a
// quotient — which is what carries a place value PAST a reduction: word_bit
// read through the word injection nat_mod(·, 2^n') is word_bit of the raw value
// guarded by the width (BitWord), and the k-th bit alone decides whether
// the (k+1)-bit residue reaches its top place value (BitValMod). As
// everywhere on the bits face, word_bit is width-free and the width enters
// only through the range guards.

// BitWord — the bits of a reduced value: reducing mod 2^n' keeps every
// bit the width admits and clears the rest. The position measures
// against the width, and the two sides of that comparison argue
// differently:
//
//	i < n' the width's place value factors through the position's
//	 (the gap n' − i tops i back up, nat_arith.PowAdd splits the
//	 power), so nat_div_mod.DivMod turns dividing the residue
//	 into reducing the quotient — and reducing by a power of
//	 two with a nonzero exponent is invisible to parity
//	 (nat_parity.OddModPowTwo).
//	¬(i < n') the residue sits below the width's place value
//	 (Division's bound), which the position's has outrun
//	 (nat_order.PowTwoMonotone through the failed guard) — so the
//	 quotient vanishes, zero is even, and the right side's
//	 guard conjunct fails with it.
var BitWord = bitWordThm{family.Add(registry.ProofEntry{
	Name: "BitWord",
	Key:  "prop_c2ace1db85b714b9",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n' i n:num.",
			Conclusion: "word_bit(i, rem(n, nat_pow(2, n'))) ⇔ nat_odd(div(n, nat_pow(2, i))) ∧ i < n'",
		},
		func(a *Argument, np, i, n Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")

			a.Cases(a.Term("i < n'"))
			a.When(
				"i < n': the width's place value factors through the "+
					"position's, and DivMod carries the bit past the reduction",
				func(b *Argument, inRange Fact) {
					gap := b.Term("n' - i")

					le := b.Have(
						"the position sits inside the width",
						"i ≤ n'",
						By(inRange, At(nat_order.LessEqOfLessThan, i, np)))
					split := b.Have(
						"so the gap tops it back up",
						"(n' - i) + i = n'",
						By(le, At(nat_monus.SubAddCancel, np, i)))
					factor := b.Have(
						"and the width's place value factors through the position's",
						"nat_pow(2, n') = nat_pow(2, i) * nat_pow(2, n' - i)",
						By(split, At(nat_arith.AddSym, gap, i), nat_arith.PowAdd))
					gapNz := b.Have(
						"a gap under a strict bound is not zero",
						"¬(n' - i = 0)",
						By(inRange, nat_monus.SubEqZero, At(nat_order.NotLessEq, np, i)))
					interchange := b.Have(
						"dividing the residue is reducing the quotient",
						"div(rem(n, nat_pow(2, n')), nat_pow(2, i)) = rem(div(n, nat_pow(2, i)), nat_pow(2, n' - i))",
						By(factor, At(nat_div_mod.DivMod, n, b.Term("nat_pow(2, i)"), b.Term("nat_pow(2, n' - i)"))))
					b.Show(
						"reducing by a nonzero power of two is invisible to parity, and the guard is true",
						By(
							inRange,
							interchange,
							gapNz,
							wordBitDef,
							At(nat_parity.OddModPowTwo,
								b.Term("div(n, nat_pow(2, i))"), gap)))
				})
			a.Otherwise(
				"¬(i < n'): the position's place value has outrun "+
					"the residue, so the quotient vanishes with the guard",
				func(b *Argument, outRange Fact) {
					wide := b.Have(
						"the width is at or below the position",
						"n' ≤ i",
						// Bare: the duality fires on the goal as the
						// rewrite it is.
						By(outRange, nat_order.NotLessThan))
					below := b.Have(
						"the residue sits below the width's place value",
						"rem(n, nat_pow(2, n')) < nat_pow(2, n')",
						By(At(nat_arith.PowTwoNonzero, np), At(nat_div_mod.Division, n, b.Term("nat_pow(2, n')"))))
					outrun := b.Have(
						"which the position's has outrun",
						"rem(n, nat_pow(2, n')) < nat_pow(2, i)",
						By(
							below,
							wide,
							At(nat_order.PowTwoMonotone, np, i),
							At(nat_order.LessThanLessEqTrans,
								b.Term("rem(n, nat_pow(2, n'))"),
								b.Term("nat_pow(2, n')"), b.Term("nat_pow(2, i)"))))
					vanish := b.Have(
						"so the residue's quotient there vanishes",
						"div(rem(n, nat_pow(2, n')), nat_pow(2, i)) = 0",
						By(
							outrun,
							At(nat_arith.PowTwoNonzero, i),
							At(nat_div_mod.DivEqZero,
								b.Term("rem(n, nat_pow(2, n'))"), b.Term("nat_pow(2, i)"))))
					b.Show(
						"zero is even and the guard fails — both sides are false",
						By(outRange, vanish, wordBitDef, nat_parity.NatOdd))
				})
		}),
})}

// BitValMod — the k-th bit as a threshold on the (k+1)-bit residue:
// the residue reaches its top place value exactly when the bit is set.
// The next place value is twice this one (nat_arith.PowAdd), so
// nat_div_mod.DivMod reads the residue's quotient at 2^k as
// nat_mod(nat_div(x, 2^k), 2) — the bit, spelled as a remainder at two
// (nat_parity's nat_odd-as-nat_mod-2 characterization). Division splits the
// residue at the place value; with the bit set the split carries one
// whole block and the threshold holds, with it clear the residue IS
// the sub-place leftover and falls short.
var BitValMod = bitValModThm{family.Add(registry.ProofEntry{
	Name: "BitValMod",
	Key:  "prop_6be69907429c7b48",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x k:num.",
			Conclusion: "nat_pow(2, k) ≤ rem(x, nat_pow(2, k + 1)) ⇔ word_bit(k, x)",
		},
		func(a *Argument, x, k Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			two := a.Ctx().Numeral(2)
			place := a.Term("nat_pow(2, k)")
			residue := a.Term("rem(x, nat_pow(2, k + 1))")
			leftover := a.Term("rem(rem(x, nat_pow(2, k + 1)), nat_pow(2, k))")

			factor := a.Have(
				"the next place value is twice this one",
				"nat_pow(2, k + 1) = nat_pow(2, k) * 2",
				By(
					At(nat_arith.PowAdd, two, k, a.Ctx().Numeral(1)),
					// bare: the clause fires on the goal as the rewrite it is
					nat_arith.PowOne))
			interchange := a.Have(
				"so dividing the residue by the place value leaves the quotient's parity bit",
				"div(rem(x, nat_pow(2, k + 1)), nat_pow(2, k)) = rem(div(x, nat_pow(2, k)), 2)",
				By(factor, At(nat_div_mod.DivMod, x, place, two)))
			notOdd := a.Unless(
				a.Term("nat_odd(div(x, nat_pow(2, k)))"),
				"the bit is set: the split at the place value carries one whole block, so the threshold holds",
				Given(func(b *Argument, odd Fact) {
					bitOne := b.Have(
						"an odd quotient reads one at two",
						"rem(div(x, nat_pow(2, k)), 2) = 1",
						By(odd, nat_parity.OddIffModTwoOne))
					lift := b.Have(
						"so one whole place-value block sits inside the residue",
						"rem(x, nat_pow(2, k + 1)) = nat_pow(2, k) + rem(rem(x, nat_pow(2, k + 1)), nat_pow(2, k))",
						By(
							At(nat_arith.PowTwoNonzero, k),
							bitOne,
							interchange,
							At(nat_div_mod.Division, residue, place),
							// bare: 1·2^k collapses on the goal directly
							nat_arith.OneMul))
					b.Show(
						"a block inside pushes the residue past the threshold, and the bit is set",
						By(odd, lift, wordBitDef, At(nat_order.LessEqAdd, place, leftover)))
				}))

			bitZero := a.Have(
				"an even quotient reads zero at two",
				"rem(div(x, nat_pow(2, k)), 2) = 0",
				By(notOdd, nat_parity.EvenIffNotOdd, nat_parity.EvenIffModTwoZero))
			short := a.Have(
				"with no block inside, the residue is its own sub-place leftover, short of the place value",
				"rem(x, nat_pow(2, k + 1)) < nat_pow(2, k)",
				By(
					At(nat_arith.PowTwoNonzero, k),
					bitZero,
					interchange,
					At(nat_div_mod.Division, residue, place),
					nat_arith.MulLeftZeroClause,
					nat_arith.AddLeftZeroClause))
			a.Show(
				"short of the threshold with the bit clear — both sides fail",
				// Bare: the duality fires on the goal as the rewrite it is.
				By(notOdd, short, wordBitDef, nat_order.NotLessEq))
		}),
})}

// ---------------------------------------------------------------------------
// The two window laws
// ---------------------------------------------------------------------------
//
// the two window laws: a RANGE of bits read as one arithmetic fact about
// the value. The top bit is the top threshold (MsbVal), and the low window
// is clear exactly when the low residue vanishes (LowerBitsZero). Both are
// the machinery already in place read at a window's edge — BitValMod's per-bit
// threshold at the top position, UpperBitsZero's bit-extensional bound at
// the empty window — and this is where the chapter's width guard finally
// earns its keep: MsbVal is the ONE member whose 1 ≤ n carries content
// (the top position n − 1 needs the width to reach back up), and
// LowerBitsZero's inner window may be empty, splitting off a vacuous case
// no guard covers.

// MsbVal — the top bit is the top threshold: a value below 2^n has its
// bit n − 1 set exactly when it reaches 2^(n−1). This is BitValMod's
// threshold read at the top position, where the residue collapses to
// the value itself: the width guard restores the top exponent —
// (n − 1) + 1 = n needs 1 ≤ n (nat_monus.SubAddCancel), the one place
// in the chapter that guard carries content — and below the width the
// reduction forgets nothing (nat_div_mod.ModLessThan).
var MsbVal = msbValThm{family.Add(registry.ProofEntry{
	Name: "MsbVal",
	Key:  "prop_285604841f22e737",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"1 ≤ n",
				"w < nat_pow(2, n)",
			},
			Conclusion: "nat_pow(2, n - 1) ≤ w ⇔ word_bit(n - 1, w)",
		},
		func(a *Argument, n, w Term, widthPos, wBound Fact) {
			one := a.Ctx().Numeral(1)
			threshold := a.Have(
				"the per-bit threshold, read at the top position",
				"(nat_pow(2, n - 1) ≤ rem(w, nat_pow(2, (n - 1) + 1))) ⇔ word_bit(n - 1, w)",
				By(BitValMod))
			split := a.Have(
				"the width guard restores the top exponent",
				"(n - 1) + 1 = n",
				By(widthPos, At(nat_monus.SubAddCancel, n, one)))
			collapse := a.Have(
				"so the top residue is the value itself",
				"rem(w, nat_pow(2, (n - 1) + 1)) = w",
				By(Normalized, split, wBound, At(nat_div_mod.ModLessThan, w, a.Term("nat_pow(2, n)"))))
			a.Show(
				"and the threshold reads on the value directly",
				By(Normalized, threshold, collapse))
		}),
})}

// LowerBitsZero — the low window is clear exactly when the low residue
// vanishes. An empty window is vacuously clear against a width-zero
// residue that is already zero (the split no guard covers). On a
// nonzero window the residue carries exactly the window's bits
// (BitWord), so a clear window strips it of every bit and bit
// extensionality at the EMPTY inner window (UpperBitsZero) squeezes it
// below 2^0 = 1 — zero; conversely a zero residue is the zero word,
// which has no bits for the window to show (BitWordZero).
var LowerBitsZero = lowerBitsZeroThm{family.Add(registry.ProofEntry{
	Name: "LowerBitsZero",
	Key:  "prop_77273926ccb36b6c",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x n:num.",
			Conclusion: "(∀i:num. ¬(i < n) ∨ ¬word_bit(i, x)) ⇔ 0 = rem(x, nat_pow(2, n))",
		},
		func(a *Argument, x, n Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			zero := a.Ctx().Numeral(0)
			residue := a.Term("rem(x, nat_pow(2, n))")

			a.Unless(
				a.Term("n = 0"),
				"n = 0: an empty window is vacuously clear, and the width-zero residue vanishes — both sides true",
				Given(func(z *Argument, isZero Fact) {
					vacuous := z.Have(
						"no position sits below zero",
						"∀i:num. ¬(i < n) ∨ ¬word_bit(i, x)",
						Derive(func(w *Argument) {
							w.Fix() // i — the position, spelled in the claim
							w.Do(By(isZero, nat_order.LessThanZeroClause))
						}))
					empty := z.Have(
						"and the residue at width zero vanishes",
						"0 = rem(x, nat_pow(2, n))",
						By(isZero, nat_arith.NatPow, At(nat_div_mod.ModOne, x)))
					z.Show(
						"both sides hold outright",
						By(vacuous, empty))
				}))
			forward := a.Have(
				"a clear window empties the residue",
				"(∀i:num.(¬(i < n) ∨ ¬word_bit(i, x))) ⇒ (0 = rem(x, nat_pow(2, n)))",
				Derive(func(b *Argument) {
					clear := b.Assume()
					noBits := b.Have(
						"no bit of the residue survives — inside the window it is clear, outside the reduction clears it",
						"∀i:num. ¬word_bit(i, rem(x, nat_pow(2, n)))",
						Derive(func(w *Argument) {
							i := w.Fix()
							w.Do(By(clear.At(i), wordBitDef, BitWord))
						}))
					zeroWindow := b.Have(
						"in the empty-window spelling",
						"∀i:num. ¬(0 ≤ i) ∨ ¬word_bit(i, rem(x, nat_pow(2, n)))",
						Derive(func(w *Argument) {
							i := w.Fix()
							w.Do(By(noBits.At(i)))
						}))
					resBound := b.Have(
						"the residue sits below the window's power",
						"rem(x, nat_pow(2, n)) < nat_pow(2, n)",
						By(At(nat_arith.PowTwoNonzero, n), At(nat_div_mod.Division, x, a.Term("nat_pow(2, n)"))))
					tiny := b.Have(
						"no bits at all squeeze the residue below 2^0 — bit extensionality at the empty window",
						"rem(x, nat_pow(2, n)) < nat_pow(2, 0)",
						By(resBound, zeroWindow, UpperBitsZero))
					b.Do(By(
						tiny,
						nat_arith.NatPow,
						nat_arith.OneIsSucZero,
						At(nat_order.LessThanSucIffLessEq, residue, zero),
						nat_order.LessEqZeroClause))
				}))
			backward := a.Have(
				"an empty residue clears the window",
				"(0 = rem(x, nat_pow(2, n))) ⇒ (∀i:num.(¬(i < n) ∨ ¬word_bit(i, x)))",
				Derive(func(b *Argument) {
					emptied := b.Assume()
					b.Fix() // i — the position, spelled in the claims below
					survive := b.Have(
						"a set bit inside the window would survive the reduction",
						"((i < n) ∧ word_bit(i, x)) ⇒ word_bit(i, rem(x, nat_pow(2, n)))",
						Derive(func(c *Argument) {
							both := c.Assume()
							c.Do(By(both, wordBitDef, BitWord))
						}))
					cleared := b.Have(
						"but the residue is the zero word, and the zero word has no bits",
						"¬word_bit(i, rem(x, nat_pow(2, n)))",
						By(emptied, BitWordZero))
					b.Do(By(survive, cleared))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ---------------------------------------------------------------------------
// Bit extensionality: a bounded value IS its low bits
// ---------------------------------------------------------------------------
//
// The projections above read single positions of a value; this part
// says the positions are all there is. Two facts carry the cluster, and both
// are one induction on the width riding one halving identity
// (bitHalf): the bits of nat_div(x, 2) are the bits of x, one place up —
// word_bit's definition read through nat_div_mod's quotient algebra, where
// stacked divisions merge into the doubled place value. Everything
// else is the induction walked down that shift: a value whose bits
// from n up are clear sits below 2^n (ClearBitsBound — the base case
// is the fundamental faithfulness fact, a value with no bits at all
// is zero, reached through the division algorithm at two), and two
// bounded values agreeing on the low n bits are equal (sameBitsEqual
// — the halves agree one window down, the parity bits agree at
// position zero, and the division algorithm reassembles).
//
// The public members read those two inductions back as biconditionals.
// The range guards are live exactly as the inductions' fuel: the BitsEq
// pair feeds both to the core.

// bitHalf — the halving identity every member of this part rides: the
// bits of the half are the bits of the value, one place up. Reading
// position suc(i) divides by 2·2^i, and dividing by two first and by
// 2^i after is the same division — nat_div_mod.DivDiv with the
// exponent's successor clause.
var bitHalf = bitHalfThm{family.Add(registry.ProofEntry{
	Name: "bitHalf",
	Key:  "prop_fd081b0bb81348f9",
	Build: family.Theorem("∀i x:num. word_bit(suc(i), x) ⇔ word_bit(i, div(x, 2))",
		func(a *Argument, i, x Term) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			merged := a.Have(
				"halving first and then reading position i is one division by the doubled place value",
				"div(div(x, 2), nat_pow(2, i)) = div(x, nat_pow(2, suc(i)))",
				By(At(nat_div_mod.DivDiv, x, a.Ctx().Numeral(2), a.Term("nat_pow(2, i)")), nat_arith.NatPow))
			a.Show(
				"so the two bits read one quotient's parity",
				By(wordBitDef, merged))
		}),
})}

// ClearBitsBound — clear bits from n up bound the value below 2^n:
// the inductive heart of UpperBitsZero. The induction is on an
// auxiliary bound k — every value carries one, and the consumer seeds
// it with its own width guard — because the width n cannot descend
// alone: the value must halve as the window does. The step is the
// halving identity walked down: the half's bits from the predecessor
// window up are the value's from n up, the IH bounds the half, and
// stacked divisions lift the half's bound back to the value. At a
// zero window the same IH lands at width zero — the half is zero, the
// parity bit is clear, and the division algorithm at two leaves
// nothing of x at all.
var ClearBitsBound = clearBitsBoundThm{family.Add(registry.ProofEntry{
	Name: "ClearBitsBound",
	Key:  "prop_56bdb802e631600c",
	Build: family.Theorem(
		Statement{
			Binders: "∀k x n:num.",
			Hypotheses: []string{
				"x < nat_pow(2, k)",
				"∀i:num. ¬(n ≤ i) ∨ ¬word_bit(i, x)",
			},
			Conclusion: "x < nat_pow(2, n)",
		},
		func(a *Argument) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			zero := a.Ctx().Numeral(0)
			one := a.Ctx().Numeral(1)
			two := a.Ctx().Numeral(2)

			a.Induct("k")
			a.Base(
				"k = 0: below 2^0 = 1 the value is zero already, and zero is below every width",
				func(b *Argument) {
					x := b.Fix()
					n := b.Fix() // the width
					// x < nat_pow(2, 0), and the clear-bits hypothesis the base never reads
					tiny := b.Conjuncts(
						b.Assume(),
						"x is below 2^0",
						"and its bits from n on are clear")[0]
					xZero := b.Have(
						"below one the value is zero",
						"x = 0",
						By(
							tiny,
							nat_arith.NatPow,
							nat_arith.OneIsSucZero,
							At(nat_order.LessThanSucIffLessEq, x, zero),
							nat_order.LessEqZeroClause))
					b.Show(
						"and zero is below every width — a power of two is never zero",
						By(xZero, At(nat_arith.PowTwoNonzero, n), nat_order.PosIffNonzero))
				})
			a.Step(
				"k → suc(k): halving shifts every bit one place down and the "+
					"bound one factor of two down — the IH answers at the half",
				func(b *Argument, ih Fact) {
					x := b.Fix()
					n := b.Fix()
					held := b.Conjuncts(
						b.Assume(),
						"x is below 2^(k+1)",
						"and its bits from n on are clear")
					xBound := held[0] // x < nat_pow(2, suc(k))
					clear := held[1]  // ∀i. ¬(n ≤ i) ∨ ¬word_bit(i, x)
					half := b.Term("div(x, 2)")
					powK := b.Term("nat_pow(2, k)")

					vanish := b.Have(
						"the bound says x's quotient at the full 2^(k+1) vanishes",
						"div(x, nat_pow(2, suc(k))) = 0",
						By(
							xBound,
							At(nat_arith.PowTwoNonzero, b.Term("suc(k)")),
							At(nat_div_mod.DivEqZero, x, b.Term("nat_pow(2, suc(k))"))))
					shifted := b.Have(
						"and that quotient is the half's at 2^k — stacked divisions merge",
						"div(div(x, 2), nat_pow(2, k)) = 0",
						By(vanish, nat_arith.NatPow, At(nat_div_mod.DivDiv, x, two, powK)))
					halfBound := b.Have(
						"so the half sits below 2^k",
						"div(x, 2) < nat_pow(2, k)",
						By(shifted, At(nat_arith.PowTwoNonzero, b.Term("k")), At(nat_div_mod.DivEqZero, half, powK)))

					notZero := b.Unless(
						b.Term("n = 0"),
						"n = 0: an empty window clears every bit, and a value with no bits at all is zero",
						Given(func(z *Argument, isZero Fact) {
							noBits := z.Have(
								"no bit of x is set anywhere",
								"∀i:num. ¬word_bit(i, x)",
								Derive(func(w *Argument) {
									i := w.Fix()
									w.Do(By(isZero, clear.At(i), nat_order.ZeroLessEq))
								}))
							halfNoBits := z.Have(
								"nor of the half — its bits are x's, one place up",
								"∀i:num. ¬word_bit(i, div(x, 2))",
								Derive(func(w *Argument) {
									w.Fix() // i — the position, spelled below
									w.Do(By(noBits.At(w.Term("suc(i)")), bitHalf))
								}))
							halfTiny := z.Have(
								"the IH at the half, read at width zero",
								"div(x, 2) < nat_pow(2, 0)",
								By(halfBound, halfNoBits, ih.At(half, zero)))
							halfZero := z.Have(
								"that is: the half is zero",
								"div(x, 2) = 0",
								By(
									halfTiny,
									nat_arith.NatPow,
									nat_arith.OneIsSucZero,
									At(nat_order.LessThanSucIffLessEq, half, zero),
									nat_order.LessEqZeroClause))
							unit := z.Have(
								"dividing by one changes nothing",
								"div(x, 1) = x",
								By(nat_arith.OneNotZero, At(nat_div_mod.DivMult, one, x), nat_arith.OneMul))
							notOdd := z.Have(
								"a clear bit at position zero says x is not odd",
								"¬nat_odd(x)",
								By(Normalized, noBits.At(zero), wordBitDef, nat_arith.NatPow, unit))
							modZero := z.Have(
								"so x leaves no remainder by two",
								"rem(x, 2) = 0",
								By(notOdd, nat_parity.EvenIffNotOdd, nat_parity.EvenIffModTwoZero))
							nzTwo := z.Have(
								"two is not zero",
								"¬(2 = 0)",
								By(nat_arith.Two, peano.SucNotZero))
							decomp := z.Have(
								"x is twice its half plus that remainder",
								"x = div(x, 2) * 2 + rem(x, 2)",
								By(nzTwo, At(nat_div_mod.Division, x, two)))
							xZero := z.Have(
								"with a zero half and no remainder, x is zero",
								"x = 0",
								By(Normalized, decomp, halfZero, modZero, nat_arith.Mul, nat_arith.Add))
							z.Show(
								"and zero is below every width — a power of two is never zero",
								By(xZero, At(nat_arith.PowTwoNonzero, n), nat_order.PosIffNonzero))
						}))

					m, nIsSuc := b.Obtain(
						"a nonzero window has a predecessor",
						"∃m:num. n = suc(m)",
						By(Normalized, notZero, At(peano.Cases, n)))
					powM := b.Term("nat_pow(2, m)")
					halfClear := b.Have(
						"the half's bits from m up are x's from n up — all clear",
						"∀i:num. ¬(m ≤ i) ∨ ¬word_bit(i, div(x, 2))",
						Derive(func(w *Argument) {
							i := w.Fix()
							w.Do(By(nIsSuc, clear.At(w.Term("suc(i)")), At(nat_order.SucLessEqSucIff, m, i), bitHalf))
						}))
					halfBelow := b.Have(
						"so the IH bounds the half below 2^m",
						"div(x, 2) < nat_pow(2, m)",
						By(halfBound, halfClear, ih.At(half, m)))
					lifted := b.Have(
						"so x's quotient at the window's power vanishes",
						"div(x, nat_pow(2, suc(m))) = 0",
						By(
							halfBelow,
							At(nat_arith.PowTwoNonzero, m),
							At(nat_div_mod.DivEqZero, half, powM),
							nat_arith.NatPow,
							At(nat_div_mod.DivDiv, x, two, powM)))
					b.Show(
						"and a vanishing quotient at the window is exactly the bound",
						By(
							lifted,
							nIsSuc,
							At(nat_arith.PowTwoNonzero, b.Term("suc(m)")),
							At(nat_div_mod.DivEqZero, x, b.Term("nat_pow(2, suc(m))"))))
				})
		}),
})}

// UpperBitsZero — a value is bounded by 2^n exactly when its bits
// from n up are clear. The forward direction is ClearBitsBound seeded
// by the outer guard — the one member of this part where that guard is
// live, and only as the induction's fuel: the inner n is the width
// that matters. Backward is BitTrivial's argument read at the inner
// n, which the outer guard never covers: past n the place
// value outruns the value, the quotient vanishes, and zero is even.
var UpperBitsZero = upperBitsZeroThm{family.Add(registry.ProofEntry{
	Name: "UpperBitsZero",
	Key:  "prop_5344154130ad60c4",
	Build: family.Theorem(
		Statement{
			Binders: "∀n' x n:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n')",
			},
			Conclusion: "(∀i:num. ¬(n ≤ i) ∨ ¬word_bit(i, x)) ⇔ x < nat_pow(2, n)",
		},
		func(a *Argument, np, x, n Term, xBound Fact) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			powN := a.Term("nat_pow(2, n)")
			forward := a.Have(
				"clear bits from n up bound the value — the induction, seeded by the outer guard",
				"(∀i:num.(¬(n ≤ i) ∨ ¬word_bit(i, x))) ⇒ (x < nat_pow(2, n))",
				Derive(func(b *Argument) {
					clear := b.Assume()
					b.Do(By(xBound, clear, At(ClearBitsBound, np, x, n)))
				}))
			backward := a.Have(
				"below 2^n no bit from n up survives — the place value outruns the value there",
				"(x < nat_pow(2, n)) ⇒ (∀i:num.(¬(n ≤ i) ∨ ¬word_bit(i, x)))",
				Derive(func(b *Argument) {
					bound := b.Assume()
					i := b.Fix("i")
					powI := b.Term("nat_pow(2, i)")
					outrun := b.Have(
						"at or past n, the place value outruns the value",
						"n ≤ i ⇒ x < nat_pow(2, i)",
						Derive(func(c *Argument) {
							le := c.Assume()
							c.Do(By(
								le,
								bound,
								At(nat_order.PowTwoMonotone, n, i),
								At(nat_order.LessThanLessEqTrans, x, powN, powI)))
						}))
					vanish := b.Have(
						"so the quotient there vanishes",
						"n ≤ i ⇒ div(x, nat_pow(2, i)) = 0",
						Derive(func(c *Argument) {
							le := c.Assume()
							c.Do(By(le, outrun, At(nat_arith.PowTwoNonzero, i), At(nat_div_mod.DivEqZero, x, powI)))
						}))
					b.Do(By(Normalized, vanish, wordBitDef, nat_parity.NatOdd))
				}))
			a.Do(By(forward, backward))
		}),
})}

// sameBitsEqual — bounded values agreeing on the low n bits are
// equal: the inductive heart of the BitsEq pair. Here the width and
// the bound descend together, so the width itself is the induction
// variable. Base: below 2^0 = 1 both values are zero. Step: the
// halves agree one window down (the halving identity, twice per
// position) and sit below 2^n, so the IH makes them equal; the parity
// bits agree because position zero is in the window; and the division
// algorithm at two reassembles each value from that half and that
// parity.
var sameBitsEqual = sameBitsEqualThm{family.Add(registry.ProofEntry{
	Name: "sameBitsEqual",
	Key:  "prop_7d5531108d5998ce",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
				"∀i:num. ¬(i < n) ∨ (word_bit(i, v) ⇔ word_bit(i, w))",
			},
			Conclusion: "v = w",
		},
		func(a *Argument) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			zero := a.Ctx().Numeral(0)
			one := a.Ctx().Numeral(1)
			two := a.Ctx().Numeral(2)
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"n = 0: below 2^0 = 1 both values are zero already",
				func(b *Argument) {
					v := b.Fix()
					w := b.Fix()
					// the two bounds, and the agreement the base never reads
					held := b.Conjuncts(
						b.Assume(),
						"v is below 2^0",
						"w is below 2^0",
						"and they agree on every bit below 0")
					vBound, wBound := held[0], held[1]
					vZero := b.Have(
						"below one, v is zero",
						"v = 0",
						By(
							vBound,
							nat_arith.NatPow,
							nat_arith.OneIsSucZero,
							At(nat_order.LessThanSucIffLessEq, v, zero),
							nat_order.LessEqZeroClause))
					wZero := b.Have(
						"and w likewise",
						"w = 0",
						By(
							wBound,
							nat_arith.NatPow,
							nat_arith.OneIsSucZero,
							At(nat_order.LessThanSucIffLessEq, w, zero),
							nat_order.LessEqZeroClause))
					b.Show(
						"both zero, hence equal",
						By(Normalized, vZero, wZero))
				})
			a.Step(
				"n → suc(n): the halves agree a window down and the IH equates them; "+
					"the parity bits agree at zero; the division algorithm reassembles",
				func(b *Argument, ih Fact) {
					v := b.Fix()
					w := b.Fix()
					held := b.Conjuncts(
						b.Assume(),
						"v is below 2^(n+1)",
						"w is below 2^(n+1)",
						"and they agree on every bit below n + 1")
					vBound := held[0] // v < nat_pow(2, suc(n))
					wBound := held[1] // w < nat_pow(2, suc(n))
					agree := held[2]  // ∀i. ¬(i < suc(n)) ∨ (word_bit(i, v) ⇔ word_bit(i, w))
					halfV := b.Term("div(v, 2)")
					halfW := b.Term("div(w, 2)")
					powN := b.Term("nat_pow(2, n)")
					powSN := b.Term("nat_pow(2, suc(n))")

					vVanish := b.Have(
						"v's quotient at the full width vanishes",
						"div(v, nat_pow(2, suc(n))) = 0",
						By(vBound, At(nat_arith.PowTwoNonzero, b.Term("suc(n)")), At(nat_div_mod.DivEqZero, v, powSN)))
					vHalfBound := b.Have(
						"so v's half sits below 2^n",
						"div(v, 2) < nat_pow(2, n)",
						By(
							vVanish,
							nat_arith.NatPow,
							At(nat_div_mod.DivDiv, v, two, powN),
							At(nat_arith.PowTwoNonzero, n),
							At(nat_div_mod.DivEqZero, halfV, powN)))
					wVanish := b.Have(
						"and w's quotient at the full width vanishes",
						"div(w, nat_pow(2, suc(n))) = 0",
						By(wBound, At(nat_arith.PowTwoNonzero, b.Term("suc(n)")), At(nat_div_mod.DivEqZero, w, powSN)))
					wHalfBound := b.Have(
						"so w's half sits below 2^n too",
						"div(w, 2) < nat_pow(2, n)",
						By(
							wVanish,
							nat_arith.NatPow,
							At(nat_div_mod.DivDiv, w, two, powN),
							At(nat_arith.PowTwoNonzero, n),
							At(nat_div_mod.DivEqZero, halfW, powN)))

					halvesAgree := b.Have(
						"the halves agree on the window below n — their bits sit one place up in the full window",
						"∀i:num. ¬(i < n) ∨ (word_bit(i, div(v, 2)) ⇔ word_bit(i, div(w, 2)))",
						Derive(func(c *Argument) {
							i := c.Fix()
							c.Do(By(
								agree.At(c.Term("suc(i)")),
								At(nat_order.SucLessEqIffLessThan, i, n),
								At(nat_order.LessThanSucIffLessEq, c.Term("suc(i)"), n),
								bitHalf))
						}))
					halvesEqual := b.Have(
						"bounded and agreeing below n, the halves are equal — the IH",
						"div(v, 2) = div(w, 2)",
						By(vHalfBound, wHalfBound, halvesAgree, ih.At(halfV, halfW)))

					unitV := b.Have(
						"dividing v by one changes nothing",
						"div(v, 1) = v",
						By(nat_arith.OneNotZero, At(nat_div_mod.DivMult, one, v), nat_arith.OneMul))
					unitW := b.Have(
						"nor w",
						"div(w, 1) = w",
						By(nat_arith.OneNotZero, At(nat_div_mod.DivMult, one, w), nat_arith.OneMul))
					parityAgree := b.Have(
						"the parity bits agree — position zero is in the window",
						"nat_odd(v) ⇔ nat_odd(w)",
						By(
							Normalized,
							agree.At(zero),
							nat_order.ZeroLessThanSuc,
							wordBitDef,
							nat_arith.NatPow,
							unitV,
							unitW))
					modAgree := b.Have(
						"so the remainders by two agree",
						"rem(v, 2) = rem(w, 2)",
						By(
							Normalized,
							parityAgree,
							nat_parity.OddIffModTwoOne,
							nat_parity.EvenIffNotOdd,
							nat_parity.EvenIffModTwoZero))

					nzTwo := b.Have(
						"two is not zero",
						"¬(2 = 0)",
						By(nat_arith.Two, peano.SucNotZero))
					decompV := b.Have(
						"v is twice its half plus its remainder",
						"v = div(v, 2) * 2 + rem(v, 2)",
						By(nzTwo, At(nat_div_mod.Division, v, two)))
					decompW := b.Have(
						"and w likewise",
						"w = div(w, 2) * 2 + rem(w, 2)",
						By(nzTwo, At(nat_div_mod.Division, w, two)))
					b.Show(
						"equal halves and equal remainders reassemble to equal values",
						By(Normalized, decompV, decompW, halvesEqual, modAgree))
				})
		}),
})}

// BitsEqBounded — bounded values agreeing on the low n bits are equal,
// as a biconditional: the forward direction is
// sameBitsEqual under the two range guards, the backward direction is
// congruence. The induction needs no positivity.
var BitsEqBounded = bitsEqBoundedThm{family.Add(registry.ProofEntry{
	Name: "BitsEqBounded",
	Key:  "prop_115f0761129bded7",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
			},
			Conclusion: "(∀i:num. ¬(i < n) ∨ (word_bit(i, v) ⇔ word_bit(i, w))) ⇔ v = w",
		},
		func(a *Argument, n, v, w Term, vBound, wBound Fact) {
			forward := a.Have(
				"agreement on the window pins the value — the induction",
				"(∀i:num.(¬(i < n) ∨ (word_bit(i, v) ⇔ word_bit(i, w)))) ⇒ (v = w)",
				Derive(func(b *Argument) {
					agree := b.Assume()
					b.Do(By(vBound, wBound, agree, At(sameBitsEqual, n, v, w)))
				}))
			backward := a.Have(
				"equal values agree everywhere — congruence",
				"(v = w) ⇒ (∀i:num.(¬(i < n) ∨ (word_bit(i, v) ⇔ word_bit(i, w))))",
				Derive(func(b *Argument) {
					eq := b.Assume()
					b.Do(By(Normalized, eq))
				}))
			a.Do(By(forward, backward))
		}),
})}

// BitsEq — the unwindowed spelling: agreement at every position is in
// particular agreement on the window, and the window pins the value —
// the same inductive core BitsEqBounded reads, cited at these two
// values. (Consuming the sibling's biconditional itself would mean
// grounding through its guarded ∀-chain, which the refuter's budget
// rejects; the core applies whole.) The congruence direction needs no
// window at all.
var BitsEq = bitsEqThm{family.Add(registry.ProofEntry{
	Name: "BitsEq",
	Key:  "prop_55af04944c41fdb3",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
			},
			Conclusion: "(∀i:num. word_bit(i, v) ⇔ word_bit(i, w)) ⇔ v = w",
		},
		func(a *Argument, n, v, w Term, vBound, wBound Fact) {
			forward := a.Have(
				"agreement everywhere includes the window, and the window pins the value",
				"(∀i:num.(word_bit(i, v) ⇔ word_bit(i, w))) ⇒ (v = w)",
				Derive(func(b *Argument) {
					agree := b.Assume()
					windowed := b.Have(
						"in particular the low window agrees",
						"∀i:num. ¬(i < n) ∨ (word_bit(i, v) ⇔ word_bit(i, w))",
						Derive(func(c *Argument) {
							i := c.Fix()
							c.Do(By(Normalized, agree.At(i)))
						}))
					b.Do(By(vBound, wBound, windowed, At(sameBitsEqual, n, v, w)))
				}))
			backward := a.Have(
				"equal values agree everywhere — congruence",
				"(v = w) ⇒ (∀i:num.(word_bit(i, v) ⇔ word_bit(i, w)))",
				Derive(func(b *Argument) {
					eq := b.Assume()
					b.Do(By(Normalized, eq))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ---------------------------------------------------------------------------
// The window combinators' defining clauses
// ---------------------------------------------------------------------------
//
// the window combinators' defining clauses are the combinators'
// definition entries themselves: words/machine_word defines
// word_bitwise_unary and word_bitwise_binary through the define door as
// recursions on the window with the operation and the operands as
// curried parameters, so `machine_word.WordBitwiseUnaryDef` and
// `machine_word.WordBitwiseBinaryDef` state the two clauses at the constant,
// and every window member below cites them.

// ---------------------------------------------------------------------------
// ---------------------------------------------------------------------------
// The operators as instances
// ---------------------------------------------------------------------------
//
// Each bitwise operator the substrate mints is ONE instantiation of
// its window combinator, so each bitwise twin here is ONE instance
// of the generic projection (below) — unfold the define door, read the
// projection at the operator's own window and operation, and let β
// hand the operation its operand bits.
//
// What the instances actually spend is the bit face's two NATIVE
// keystones. BitBelowBound is the width-free operators' entire
// bookkeeping: a set bit sits below ANY covering width — below the
// stated width n through the range guards, and below the operators'
// own window x + y through nothing but the operands themselves (a
// value sits under its own power, nat_order.LessThanPowTwoSelf) — which is exactly how
// the window conjunct the projection reports reconciles with the k < n
// the twins state. BitsEqAll is bit extensionality with the window
// dissolved: two values agreeing at EVERY position are equal, no bound
// asked — every value is bounded by the width suc(v + w) of its own
// making, and BitsEq (above) does the rest. The pointwise-law
// waves ride these two: a law of the operators is a law of bits read
// through the projections, and BitsEqAll is what turns it back into an
// equation of values.
//
// The range guards are live exactly where a position is measured
// against the width.

// ---------------------------------------------------------------------------
// BitBelowBound — a set bit sits below any covering width
// ---------------------------------------------------------------------------

// BitBelowBound — the keystone the instances reconcile their windows
// with: whatever width covers the value covers its set bits. A set bit
// is an odd quotient, so a nonzero one — the value reaches the bit's
// place value (DivEqZero's contrapositive). Were the position at or
// past the width, the width's power would sit under the position's
// (nat_order.PowTwoMonotone), and the value would have outrun the very bound
// that covers it.
var BitBelowBound = bitBelowBoundThm{family.Add(registry.ProofEntry{
	Name: "BitBelowBound",
	Key:  "prop_2b453dece020107f",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x k:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"word_bit(k, x)",
			},
			Conclusion: "k < n",
		},
		func(a *Argument, n, x, k Term, xBound, bitSet Fact) {
			wordBitDef := a.Ctx().ConstDefNormalized("word_bit")
			place := a.Term("nat_pow(2, k)")

			divNz := a.Have(
				"a set bit is an odd quotient, and odd is nonzero",
				"¬(div(x, nat_pow(2, k)) = 0)",
				By(Normalized, bitSet, wordBitDef, nat_parity.NatOdd))
			placeLe := a.Have(
				"so the value reaches the bit's place value",
				"nat_pow(2, k) ≤ x",
				// Bare: the duality fires on the claim as the rewrite it is.
				By(
					divNz,
					At(nat_arith.PowTwoNonzero, k),
					At(nat_div_mod.DivEqZero, x, place),
					nat_order.NotLessThan))
			a.Show(
				"were the position at or past the width, its place "+
					"value would outrun the very bound that covers the value",
				By(
					placeLe,
					xBound,
					At(nat_order.PowTwoMonotone, n, k),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, n)"), place),
					// Bare: one duality, read at both comparisons.
					nat_order.NotLessThan))
		}),
})}

// ---------------------------------------------------------------------------
// BitAnd · BitOr · BitXor — the binary operators, projected
// ---------------------------------------------------------------------------

// BitAnd — the val-face form: a bit of the conjunction is
// the conjunction of bits, inside the width. Unfolding the define door
// hands the goal to BitwiseBinaryProjection at the operator's own window
// x + y; what remains is reconciling the windows — a set bit of either
// side sits below x + y because a value sits under its own power
// (BitBelowBound at the window x + y covers, seeded by nat_order.LessThanPowTwoSelf),
// and below n through the range guard (BitBelowBound again).
var BitAnd = bitAndThm{family.Add(registry.ProofEntry{
	Name: "BitAnd",
	Key:  "prop_8236f924fc5cbeb1",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num. ∀k.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_bit(k, word_and(x, y)) ⇔ k < n ∧ word_bit(k, x) ∧ word_bit(k, y)",
		},
		func(a *Argument, n, x, y, k Term, xBound Fact) {
			wordAndDef := a.Ctx().ConstDefNormalized("word_and")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the conjunction is the "+
					"conjunction of bits inside the operator's own window",
				"word_bit(k, word_and(x, y)) ⇔ ((word_bit(k, x) ∧ word_bit(k, y)) ∧ (k < x + y))",
				By(wordAndDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			guardX := a.Have(
				"and below the width, through the range guard",
				"word_bit(k, x) ⇒ (k < n)",
				By(xBound, BitBelowBound))
			a.Show(
				"both windows agree on a set bit of x, and the rest is propositional",
				By(Normalized, projRead, covX, guardX))
		}),
})}

// BitOr — the val-face form: a bit of the disjunction is the
// disjunction of bits, inside the width. The shape is BitAnd's; here a
// set bit of the OR only promises a set bit of ONE operand, so both
// sides carry their window facts.
var BitOr = bitOrThm{family.Add(registry.ProofEntry{
	Name: "BitOr",
	Key:  "prop_77ff59eb11e77d14",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num. ∀k.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_bit(k, word_or(x, y)) ⇔ k < n ∧ (word_bit(k, x) ∨ word_bit(k, y))",
		},
		func(a *Argument, n, x, y, k Term, xBound, yBound Fact) {
			wordOrDef := a.Ctx().ConstDefNormalized("word_or")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the disjunction is the "+
					"disjunction of bits inside the operator's own window",
				"word_bit(k, word_or(x, y)) ⇔ ((word_bit(k, x) ∨ word_bit(k, y)) ∧ (k < x + y))",
				By(wordOrDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			yCover := a.Have(
				"and y likewise",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAddLeft, x, y),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans,
						y, a.Term("nat_pow(2, y)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			covY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < x + y)",
				By(yCover, BitBelowBound))
			guardX := a.Have(
				"a set bit of x sits below the width, through the range guard",
				"word_bit(k, x) ⇒ (k < n)",
				By(xBound, BitBelowBound))
			guardY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < n)",
				By(yBound, BitBelowBound))
			a.Show(
				"whichever operand carries the bit carries both windows, and the rest is propositional",
				By(Normalized, projRead, covX, covY, guardX, guardY))
		}),
})}

// BitXor — the val-face form: a bit of the difference is
// the difference of bits, inside the width. The door's operation is
// spelled (a ∨ b) ∧ ¬(a ∧ b) at the mint (the ⊕ the parser does not
// read back) while the twin states ¬a ⇔ b — a two-atom propositional
// gap the closing refute absorbs along with the window reconciliation,
// which is BitOr's verbatim.
var BitXor = bitXorThm{family.Add(registry.ProofEntry{
	Name: "BitXor",
	Key:  "prop_f56f807b4f3cbf72",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num. ∀k.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_bit(k, word_xor(x, y)) ⇔ k < n ∧ (¬word_bit(k, x) ⇔ word_bit(k, y))",
		},
		func(a *Argument, n, x, y, k Term, xBound, yBound Fact) {
			wordXorDef := a.Ctx().ConstDefNormalized("word_xor")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the difference is the door's own spelling "+
					"of exactly-one at the operand bits, inside the operator's window",
				"word_bit(k, word_xor(x, y)) ⇔ "+
					"(((word_bit(k, x) ∨ word_bit(k, y)) ∧ ¬(word_bit(k, x) ∧ word_bit(k, y))) ∧ (k < x + y))",
				By(wordXorDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			yCover := a.Have(
				"and y likewise",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAddLeft, x, y),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans,
						y, a.Term("nat_pow(2, y)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			covY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < x + y)",
				By(yCover, BitBelowBound))
			guardX := a.Have(
				"a set bit of x sits below the width, through the range guard",
				"word_bit(k, x) ⇒ (k < n)",
				By(xBound, BitBelowBound))
			guardY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < n)",
				By(yBound, BitBelowBound))
			a.Show(
				"exactly-one means some operand carries the bit, so both windows "+
					"ride along — the two spellings of the difference are the same table",
				By(Normalized, projRead, covX, covY, guardX, guardY))
		}),
})}

// ---------------------------------------------------------------------------
// BitNot — the unary operator, projected
// ---------------------------------------------------------------------------

// BitNot — the val-face form: a bit of the complement is
// the cleared bit, inside the width. The one instance with NO window
// reconciliation: word_not's window IS the width n (complement is a fact
// about a window, and the mint says so), so BitwiseUnaryProjection's guard
// is already the twin's. Unfold the door, read the projection, done.
var BitNot = bitNotThm{family.Add(registry.ProofEntry{
	Name: "BitNot",
	Key:  "prop_78c74c2c42750aba",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n x:num. ∀k.",
			Conclusion: "word_bit(k, word_not(n, x)) ⇔ ¬word_bit(k, x) ∧ k < n",
		},
		func(a *Argument, n, x, k Term) {
			wordNotDef := a.Ctx().ConstDefNormalized("word_not")
			a.Show(
				"the complement's window is the width itself — the projection answers whole",
				By(wordNotDef, BitwiseUnaryProjection))
		}),
})}

// ---------------------------------------------------------------------------
// BitsEqAll — unbounded bit extensionality
// ---------------------------------------------------------------------------

// BitsEqAll — two values agreeing at EVERY position are equal, no
// bound asked: the exit every pointwise law takes back to an equation
// of values. The bound BitsEq wants is of the values' own making —
// suc(v + w) covers both (a value sits under its own power, and the
// power only grows to the chosen width) and is positive by shape.
var BitsEqAll = bitsEqAllThm{family.Add(registry.ProofEntry{
	Name: "BitsEqAll",
	Key:  "prop_19396d504db1526b",
	Build: family.Theorem(
		Statement{
			Binders: "∀v w:num.",
			Hypotheses: []string{
				"∀i:num. word_bit(i, v) ⇔ word_bit(i, w)",
			},
			Conclusion: "v = w",
		},
		func(a *Argument, v, w Term, agree Fact) {
			width := a.Term("suc(v + w)")
			powW := a.Term("nat_pow(2, suc(v + w))")

			vInside := a.Have(
				"it covers v — a value sits under its own power, which only grows to the width",
				"v < nat_pow(2, suc(v + w))",
				By(
					At(nat_order.LessThanPowTwoSelf, v),
					At(nat_order.LessEqAdd, v, w),
					At(nat_order.LessThanSucIffLessEq, v, a.Term("v + w")),
					At(nat_order.LessEqOfLessThan, v, width),
					At(nat_order.PowTwoMonotone, v, width),
					At(nat_order.LessThanLessEqTrans,
						v, a.Term("nat_pow(2, v)"), powW)))
			wInside := a.Have(
				"and w likewise",
				"w < nat_pow(2, suc(v + w))",
				By(
					At(nat_order.LessThanPowTwoSelf, w),
					At(nat_order.LessEqAddLeft, v, w),
					At(nat_order.LessThanSucIffLessEq, w, a.Term("v + w")),
					At(nat_order.LessEqOfLessThan, w, width),
					At(nat_order.PowTwoMonotone, w, width),
					At(nat_order.LessThanLessEqTrans,
						w, a.Term("nat_pow(2, w)"), powW)))
			a.Show(
				"agreeing everywhere, the two values agree in particular below "+
					"a width that bounds both — extensionality pins them equal",
				By(agree, vInside, wInside, BitsEq))
		}),
})}

// ---------------------------------------------------------------------------
// What the window combinators COMPUTE
// ---------------------------------------------------------------------------
//
// what the window combinators COMPUTE: every combinator value sits below
// its window's weight (the bound pair), and reading any bit of it gives
// the operation at the operands' bits, guarded by the window (the
// projection pair, stated over the low-k window).
//
// The set builder supplies the range and bit table. Each combinator
// builds the set of positions where its operation holds, so its bound
// and projection are readings of the builder's two laws.
//
// The width-free operators lean throughout on nat_order's
// order-against-exponentiation chapter — `n < 2^n` (LessThanPowTwoSelf) is
// what lets a window of x + y cover every set bit, and the place
// value's monotonicity (PowTwoMonotone) is what every high-bit
// argument spends.

// ---------------------------------------------------------------------------
// The digit table — bit_value's laws
// ---------------------------------------------------------------------------
//
// `bit_value : bool → num` names no word and no dimension, so its laws are
// dimension-orthogonal and live with the term-level substrate that
// spends them: the table itself, its bound, the two equality readings,
// and the parity reading.

// BitValueClauses — a bit read as a number is 1 when set and 0 when clear.
//
// The pair of equations is the whole of what `bit_value` does, and a word's
// value is a weighted sum of exactly these two digits, so every
// statement below is at bottom a statement about which of the two each
// place contributes. It is also where the readings the definition does
// not name come from: `bit_value(b) = 1 ⇔ b` is this table plus 1 ≠ 0.
var BitValueClauses = bitValueClausesThm{family.Add(registry.ProofEntry{
	Name: "BitValueClauses",
	Key:  "prop_64268550a97d707d",
	Build: family.Theorem("bit_value(⊥) = 0 ∧ bit_value(⊤) = 1",
		func(a *Argument) {
			a.Show(
				"at ⊥ and at ⊤ the conditional reduces to the branch each of them names",
				Unfold(machine_word.BitValueDef))
		}),
})}

// BitValueBound — a digit is at most 1.
//
// What makes a word's value a BINARY numeral rather than an arbitrary
// weighted sum: a place contributes its weight or nothing, never a
// multiple of it. Nothing in this chapter cites it — `ValBound` gets the
// same content already folded into the general digit-sum bound — so it
// is here as the scalar statement of that fact, for the faces above
// that count digits directly.
//
// Neither branch of the conditional can exceed 1: one branch is 1
// itself, and the other is the bottom of ≤.
var BitValueBound = bitValueBoundThm{family.Add(registry.ProofEntry{
	Name: "BitValueBound",
	Key:  "prop_d9297c134dbcc9a4",
	Build: family.Theorem("∀b:bool. bit_value(b) ≤ 1",
		func(a *Argument, b Term) {
			one := a.Ctx().Numeral(1)

			a.Show(
				"the digit is 1 or 0, and each of those is at most 1",
				Unfold(machine_word.BitValueDef),
				By(
					At(nat_order.LessEqRefl, one), // 1 ≤ 1
					At(nat_order.ZeroLessEq, one), // 0 ≤ 1
				))
		}),
})}

// BitValueEqZero — a digit is 0 exactly when its bit is clear.
//
// The reading of the table's zero case: a place contributes nothing to a
// word's value precisely when the word does not have that place. It is
// the form an argument wants when it is showing a SUM to vanish, so its
// consumers are the members that read a word's value as zero over a
// range of places rather than the ones that read a single digit.
//
// One direction is the definition read off the clear branch and nothing
// more; the other carries the whole content, and it turns on a single
// fact — that the digit on the OTHER branch is not 0 either, without
// which a set bit could contribute nothing too.
var BitValueEqZero = bitValueEqZeroThm{family.Add(registry.ProofEntry{
	Name: "BitValueEqZero",
	Key:  "prop_ee175dd0d47ddfdf",
	Build: family.Theorem("∀b:bool. bit_value(b) = 0 ⇔ ¬b",
		func(a *Argument, b Term) {
			a.Show(
				"the digit is 0 on the clear branch and 1 on the set one, and 1 is not 0",
				Unfold(machine_word.BitValueDef),
				By(nat_arith.OneNotZero))
		}),
})}

// BitValueEqOne — a digit is 1 exactly when its bit is set.
//
// `BitValueEqZero`'s mirror, and the pair of them is the statement that
// `bit_value` throws nothing away: the two digits are told apart, so a bit
// is recoverable from the number it contributes and not merely readable
// into one. That is the direction an argument needs when what it holds
// is a digit and what it owes is the bit — the table on its own only
// goes the other way.
//
// `digitIsBit`, below, wants exactly this equivalence at one word's
// bit, off exactly these two premises, and reaches it by hand.
var BitValueEqOne = bitValueEqOneThm{family.Add(registry.ProofEntry{
	Name: "BitValueEqOne",
	Key:  "prop_3b1505290bf959d9",
	Build: family.Theorem("∀b:bool. bit_value(b) = 1 ⇔ b",
		func(a *Argument, b Term) {
			a.Show(
				"1 and 0 are the table's two digits, and telling those apart is what recovers the bit",
				By(
					// Both premises are closed statements — no binder, so no
					// instance to name. That is why every bare cite in this
					// file's ground-value members is bare.
					BitValueClauses,
					nat_arith.OneNotZero,
				))
		}),
})}

// BitValueOfOdd — a number's parity, read as a digit, is its last binary
// place.
//
// Everywhere else a digit's bit is left abstract: the table and its two
// equality readings say nothing about where the boolean came from. Here
// it comes from a number, and this is the one place the chapter's two
// languages meet on a single digit — `nat_mod(·, 2)` is the bottom place
// computed by dividing, `bit_value` of a parity test is the same place
// obtained by asking a question, and they agree. It is the one-place
// form of the arithmetic `digitIsBit`, below, runs at every place of a
// word — though not the fact it needs there, which also wants `bit_value`
// read backwards.
//
// Both sides are decided by which of two cases holds, and each case is a
// row of the table matched with `nat_parity`'s reading of the residue it
// leaves.
var BitValueOfOdd = bitValueOfOddThm{family.Add(registry.ProofEntry{
	Name: "BitValueOfOdd",
	Key:  "prop_1751adfebd0b5d68",
	Build: family.Theorem("∀n:num. bit_value(nat_odd(n)) = rem(n, 2)",
		func(a *Argument, n Term) {
			// Normalized is load-bearing, and not because a premise is
			// missing: with these four resident the leaf settles under
			// Basic(), so the shaping keeps it away from the refuter and
			// this member records no CNF key. Drop it and the same list
			// reaches the refuter and needs one.
			a.Show(
				"an odd number leaves 1 and an even one leaves 0, which "+
					"are the table's two digits, and no number is neither",
				By(
					Normalized,
					BitValueClauses,                     // closed — no instance to name
					At(nat_parity.OddIffModTwoOne, n),   // nat_odd(n₀) ⇔ nat_mod(n₀, 2) = 1
					At(nat_parity.EvenIffModTwoZero, n), // nat_even(n₀) ⇔ nat_mod(n₀, 2) = 0
					At(nat_parity.OddIffNotEven, n),     // nat_odd(n₀) ⇔ ¬nat_even(n₀)
				))
		}),
})}

// OddBitValue — a digit's parity is its bit: the reading the projection
// members want at the window's edge, where the value's quotient at the
// weight has become a bare digit. The table's two digits are 1 and 0;
// one is odd and zero is not.
var OddBitValue = oddBitValueThm{family.Add(registry.ProofEntry{
	Name: "OddBitValue",
	Key:  "prop_d2d621b1788f83f",
	Build: family.Theorem("∀b:bool. nat_odd(bit_value(b)) ⇔ b",
		func(a *Argument, b Term) {
			oddOne := a.Have(
				"one is odd",
				"nat_odd(1)",
				By(nat_parity.NatOdd, nat_arith.OneIsSucZero))
			a.Show(
				"the digit is 1 on the set branch and 0 on the clear one; one is odd and zero is not",
				By(BitValueClauses, oddOne, nat_parity.NatOdd))
		}),
})}

// ---------------------------------------------------------------------------
// The set builder's range and bit table
// ---------------------------------------------------------------------------
//
// Building a word from a set truncates its membership table to the
// window. Its range and projection laws supply the corresponding
// laws for every pointwise window combinator through its set table.

// WordOfBitsBound — the built value sits below its window's weight, by
// induction on the window; the Case labels below carry the argument.
//
// This is what a consumer spends to know the builder's output is already
// reduced: nothing the set holds at or above n survives the cut.
var WordOfBitsBound = wordOfBitsBoundThm{family.Add(registry.ProofEntry{
	Name: "WordOfBitsBound",
	Key:  "prop_8e4a673b47c6b27a",
	Build: family.Theorem(
		"∀n:num. ∀s:set(num). word_of_bits(n, s) < nat_pow(2, n)",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"an empty window contributes nothing, and zero is below the empty weight one",
				func(b *Argument) {
					b.Fix() // s — spelled in the claims below
					empty := b.Have(
						"an empty window contributes nothing",
						"word_of_bits(0, s) = 0",
						By(machine_word.WordOfBitsDef))
					b.Show(
						"and zero is below the empty weight one",
						By(Normalized, empty, nat_arith.NatPow, nat_arith.OneNotZero, nat_order.PosIffNonzero))
				})
			a.Step(
				"the previous window sits strictly below its weight and the new "+
					"place adds at most its own — together below the doubled weight",
				func(b *Argument, ih Fact) {
					s := b.Fix()
					prev := b.Term("word_of_bits(n, s)")
					digit := b.Term("bit_value(n ∈ s)")
					place := b.Term("nat_pow(2, n) * bit_value(n ∈ s)")
					powN := b.Term("nat_pow(2, n)")
					one := b.Ctx().Numeral(1)

					open := b.Have(
						"widening the window adds the new place's weighted digit",
						"word_of_bits(suc(n), s) = word_of_bits(n, s) + nat_pow(2, n) * bit_value(n ∈ s)",
						By(machine_word.WordOfBitsDef))
					digitLe := b.Have(
						"the new digit is at most one",
						"bit_value(n ∈ s) ≤ 1",
						// Bare: the bound fires at the goal's own digit.
						By(BitValueBound))
					placeLe := b.Have(
						"so the new place contributes at most its weight",
						"nat_pow(2, n) * bit_value(n ∈ s) ≤ nat_pow(2, n)",
						// MulOne folds the goal's · 1 where it stands, so it
						// stays bare.
						By(digitLe, At(nat_order.LessEqMulMono, powN, digit, one), nat_arith.MulOne))
					b.Show(
						"at-most plus strictly-below stays strictly below the doubled weight — the next weight up",
						By(
							open,
							ih.At(s),
							placeLe,
							At(nat_order.LessEqLessThanAdd2, place, prev, powN, powN),
							At(nat_arith.AddSym, prev, place),
							// Bare: fires on the goal as the rewrite it is.
							nat_arith.PowTwoSuc))
				})
		}),
})}

// BitOfBitSet — a bit of the built value is membership, guarded by the
// window: position i is set exactly when the set holds i and the window
// reaches that far. This is the round trip that makes the position-set
// face usable — every law about a word built from a set is proved by
// reading its bits through this one.
//
// By induction on the window; the step splits the position against the
// window's edge into three regions, and the Case labels carry each
// region's argument.
var BitOfBitSet = bitOfBitSetThm{family.Add(registry.ProofEntry{
	Name: "BitOfBitSet",
	Key:  "prop_87cd41caf78e4d0d",
	Build: family.Theorem(
		"∀n i:num. ∀s:set(num). word_bit(i, word_of_bits(n, s)) ⇔ i < n ∧ (i ∈ s)",
		func(a *Argument) {
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"an empty window contributes nothing — the zero word has no bits, and no position sits below zero",
				func(b *Argument) {
					b.Fix() // i — spelled in the claims below
					b.Fix() // s
					wordBitDef := b.Ctx().ConstDefNormalized("word_bit")
					empty := b.Have(
						"an empty window contributes nothing",
						"word_of_bits(0, s) = 0",
						By(machine_word.WordOfBitsDef))
					b.Show(
						"every quotient of zero is zero, zero is even, and the guard is vacuous",
						By(
							Normalized,
							empty,
							wordBitDef,
							At(nat_div_mod.ZeroDiv, b.Term("nat_pow(2, i)")),
							nat_parity.NatOdd,
							nat_order.LessThanZeroClause))
				})
			a.Step(
				"the position splits against the window's edge — below it the "+
					"residue answers, at it the digit does, past it the bound does",
				func(b *Argument, ih Fact) {
					i := b.Fix()
					s := b.Fix()
					wordBitDef := b.Ctx().ConstDefNormalized("word_bit")
					val := b.Term("word_of_bits(suc(n), s)")
					prev := b.Term("word_of_bits(n, s)")
					powN := b.Term("nat_pow(2, n)")
					powI := b.Term("nat_pow(2, i)")

					open := b.Have(
						"widening the window adds the new place's weighted digit",
						"word_of_bits(suc(n), s) = word_of_bits(n, s) + nat_pow(2, n) * bit_value(n ∈ s)",
						By(machine_word.WordOfBitsDef))
					prevBound := b.Have(
						"the previous window sits below its weight",
						"word_of_bits(n, s) < nat_pow(2, n)",
						// Bare: the bound fires at the goal's own instance.
						By(WordOfBitsBound))

					b.Cases(b.Term("i < n"))
					b.When(
						"i < n: the low bits ride the residue, and the hypothesis reads them",
						func(c *Argument, inWin Fact) {
							residue := c.Have(
								"the residue at the weight is the previous window's value — the new place is an added multiple",
								"rem(word_of_bits(suc(n), s), nat_pow(2, n)) = word_of_bits(n, s)",
								By(open, prevBound, nat_div_mod.ModMultAdd, At(nat_div_mod.ModLessThan, prev, powN)))
							lowRead := c.Have(
								"a bit inside the window reads through the residue",
								"word_bit(i, rem(word_of_bits(suc(n), s), nat_pow(2, n))) ⇔ "+
									"nat_odd(div(word_of_bits(suc(n), s), nat_pow(2, i))) ∧ i < n",
								By(BitWord))
							c.Show(
								"so the bit is the previous window's, which the hypothesis reads; both guards hold below the edge",
								// The order bridges fire on the goal as
								// the rewrites they are, so both stay
								// bare.
								By(
									inWin,
									lowRead,
									residue,
									wordBitDef,
									ih.At(i, s),
									nat_order.LessEqOfLessThan,
									nat_order.LessThanSucIffLessEq))
						})
					b.Otherwise(
						"¬(i < n): at or past the window's edge",
						func(c *Argument, outWin Fact) {
							c.Cases(c.Term("i = n"))
							c.When(
								"i = n: the value's quotient at the weight is the "+
									"bare edge digit, and a digit's parity is membership",
								func(d *Argument, atEdge Fact) {
									splitDiv := d.Have(
										"the added multiple raises the quotient at the weight by exactly the digit",
										"div(word_of_bits(suc(n), s), nat_pow(2, n)) = "+
											"div(word_of_bits(n, s), nat_pow(2, n)) + bit_value(n ∈ s)",
										By(open, At(nat_arith.PowTwoNonzero, n), nat_div_mod.DivMultAdd))
									prevVanish := d.Have(
										"and the previous window's quotient vanishes under its bound",
										"div(word_of_bits(n, s), nat_pow(2, n)) = 0",
										By(prevBound, At(nat_arith.PowTwoNonzero, n), At(nat_div_mod.DivEqZero, prev, powN)))
									digitRead := d.Have(
										"so the quotient at the weight is the bare edge digit",
										"div(word_of_bits(suc(n), s), nat_pow(2, n)) = bit_value(n ∈ s)",
										By(splitDiv, prevVanish, nat_arith.AddLeftZeroClause))
									inSuc := d.Have(
										"the edge sits inside the widened window",
										"n < suc(n)",
										// Bare: the bridge fires on the
										// goal as the rewrite it is, and
										// reflexivity closes what is left.
										By(nat_order.LessThanSucIffLessEq, nat_order.LessEqRefl))
									d.Show(
										"so the bit at the edge is exactly whether the set holds it",
										By(atEdge, wordBitDef, digitRead, At(OddBitValue, d.Term("n ∈ s")), inSuc))
								})
							c.Otherwise(
								"i ≠ n: past the edge the position's weight outruns "+
									"the whole value — the bit is clear as the guard fails",
								func(d *Argument, offEdge Fact) {
									past := d.Have(
										"strictly past the edge",
										"n < i",
										By(outWin, offEdge, nat_order.NotLessThan, nat_order.LessEqSplit))
									valBound := d.Have(
										"the whole value sits below the widened weight",
										"word_of_bits(suc(n), s) < nat_pow(2, suc(n))",
										By(WordOfBitsBound))
									outrun := d.Have(
										"which the position's weight has outrun",
										"word_of_bits(suc(n), s) < nat_pow(2, i)",
										By(
											valBound,
											past,
											At(nat_order.SucLessEqIffLessThan, n, i),
											At(nat_order.PowTwoMonotone, d.Term("suc(n)"), i),
											At(nat_order.LessThanLessEqTrans,
												val, d.Term("nat_pow(2, suc(n))"), powI)))
									vanish := d.Have(
										"so the quotient there vanishes",
										"div(word_of_bits(suc(n), s), nat_pow(2, i)) = 0",
										By(outrun, At(nat_arith.PowTwoNonzero, i), At(nat_div_mod.DivEqZero, val, powI)))
									d.Show(
										"zero is even and the guard fails — both sides are false",
										// The order bridges fire on the
										// goal as the rewrites they are,
										// so both stay bare.
										By(
											vanish,
											wordBitDef,
											nat_parity.NatOdd,
											past,
											nat_order.LessThanSucIffLessEq,
											nat_order.NotLessEq))
								})
						})
				})
		}),
})}

// BitwiseUnaryAsBits — a unary window combinator builds the set of
// positions where its operation holds, by the same zero and successor
// clauses as the set builder.
var BitwiseUnaryAsBits = bitwiseUnaryAsBitsThm{family.Add(registry.ProofEntry{
	Name: "BitwiseUnaryAsBits",
	Key:  "prop_1b8dab36ca050013",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool). ∀x:num. "+
			"    word_bitwise_unary(n, op, x) = word_of_bits(n, {k:num | op(word_bit(k, x))})",
		func(a *Argument, n *Expr[Nat], op *Arrow[Bool, Bool], x *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"both empty windows build zero",
				func(b *Argument) {
					b.Do(Simp(Fwd(machine_word.WordBitwiseUnaryDef), Fwd(machine_word.WordOfBitsDef)))
					b.Show(
						"the empty values agree",
						Basic())
				})
			a.Step(
				"the two constructions append the same digit to equal shorter windows",
				func(b *Argument, ih Fact) {
					b.Do(Simp(Fwd(machine_word.WordBitwiseUnaryDef), Fwd(machine_word.WordOfBitsDef), Fwd(ih)))
					b.Show(
						"membership in the operation's table reads its result",
						BySets())
				})
		}),
})}

// BitwiseBinaryAsBits — a binary window combinator builds the set of
// positions where its operation holds on the two operand bits. The
// recursive clauses append exactly the set builder's weighted digit.
var BitwiseBinaryAsBits = bitwiseBinaryAsBitsThm{family.Add(registry.ProofEntry{
	Name: "BitwiseBinaryAsBits",
	Key:  "prop_74e7ee1cd16d0beb",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool → bool). ∀x y:num. "+
			"    word_bitwise_binary(n, op, x, y) = "+
			"    word_of_bits(n, {k:num | op(word_bit(k, x), word_bit(k, y))})",
		func(a *Argument, n *Expr[Nat], op *Arrow2[Bool, Bool, Bool], x, y *Expr[Nat]) {
			a.Induct(n)
			a.Base(
				"both empty windows build zero",
				func(b *Argument) {
					b.Do(Simp(Fwd(machine_word.WordBitwiseBinaryDef), Fwd(machine_word.WordOfBitsDef)))
					b.Show(
						"the empty values agree",
						Basic())
				})
			a.Step(
				"the two constructions append the same digit to equal shorter windows",
				func(b *Argument, ih Fact) {
					b.Do(Simp(Fwd(machine_word.WordBitwiseBinaryDef), Fwd(machine_word.WordOfBitsDef), Fwd(ih)))
					b.Show(
						"membership in the operation's table reads its result",
						BySets())
				})
		}),
})}

// BitwiseBinaryBound — a binary window value has the set builder's
// range bound, read through its operation's position table.
var BitwiseBinaryBound = bitwiseBinaryBoundThm{family.Add(registry.ProofEntry{
	Name: "BitwiseBinaryBound",
	Key:  "prop_155931b082366bae",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool → bool). ∀x y:num. word_bitwise_binary(n, op, x, y) < nat_pow(2, n)",
		func(a *Argument, n *Expr[Nat], op *Arrow2[Bool, Bool, Bool], x, y *Expr[Nat]) {
			a.Show(
				"the set builder stays below the window's weight",
				By(BitwiseBinaryAsBits.At(n, op, x, y), WordOfBitsBound))
		}),
})}

// ---------------------------------------------------------------------------
// BitwiseBinaryProjection — a bit of the binary combinator reads its
// operation's position table, restricted to the window.
var BitwiseBinaryProjection = bitwiseBinaryProjectionThm{family.Add(registry.ProofEntry{
	Name: "BitwiseBinaryProjection",
	Key:  "prop_678f6af23b759986",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool → bool). ∀x y:num. ∀k:num. "+
			"    word_bit(k, word_bitwise_binary(n, op, x, y)) ⇔ (op(word_bit(k, x), word_bit(k, y)) ∧ k < n)",
		func(a *Argument, n *Expr[Nat], op *Arrow2[Bool, Bool, Bool], x, y, k *Expr[Nat]) {
			a.Show(
				"the set builder reads the operation's table inside the window",
				BySets(
					BitwiseBinaryAsBits.At(n, op, x, y),
					BitOfBitSet.At(n, k,
						a.TermAs[Set[Nat]]("{j:num | op(word_bit(j, x), word_bit(j, y))}"))))
		}),
})}

// ---------------------------------------------------------------------------
// BitwiseUnaryBound · BitwiseUnaryProjection — the unary mirrors
// ---------------------------------------------------------------------------

// BitwiseUnaryBound — a unary window value has the set builder's
// range bound, read through its operation's position table.
var BitwiseUnaryBound = bitwiseUnaryBoundThm{family.Add(registry.ProofEntry{
	Name: "BitwiseUnaryBound",
	Key:  "prop_72bc8c341c5ddca",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool). ∀x:num. word_bitwise_unary(n, op, x) < nat_pow(2, n)",
		func(a *Argument, n *Expr[Nat], op *Arrow[Bool, Bool], x *Expr[Nat]) {
			a.Show(
				"the set builder stays below the window's weight",
				By(BitwiseUnaryAsBits.At(n, op, x), WordOfBitsBound))
		}),
})}

// BitwiseUnaryProjection — a bit of the unary combinator reads its
// operation's position table, restricted to the window.
var BitwiseUnaryProjection = bitwiseUnaryProjectionThm{family.Add(registry.ProofEntry{
	Name: "BitwiseUnaryProjection",
	Key:  "prop_95b1820b5f4d25f1",
	Build: family.Theorem(
		"∀n:num. ∀op:(bool → bool). ∀x:num. ∀k:num. "+
			"    word_bit(k, word_bitwise_unary(n, op, x)) ⇔ (op(word_bit(k, x)) ∧ k < n)",
		func(a *Argument, n *Expr[Nat], op *Arrow[Bool, Bool], x, k *Expr[Nat]) {
			a.Show(
				"the set builder reads the operation's table inside the window",
				BySets(
					BitwiseUnaryAsBits.At(n, op, x),
					BitOfBitSet.At(n, k, a.TermAs[Set[Nat]]("{j:num | op(word_bit(j, x))}"))))
		}),
})}

// ---------------------------------------------------------------------------
// BitOfAnd · BitOfOr — the width-free projections
// ---------------------------------------------------------------------------

// BitOfAnd — a bit of the conjunction is the conjunction of bits, at
// every position of every pair of operands: BitAnd with the window
// dissolved. Unfolding the door hands the goal to BitwiseBinaryProjection at
// the operator's own window x + y; the window conjunct absorbs because
// a set bit of x already sits below x + y — a value sits under its own
// power, and BitBelowBound reads the bound at the window.
var BitOfAnd = bitOfAndThm{family.Add(registry.ProofEntry{
	Name: "BitOfAnd",
	Key:  "prop_415ea2112fe9f71d",
	Build: family.Theorem(
		"∀x y:num. ∀k:num. word_bit(k, word_and(x, y)) ⇔ (word_bit(k, x) ∧ word_bit(k, y))",
		func(a *Argument, x, y, k Term) {
			wordAndDef := a.Ctx().ConstDefNormalized("word_and")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the conjunction is the "+
					"conjunction of bits inside the operator's own window",
				"word_bit(k, word_and(x, y)) ⇔ ((word_bit(k, x) ∧ word_bit(k, y)) ∧ (k < x + y))",
				By(wordAndDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			a.Show(
				"a set bit of the conjunction carries x's bit, and a "+
					"set bit of x carries the window — the guard absorbs",
				By(Normalized, projRead, covX))
		}),
})}

// BitOfOr — a bit of the disjunction is the disjunction of bits, at
// every position of every pair of operands: BitOr with the window
// dissolved. The shape is BitOfAnd's; here a set bit of the OR only
// promises a set bit of ONE operand, so both operands carry their
// window facts.
var BitOfOr = bitOfOrThm{family.Add(registry.ProofEntry{
	Name: "BitOfOr",
	Key:  "prop_d0ad97d3ec18ffa6",
	Build: family.Theorem(
		"∀x y:num. ∀k:num. word_bit(k, word_or(x, y)) ⇔ (word_bit(k, x) ∨ word_bit(k, y))",
		func(a *Argument, x, y, k Term) {
			wordOrDef := a.Ctx().ConstDefNormalized("word_or")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the disjunction is the "+
					"disjunction of bits inside the operator's own window",
				"word_bit(k, word_or(x, y)) ⇔ ((word_bit(k, x) ∨ word_bit(k, y)) ∧ (k < x + y))",
				By(wordOrDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			yCover := a.Have(
				"and y likewise",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAddLeft, x, y),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans,
						y, a.Term("nat_pow(2, y)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			covY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < x + y)",
				By(yCover, BitBelowBound))
			a.Show(
				"whichever operand carries the bit carries the window — the guard absorbs",
				By(Normalized, projRead, covX, covY))
		}),
})}

// ---------------------------------------------------------------------------
// BitOfXor — the width-free bit read of the difference
// ---------------------------------------------------------------------------

// BitOfXor — a bit of the difference is the disagreement of the
// operands' bits, at EVERY position and with no width in sight: the
// strong, window-absorbed reading the laws below spend. The projection
// reports the door's own spelling of exactly-one guarded by the window
// x + y; a bit the operands disagree on is a set bit of one of them,
// which sits below the window (BitBelowBound over the operand's own
// power), so the guard adds nothing — and the (a ∨ b) ∧ ¬(a ∧ b) vs
// ¬(a ⇔ b) propositional gap closes in the refute.
var BitOfXor = bitOfXorThm{family.Add(registry.ProofEntry{
	Name: "BitOfXor",
	Key:  "prop_9ddf32e22c3ea352",
	Build: family.Theorem(
		"∀x y:num. ∀k:num. word_bit(k, word_xor(x, y)) ⇔ (¬word_bit(k, x) ⇔ word_bit(k, y))",
		func(a *Argument, x, y, k Term) {
			wordXorDef := a.Ctx().ConstDefNormalized("word_xor")
			window := a.Term("x + y")

			projRead := a.Have(
				"unfolding the door, a bit of the difference is the door's own spelling "+
					"of exactly-one at the operand bits, inside the operator's window",
				"word_bit(k, word_xor(x, y)) ⇔ "+
					"(((word_bit(k, x) ∨ word_bit(k, y)) ∧ ¬(word_bit(k, x) ∧ word_bit(k, y))) ∧ (k < x + y))",
				By(wordXorDef, BitwiseBinaryProjection))
			xCover := a.Have(
				"the window covers x — a value sits under its own power",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans,
						x, a.Term("nat_pow(2, x)"), a.Term("nat_pow(2, x + y)"))))
			yCover := a.Have(
				"and y likewise",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAddLeft, x, y),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans,
						y, a.Term("nat_pow(2, y)"), a.Term("nat_pow(2, x + y)"))))
			covX := a.Have(
				"so a set bit of x sits below the window",
				"word_bit(k, x) ⇒ (k < x + y)",
				By(xCover, BitBelowBound))
			covY := a.Have(
				"and of y",
				"word_bit(k, y) ⇒ (k < x + y)",
				By(yCover, BitBelowBound))
			a.Show(
				"a disagreement is a set bit of one operand, so the window rides "+
					"along — the two spellings of the difference are the same table",
				By(Normalized, projRead, covX, covY))
		}),
})}
