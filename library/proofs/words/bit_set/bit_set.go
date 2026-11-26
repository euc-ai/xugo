// bit_set.go — the chapter's position-set face: a word read as the set of
// places it holds.
//
// Five parts, marked by banners:
//
// - The bit set at zero and at one, and two facts about it at every value
// - The bitwise operations as set operations
// - Reading a word back off its place set
// - The built word: what the set builder makes, read back bit by bit
// - The set builder as a weight sum
//
// A word's third face. The bit face asks whether one place is held; this
// face takes them all at once, so a word becomes a set of numbers and the
// set operations become word operations — the meet of two words is the
// intersection of their place sets, the complement within a width is a
// set difference against that width's places.
//
// The face is TWO translations, and they are not symmetric. Reading a
// word as a set needs no constant at all: `{i | word_bit(i, x)}` is already
// the set, and it is width-free for the same reason the bit face is —
// which places x holds is a fact about x, and a bounded value holds none
// at or beyond its width. Building a word FROM a set does need one,
// because it truncates: a set may hold places the width does not reach,
// and `word_of_bits` is exactly the cut.

package bit_set

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"

	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/words/bit_arith"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The bit set at zero and at one, and two facts about it at every value
// ---------------------------------------------------------------------------
//
// Four readings of one translation. A place lies in `{i | word_bit(i, x)}`
// exactly when x holds it — that is the whole of what the set builder
// says — so every statement about the SET is a statement about which
// places are held, and the set driver is what carries it across: it
// unfolds the set vocabulary and refutes what is left. All each member
// has to supply is the bit fact the driver is left holding.
//
// The two computed values are the two the bit face already answers for,
// and the driver takes those answers as they stand.
//
// The last two hold at every value and mention no width, but for
// opposite reasons. Emptiness pins the value because bit extensionality
// does, and no width enters that. Finiteness genuinely needs one and has
// to PRODUCE it, the statement carrying none to receive: a value is
// smaller than its own power of two, which makes that power a covering
// width, and the places a value holds lie below any covering width.
// Below a width there are finitely many places, and that is the bound.

// BitSetOfZero — zero hands out the empty set of places.
var BitSetOfZero = bitSetOfZeroThm{family.Add(registry.ProofEntry{
	Name: "BitSetOfZero",
	Key:  "prop_7e808bc8c2963710",
	Build: family.Theorem(
		"{i:num | word_bit(i, 0)} = ∅",
		func(a *Argument) {
			a.Show(
				"a place in the set would be a place zero holds, and it holds none",
				BySets(word_bits.BitWordZero))
		}),
})}

// BitSetOfOne — one hands out the set holding position 0 alone.
//
// The bit face answers for one as an equivalence rather than as two
// separate facts, and an equivalence is already a membership condition,
// so the guard is all that stands between the two faces.
var BitSetOfOne = bitSetOfOneThm{family.Add(registry.ProofEntry{
	Name: "BitSetOfOne",
	Key:  "prop_c26f0fae44324d0b",
	Build: family.Theorem(
		"{i:num | word_bit(i, 1)} = {0}",
		func(a *Argument) {
			a.Show(
				"so the places one holds are exactly the single place 0",
				BySets(word_bits.BitWordOne))
		}),
})}

// BitSetEmpty — a value hands out the empty set exactly when it is zero.
//
// One direction is the member above, read at the value the case fixes.
// The other is bit extensionality: a value holding no place agrees with
// zero everywhere, and values agreeing everywhere are equal. Neither
// side mentions a width and neither needs one — BitsEqAll is the
// unbounded form, which finds a width covering both values by itself.
//
// This is what brings an argument carried out in sets — an intersection
// that misses, a mask that clears everything — back to a statement about
// a value.
var BitSetEmpty = bitSetEmptyThm{family.Add(registry.ProofEntry{
	Name: "BitSetEmpty",
	Key:  "prop_77682ea35abe1462",
	Build: family.Theorem(
		"∀x:num. ({i:num | word_bit(i, x)} = ∅) ⇔ (x = 0)",
		func(a *Argument, x Term) {
			zero := a.Ctx().Numeral(0)

			a.Iff()
			a.Forward(
				"a value holding no place agrees with zero everywhere, and agreement pins it",
				func(b *Argument, noPlaces Fact) {
					holdsNothing := b.Have(
						"an empty set of places is no place held",
						"∀i:num. ¬word_bit(i, x)",
						BySets(noPlaces))
					agree := b.Have(
						"so x and zero hold the same places — neither holds any",
						"∀i:num. word_bit(i, x) ⇔ word_bit(i, 0)",
						By(Normalized, holdsNothing, word_bits.BitWordZero))

					b.Show(
						"and two values agreeing at every place are equal",
						By(agree, At(word_bits.BitsEqAll, x, zero)))
				})
			a.Backward(
				"at zero the set is empty outright",
				func(b *Argument, isZero Fact) {
					b.Show(
						"read place by place, the two sets are the same condition",
						BySets(isZero, BitSetOfZero))
				})
		}),
})}

// BitSetIsFinite — the set of places a value holds is finite, at every
// value and with no width in sight.
//
// A set of numbers need not be finite, so this is what an argument
// phrased in place sets needs and what being a set of places does not
// supply. The width that supplies it is not in the statement and has to
// be found; the value itself is where it comes from, since a value is
// smaller than its own power of two. That puts the set inside the
// numbers below the value, and those are finite for reasons of their
// own.
var BitSetIsFinite = bitSetIsFiniteThm{family.Add(registry.ProofEntry{
	Name: "BitSetIsFinite",
	Key:  "prop_f5432fb8ba698a6f",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x:num.",
			Conclusion: "finite({i:num | word_bit(i, x)})",
			Abbrev: Abbrev{
				{Name: "heldPlaces", Text: "{i:num | word_bit(i, x)}"},
				{Name: "lowerPlaces", Text: "{i:num | i < x}"},
			},
		},
		func(a *Argument, x Term) {
			below := a.Have(
				"every place x holds lies below x itself",
				"∀k:num. word_bit(k, x) ⇒ (k < x)",
				// BitBelowBound stays bare: the ground covering bound is
				// what reads a width out of it, and the place it speaks
				// about is quantified in the claim, so there is none to name.
				By(At(nat_order.LessThanPowTwoSelf, x), word_bits.BitBelowBound)) // x < nat_pow(2, x)

			within := a.Have(
				"so those places sit among the numbers below x",
				"«heldPlaces» ⊆ «lowerPlaces»",
				// Wide: the place is the set builder's own bound variable,
				// so there is no witness to name it by.
				BySets(below))

			a.Show(
				"and a set inside the finitely many numbers below a bound is itself finite",
				By(
					within,
					// finite(«lowerPlaces») ∧ «heldPlaces» ⊆ «lowerPlaces»
					// ⇒ finite(«heldPlaces») — subset first, container second
					At(finite_set.FiniteSubset, a.Term("«heldPlaces»"), a.Term("«lowerPlaces»")),
					// Bare: the segment law discharges the container's
					// finiteness at its ∀-form install, with no instance to name.
					num_segment.FiniteBelowStrict))
		}),
})}

// ---------------------------------------------------------------------------
// The bitwise operations as set operations
// ---------------------------------------------------------------------------
//
// the bitwise operations as set operations: once a word is read as the
// set of places it holds, the meet of two words becomes the
// intersection of their place sets and the complement within a width
// becomes a difference against that width's places. Each law is the
// same two-step move — read the operation's places off the bit face,
// then cross from a pointwise equivalence to an equation of sets — and
// the crossing needs no plumbing lemma about `∈` or the set builder:
// the membership-mode set driver unfolds that vocabulary itself, which
// is the whole of its content.
//
// The meet's law is width-free because the meet is: its window x + y
// already covers every place either operand holds. The complement's
// keeps one, because complementing IS a fact about a window — the
// places it holds are exactly the CLEAR places below n — and that is
// what makes its right-hand side a difference against the window's own
// places rather than against a universe.

// meetHoldsBothPlaces is BitOfAnd read at the pair in scope, x and y:
// the meet holds exactly the places both operands hold — the pointwise
// fact both the intersection law and the disjointness law cross from.
// Two members spend it.
func meetHoldsBothPlaces(a *Argument) Fact {
	return a.Have(
		"a place belongs to the meet exactly when both operands hold it",
		"∀k:num. word_bit(k, word_and(x, y)) ⇔ (word_bit(k, x) ∧ word_bit(k, y))",
		Derive(func(b *Argument) {
			b.Fix() // k — spelled in the claim
			b.Do(By(word_bits.BitOfAnd))
		}))
}

// BitSetOfAnd — a meet holds exactly the places both operands hold, so
// under the translation it is an intersection. BitOfAnd already reads
// the meet's bit off the operands' at every position and every pair of
// operands; the pointwise reading is taken at THIS pair first, so that
// what crosses to the sets is a statement about x and y rather than a
// law the driver would have to instantiate.
var BitSetOfAnd = bitSetOfAndThm{family.Add(registry.ProofEntry{
	Name: "BitSetOfAnd",
	Key:  "prop_248bf738f82f7559",
	Build: family.Theorem(
		"∀x y:num. "+
			"    {i:num | word_bit(i, word_and(x, y))} = {i:num | word_bit(i, x)} ∩ {i:num | word_bit(i, y)}",
		func(a *Argument, x, y Term) {
			meetBits := meetHoldsBothPlaces(a)
			a.Show(
				"and that is what membership in the intersection asks",
				BySets(meetBits))
		}),
})}

// BitSetOfNot — a complement holds exactly the places below its width
// that the operand leaves clear, so under the translation it is a
// difference against the window's places. The window the projection
// guards by IS the width here (complement is the one operation whose
// width is its own window), so the pointwise reading comes off the
// definition and the generic projection with no window to reconcile.
var BitSetOfNot = bitSetOfNotThm{family.Add(registry.ProofEntry{
	Name: "BitSetOfNot",
	Key:  "prop_cbf71bb32a83f0b1",
	Build: family.Theorem(
		"∀n x:num. {i:num | word_bit(i, word_not(n, x))} = {i:num | i < n} ∖ {i:num | word_bit(i, x)}",
		func(a *Argument, n, x Term) {
			wordNotDef := a.Ctx().ConstDefNormalized("word_not")
			complementBits := a.Have(
				"a place of the complement is a place below the width that x leaves clear",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ (k < n ∧ ¬word_bit(k, x))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(wordNotDef, word_bits.BitwiseUnaryProjection))
				}))
			a.Show(
				"and that is exactly what the width's places admit once x's are taken away",
				BySets(complementBits))
		}),
})}

// ---------------------------------------------------------------------------
// Reading a word back off its place set
// ---------------------------------------------------------------------------
//
// reading a word back off its place set: the translation loses
// nothing. Two words holding the same places are the same word, and
// two words meet in the zero word exactly when their place sets meet
// in nothing — so an equation between words and a disjointness between
// sets are one statement said twice.
//
// Both members cross the same bridge, and each states what it wants at
// the bits before crossing. Unbounded bit extensionality (BitsEqAll)
// turns agreement at every place back into an equation of values,
// asking no width; the set driver then carries that pointwise reading
// over to `∈`, exactly as it does for the two operation laws above.
//
// Where a close below declares Normalized, the reason is always the
// same one: these arguments pass ∀-headed equivalences around, the
// clause form the refuter works in tears the quantifier off, and one
// simplification between the installs and the close puts it back
// beside the goal.

// EqByBitSet — a word is determined by the places it holds. The bit
// reading is where the content is: agreeing at every place pins the
// values equal, with no width asked, and equal words agree at every
// place. Reading that through the place sets is the driver's step.
var EqByBitSet = eqByBitSetThm{family.Add(registry.ProofEntry{
	Name: "EqByBitSet",
	Key:  "prop_1bae7bd19e60f68a",
	Build: family.Theorem(
		"∀x y:num. ({i:num | word_bit(i, x)} = {i:num | word_bit(i, y)}) ⇔ (x = y)",
		func(a *Argument, x, y Term) {
			agreeIffEqual := a.Have(
				"two words agree at every place exactly when they are the same word",
				"(∀k:num. word_bit(k, x) ⇔ word_bit(k, y)) ⇔ (x = y)",
				// Grounded: extensionality is wanted at this pair and no
				// other, and the cite's free pair would otherwise unify
				// against every bit literal in scope.
				By(Normalized, At(word_bits.BitsEqAll, x, y)))
			a.Show(
				"and two place sets are equal exactly when they admit the same places",
				BySets(agreeIffEqual))
		}),
})}

// AndEqZero — a meet vanishes exactly when the two operands share no
// place. The bit-level content is stated in full first — the meet is
// the zero word precisely when no position carries both bits — and
// disjointness of the place sets is that same condition read through
// the translation.
var AndEqZero = andEqZeroThm{family.Add(registry.ProofEntry{
	Name: "AndEqZero",
	Key:  "prop_5ce3a4b7d6d4171",
	Build: family.Theorem(
		"∀x y:num. word_and(x, y) = 0 ⇔ disjoint({i:num | word_bit(i, x)}, {i:num | word_bit(i, y)})",
		func(a *Argument, x, y Term) {
			meet := a.Term("word_and(x, y)")
			zero := a.Ctx().Numeral(0)

			meetBits := meetHoldsBothPlaces(a)
			forward := a.Have(
				"a vanished meet holds nothing, so no place is held by both operands",
				"(word_and(x, y) = 0) ⇒ (∀k:num. ¬(word_bit(k, x) ∧ word_bit(k, y)))",
				Derive(func(b *Argument) {
					vanished := b.Assume()
					k := b.Fix()
					b.Show(
						"a place held by both would be a place of the zero word",
						// The vanishing equation also has to reach INSIDE
						// the meet's bit, which is the same simplification.
						By(Normalized, vanished, meetBits.At(k), At(word_bits.BitWordZero, k)))
				}))
			backward := a.Have(
				"and with no place held by both, the meet holds exactly what the zero word does",
				"(∀k:num. ¬(word_bit(k, x) ∧ word_bit(k, y))) ⇒ (word_and(x, y) = 0)",
				Derive(func(b *Argument) {
					noCommon := b.Assume()
					agree := b.Have(
						"neither the meet nor the zero word holds any place",
						"∀k:num. word_bit(k, word_and(x, y)) ⇔ word_bit(k, 0)",
						Derive(func(c *Argument) {
							k := c.Fix()
							c.Do(By(noCommon.At(k), meetBits.At(k), At(word_bits.BitWordZero, k)))
						}))
					b.Show(
						"so agreement at every place pins the meet equal to zero",
						// Grounded, as EqByBitSet's — here at the meet and
						// the zero word.
						By(agree, At(word_bits.BitsEqAll, meet, zero)))
				}))
			vanishes := a.Have(
				"so the meet vanishes exactly when no place carries both bits",
				"(word_and(x, y) = 0) ⇔ (∀k:num. ¬(word_bit(k, x) ∧ word_bit(k, y)))",
				By(forward, backward))
			a.Show(
				"and sharing no place is what disjointness of the two place sets says",
				BySets(vanishes))
		}),
})}

// ---------------------------------------------------------------------------
// The built word: what the set builder makes, read back bit by bit
// ---------------------------------------------------------------------------
//
// the built word: four members, one method. word_bits.BitOfBitSet reads any built
// word's bits — a place is held exactly when the window reaches it and
// the set holds it — and unbounded bit extensionality (BitsEqAll) turns
// pointwise agreement back into an equation of values, so every law
// here is proved by computing both sides' place tables and watching
// them coincide.
//
// The first two say the building direction loses nothing it could keep.
// A reduced value rebuilt from its own places is itself — the covering
// width is load-bearing, because the cut forgets every place at or
// beyond the window and an unreduced value holds such a place. And two
// builds at one window are equal exactly when their sets agree below
// it: the window is precisely how much of a set the builder consults.
//
// The last two recognize familiar residues as builds. Truncation keeps
// handing this face two values — a mask cut into a window, a power cut
// into a window — and each is the build from one of the simplest sets
// there are: the places below m, and the single place i. Both proofs
// read the residue's bits through BitWord and the untruncated value's
// own places, then cross by extensionality as above.

// WordOfBitSet — the round trip at a value: a reduced word rebuilt from
// its own place set is itself. The guard earns its place — the builder
// cuts at n, so a value holding a place at or beyond n would lose it;
// sitting below the window's weight is exactly holding no such place
// (BitBelowBound), which is what discharges the rebuild's window guard
// at every held place.
var WordOfBitSet = wordOfBitSetThm{family.Add(registry.ProofEntry{
	Name: "WordOfBitSet",
	Key:  "prop_24e1212fdbc54a09",
	Build: family.Theorem(
		Statement{
			Binders: "∀n w:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n)",
			},
			Conclusion: "w = word_of_bits(n, {i:num | word_bit(i, w)})",
		},
		func(a *Argument, n, w Term, wBound Fact) {
			built := a.Term("word_of_bits(n, {i:num | word_bit(i, w)})")

			agree := a.Have(
				"the value and its rebuild hold the same places",
				"∀k:num. word_bit(k, w) ⇔ word_bit(k, word_of_bits(n, {i:num | word_bit(i, w)}))",
				Derive(func(b *Argument) {
					k := b.Fix()
					below := b.Have(
						"a held place lies below the covering width",
						"word_bit(k, w) ⇒ k < n",
						// Bare, as BitSetIsFinite's: the bound's inner ∀
						// grounds at the claim's own place.
						By(wBound, word_bits.BitBelowBound))
					b.Show(
						"the rebuild's bit is membership under the window guard; "+
							"membership is the value's own bit, and the guard is free",
						BySets(below, At(word_bits.BitOfBitSet, n, k, b.Term("{i:num | word_bit(i, w)}"))))
				}))

			a.Show(
				"and agreement at every place returns the value",
				By(agree, At(word_bits.BitsEqAll, w, built)))
		}),
})}

// EqByBitSetBelow — the builder is injective up to agreement below the
// window: two builds at one window are equal exactly when their sets
// admit the same places below it. Both directions are word_bits.BitOfBitSet's
// reading — one crossed to the values by extensionality, the other
// carried through the equation itself.
var EqByBitSetBelow = eqByBitSetBelowThm{family.Add(registry.ProofEntry{
	Name: "EqByBitSetBelow",
	Key:  "prop_4164aa39c8ac33d1",
	Build: family.Theorem(
		"∀n:num. ∀s t:set(num). "+
			"    (∀i:num. i < n ⇒ ((i ∈ s) ⇔ (i ∈ t))) ⇔ (word_of_bits(n, s) = word_of_bits(n, t))",
		func(a *Argument, n, s, t Term) {
			a.Iff()
			a.Forward(
				"sets agreeing below the window build words holding the same places, and agreement pins them equal",
				func(b *Argument, agree Fact) {
					holdSame := b.Have(
						"the two builds hold the same places",
						"∀k:num. word_bit(k, word_of_bits(n, s)) ⇔ word_bit(k, word_of_bits(n, t))",
						Derive(func(c *Argument) {
							k := c.Fix()
							c.Show(
								"both agree read as membership under one guard, and below it the memberships agree",
								By(Normalized, agree.At(k), At(word_bits.BitOfBitSet, n, k, s), At(word_bits.BitOfBitSet, n, k, t)))
						}))
					b.Show(
						"and agreement at every place pins the builds equal",
						By(holdSame, At(word_bits.BitsEqAll, b.Term("word_of_bits(n, s)"), b.Term("word_of_bits(n, t)"))))
				})
			a.Backward(
				"equal builds agree below the window: each membership "+
					"is its build's bit, and the builds are one word",
				func(b *Argument, eq Fact) {
					i := b.Fix()
					inWin := b.Assume()
					b.Show(
						"below the window each side's membership is its own build's bit at i",
						By(inWin, eq, At(word_bits.BitOfBitSet, n, i, s), At(word_bits.BitOfBitSet, n, i, t)))
				})
		}),
})}

// MaskAsBitSet — the m-bit mask truncated into width n is the build
// from the places below m. The complement of zero holds exactly the
// places below m, reduction cuts them to n, and bit extensionality
// identifies that table with the set builder's.
var MaskAsBitSet = maskAsBitSetThm{family.Add(registry.ProofEntry{
	Name: "MaskAsBitSet",
	Key:  "prop_2924383e6bacd822",
	Build: family.Theorem(
		Statement{
			Binders:    "∀m n:num.",
			Conclusion: "rem(nat_pow(2, m) - 1, nat_pow(2, n)) = word_of_bits(n, {i:num | i < m})",
		},
		func(a *Argument, m, n *Expr[Nat]) {
			maskBits := a.Have(
				"the m-mask holds exactly the places below m",
				"∀k:num. word_bit(k, word_not(m, 0)) ⇔ k < m",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"zero leaves every place clear, so its complement takes every place the window reaches",
						By(word_bits.BitNot.At(m, b.Ctx().Nat(0), k), word_bits.BitWordZero))
				}))
			residueBits := a.Have(
				"truncating the mask keeps exactly the places below both widths",
				"∀k:num. word_bit(k, rem(nat_pow(2, m) - 1, nat_pow(2, n))) ⇔ (k < m ∧ k < n)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					wordBitDef := b.Ctx().ConstDefNormalized("word_bit")
					b.Show(
						"the residue's bit is the mask's own inside the window, and the mask is two to the m minus one",
						By(maskBits.At(k), wordBitDef, word_bits.BitWord, bit_arith.AllOnes))
				}))
			builtBits := a.Have(
				"the build keeps exactly the same places",
				"∀k:num. word_bit(k, word_of_bits(n, {i:num | i < m})) ⇔ (k < n ∧ k < m)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"the build's bit is membership below m, under the window guard",
						BySets(word_bits.BitOfBitSet.At(n, k, b.TermAs[Set[Nat]]("{i:num | i < m}"))))
				}))
			a.Show(
				"two values holding the same places are one value",
				By(
					residueBits,
					builtBits,
					word_bits.BitsEqAll.At(
						a.TermAs[Nat]("rem(nat_pow(2, m) - 1, nat_pow(2, n))"),
						a.TermAs[Nat]("word_of_bits(n, {i:num | i < m})"))))
		}),
})}

// SingletonBitSet — truncating a power of two builds the singleton
// containing its place: BitPowTwo identifies the held place, BitWord
// cuts it to the window, and bit extensionality identifies the values.
var SingletonBitSet = singletonBitSetThm{family.Add(registry.ProofEntry{
	Name: "SingletonBitSet",
	Key:  "prop_1a1325ceea4745a3",
	Build: family.Theorem(
		"∀n i:num. rem(nat_pow(2, i), nat_pow(2, n)) = word_of_bits(n, {i})",
		func(a *Argument, n, i *Expr[Nat]) {
			residueBits := a.Have(
				"truncating the power keeps its place exactly when the window reaches it",
				"∀k:num. word_bit(k, rem(nat_pow(2, i), nat_pow(2, n))) ⇔ (k = i ∧ k < n)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					wordBitDef := b.Ctx().ConstDefNormalized("word_bit")
					b.Show(
						"the residue's bit is the power's own inside the window",
						By(word_bits.BitPowTwo.At(i, k), wordBitDef, word_bits.BitWord))
				}))
			builtBits := a.Have(
				"the build from the single place keeps exactly the same bits",
				"∀k:num. word_bit(k, word_of_bits(n, {i})) ⇔ (k < n ∧ k = i)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Show(
						"the build's bit is membership in the singleton, under the window guard",
						BySets(word_bits.BitOfBitSet.At(n, k, b.TermAs[Set[Nat]]("{i}"))))
				}))
			a.Show(
				"two values holding the same places are one value",
				By(
					residueBits,
					builtBits,
					word_bits.BitsEqAll.At(
						a.TermAs[Nat]("rem(nat_pow(2, i), nat_pow(2, n))"),
						a.TermAs[Nat]("word_of_bits(n, {i})"))))
		}),
})}

// ---------------------------------------------------------------------------
// The set builder as a weight sum
// ---------------------------------------------------------------------------
//
// the set builder as a weight sum: `word_of_bits` is the sum its name
// promises — the weights of the held places below the window, added
// up. One sentence read three ways. At the sum itself
// (WordOfBitsAsSum), the recursion and the summation build the same
// number place by place. Under the window's reduction
// (WordOfBitsAsWord), the restricted sum is already reduced, so the
// remainder is free. And with the window cut dropped
// (WordOfBitsAsWordFinite), the places at or beyond the window
// contribute a multiple of the window's weight, which the remainder
// discards — provided the set is finite, because a sum with infinite
// support is 0 by convention while the low places may be inhabited.
//
// This is the face's bridge into summation arithmetic: an argument
// about a word built from a set — a mask's value, a union's weight —
// becomes an argument about nat_sum, where the finite-summation theory
// does the work.
//
// Where a close below declares Normalized, the reason differs from the
// place-set parts above: the ground nat_sum-law instances carry β-redexes
// — `(λi. …)(k)` — that only the Basic pass reduces, so one
// simplification stands between the installs and the close.

// WordOfBitsAsSum — the built value is the sum of the held places'
// weights below the window.
//
// The recursion computes the sum place by place, so the argument is
// the induction that says so, followed by the bookkeeping that moves
// the membership from the summand into the index set. The induction
// proves the builder equal to the sum over EVERY place below the
// window of the weighted digit nat_pow(2, i) * bit_value(i ∈ s): widening
// the window by one place adds exactly that place's weighted digit to
// both sides — machine_word.WordOfBitsDef on the left, the segment sum's own
// recurrence on the right. What remains is summand arithmetic: a
// weighted digit is the weight where the set holds the place and 0
// elsewhere, a summand that vanishes off a set is that set's own
// restricted sum, and the restricted index set — below the window and
// in s, each said once — is the window set as stated.
var WordOfBitsAsSum = wordOfBitsAsSumThm{family.Add(registry.ProofEntry{
	Name: "WordOfBitsAsSum",
	Key:  "prop_35bb46c9e3286255",
	Build: family.Theorem(
		"∀n:num. ∀s:set(num). word_of_bits(n, s) = sum({i:num | i < n ∧ (i ∈ s)}, λi:num. nat_pow(2, i))",
		func(a *Argument, n, s Term) {
			plain := a.Have(
				"the built value is the weighted-digit sum over every place below the window",
				"∀k:num. ∀t:set(num). "+
					"    word_of_bits(k, t) = sum({i:num | i < k}, λi:num. nat_pow(2, i) * bit_value(i ∈ t))",
				Derive(func(b *Argument) {
					k := b.Binder("k")
					b.Induct(k)
					b.Base(
						"an empty window builds zero, and the sum below zero is empty",
						func(c *Argument) {
							c.Fix() // t — spelled in the witness below
							c.Show(
								"both sides are zero",
								By(
									machine_word.WordOfBitsDef,
									At(nat_sum.BelowClauses, c.Ctx().Numeral(0),
										c.Term("λi:num. nat_pow(2, i) * bit_value(i ∈ t)"))))
						})
					b.Step(
						"widening by one place adds that place's weighted digit to both sides",
						func(c *Argument, ih Fact) {
							t := c.Fix()
							c.Show(
								"the clauses open the builder, the segment recurrence "+
									"opens the sum, and the hypothesis matches what is left",
								By(
									Normalized,
									ih.At(t),
									At(machine_word.WordOfBitsDef, k, t),
									At(nat_sum.BelowClauses, k,
										c.Term("λi:num. nat_pow(2, i) * bit_value(i ∈ t)"))))
						})
				}))

			// The restriction law's image writes the two conditions as
			// memberships, ambient set second; the driver identifies that
			// spelling with the window set as stated.
			setForm := a.Have(
				"membership below the window, said as the restriction law says it, is the window set",
				"{x:num | (x ∈ s) ∧ (x ∈ {i:num | i < n})} = {i:num | i < n ∧ (i ∈ s)}",
				BySets())

			a.Do(CalcEq(
				Leg(
					a.Term("sum({i:num | i < n}, λi:num. nat_pow(2, i) * bit_value(i ∈ s))"),
					"the recursion's own reading of the builder, at this window and set",
					By(plain.At(n, s))),
				Leg(
					a.Term("sum({i:num | i < n}, λi:num. COND(i ∈ s, nat_pow(2, i), 0))"),
					"a place's weighted digit is its weight where the set holds it and nothing elsewhere",
					Congr(),
					Funext(),
					StripQuant(),
					Unfold(machine_word.BitValueDef),
					By(nat_arith.MulClauses)),
				FinalLeg(
					"and a summand that vanishes off the set is the restricted set's own sum",
					// Backward: put the index set into the restriction law's
					// own spelling, so the leg IS the law's instance. The law
					// stays wide: grounding it by hand leaves β-redexes the
					// closer cannot reduce, while the wide install applies it
					// to the leg and reduces as it goes.
					setForm.RwRev(),
					By(nat_sum.Restrict)),
			))
		}),
})}

// WordOfBitsAsWord — reducing the restricted weight sum at the window's
// weight gives the built value back untouched.
//
// The reduction is free because there is nothing to reduce: the sum
// is the built value (WordOfBitsAsSum), and the built value sits below
// the window's weight (word_bits.WordOfBitsBound), so the remainder returns it
// whole. This is the form a consumer meets when a word arrives as a
// reduction — the val-face operations all produce one — and wants it
// as a set's weight sum.
var WordOfBitsAsWord = wordOfBitsAsWordThm{family.Add(registry.ProofEntry{
	Name: "WordOfBitsAsWord",
	Key:  "prop_875b2b0dd917816c",
	Build: family.Theorem(
		"∀n:num. ∀s:set(num). "+
			"    rem(sum({i:num | i < n ∧ (i ∈ s)}, λi:num. nat_pow(2, i)), nat_pow(2, n)) = "+
			"    word_of_bits(n, s)",
		func(a *Argument, n, s Term) {
			asSum := a.Have(
				"the restricted sum is the built value",
				"word_of_bits(n, s) = sum({i:num | i < n ∧ (i ∈ s)}, λi:num. nat_pow(2, i))",
				By(WordOfBitsAsSum))
			// ↦ nat_mod(word_of_bits(n, s), nat_pow(2, n)) = word_of_bits(n, s)
			a.Do(asSum.RwRev())
			a.Show(
				"already below the window's weight, the value is its own remainder",
				By(
					word_bits.WordOfBitsBound,
					At(nat_div_mod.ModLessThan,
						a.Term("word_of_bits(n, s)"), a.Term("nat_pow(2, n)"))))
		}),
})}

// WordOfBitsAsWordFinite — for a finite set the window cut may be dropped
// from the sum: the unrestricted weight sum reduces to the same word.
//
// finite is load-bearing, not a convenience: nat_sum over a set of
// infinite support is 0 by convention, so the unrestricted sum of an
// infinite set forgets the low places entirely and the unguarded
// equation is false there.
//
// The proof is the splitting of a digit sum at the window.
// The split (at radix 2, every place counted once) writes the
// whole sum as a multiple of the window's weight plus the cut sum;
// the remainder discards the multiple, so the two sums agree modulo
// the window's weight; and the cut sum's remainder is the built word
// — WordOfBitsAsWord. The split law states each sum with its digit as a
// factor, so a small bridge folds the spare · 1 away first.
var WordOfBitsAsWordFinite = wordOfBitsAsWordFiniteThm{family.Add(registry.ProofEntry{
	Name: "WordOfBitsAsWordFinite",
	Key:  "prop_2ec62291b20823ae",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀s:set(num).",
			Hypotheses: []string{
				"finite(s)",
			},
			Conclusion: "rem(sum(s, λi:num. nat_pow(2, i)), nat_pow(2, n)) = word_of_bits(n, s)",
		},
		func(a *Argument, n, s Term, finite Fact) {
			timesOne := a.Have(
				"multiplying every term of a sum by one changes nothing",
				"∀f:(num → num). ∀A:set(num). sum(A, λi:num. f(i) * 1) = sum(A, f)",
				StripQuant(),
				Congr(),
				Funext(),
				By(nat_arith.MulClauses))

			// The three sums the split relates, as their index sets and
			// summands: a place's weight, the weight it carries once the
			// window is taken off it, and s's places on each side of the
			// window. everyPlaceOnce is the digit sequence counting each
			// place of s exactly once — the split law's b.
			weight := a.Term("λi:num. nat_pow(2, i)")
			weightPastWindow := a.Term("λi:num. nat_pow(2, i - n)")
			everyPlaceOnce := a.Term("λi:num. 1")
			belowWindow := a.Term("{i:num | i < n ∧ (i ∈ s)}")
			fromWindowUp := a.Term("{i:num | n ≤ i ∧ (i ∈ s)}")
			two := a.Ctx().Numeral(2)

			split := a.Have(
				"splitting s at the window: at or beyond it a "+
					"multiple of the window's weight, below it the cut sum",
				"nat_pow(2, n) * sum({i:num | n ≤ i ∧ i ∈ s}, λi:num. nat_pow(2, i - n)) + "+
					"sum({i:num | i < n ∧ i ∈ s}, λi:num. nat_pow(2, i)) = "+
					"sum(s, λi:num. nat_pow(2, i))",
				By(
					Normalized,
					finite,
					timesOne.At(weightPastWindow, fromWindowUp),
					timesOne.At(weight, belowWindow),
					timesOne.At(weight, s),
					At(nat_sum.DigitSumSplit, two, everyPlaceOnce, s, n)))

			cutAgrees := a.Have(
				"so the cut sum and the whole sum agree modulo the window's weight",
				"rem(sum({i:num | i < n ∧ i ∈ s}, λi:num. nat_pow(2, i)), nat_pow(2, n)) = "+
					"rem(sum(s, λi:num. nat_pow(2, i)), nat_pow(2, n))",
				// As a rewrite, not a premise: the discarded part enters
				// multiplied by nat_pow(2, n), and the closer reads a product of
				// two opaque terms as an atom it cannot see into. And
				// backwards — the claim names the whole sum, and the rewrite
				// expands it into the split, not the other way round.
				split.RwRev(),
				By(nat_div_mod.ModMultAdd))

			// ↦ nat_mod(cut sum, nat_pow(2, n)) = word_of_bits(n, s)
			a.Do(cutAgrees.RwRev())
			a.Show(
				"and the cut sum's remainder is the built word",
				By(WordOfBitsAsWord))
		}),
})}
