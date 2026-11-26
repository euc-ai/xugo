// bit_arith.go — the chapter's bitwise face read as ARITHMETIC: what
// the meet, the join, the difference and the complement do to a word's
// VALUE.
//
// `words/word_bits` reads a word one bit at a time and `words/machine_word`'s
// value face reads it as a number mod 2ⁿ; this chapter is where the
// two meet. Every law here is a statement about magnitude — a sum, an
// order, a difference from the mask — whose PROOF is a statement about
// positions, so each part takes its pointwise facts from the reading
// face and spends them on values.
//
// Four parts, marked by banners:
//
// - Sums: how the meet and the join distribute the value of a sum
// - No carry: what those identities say where the meet is empty
// - Order: the meet sits below both operands, the join above both
// - Complement: word_not(n, x) as 2ⁿ - 1 - x, and the sub-and-negate laws
// that follow from it
//
// The parts share one habit worth naming once. The binary operators
// window at x + y, which holds both operands whole, so their laws land
// width-free and the twins' relativization guard 1 ≤ n drops; word_not
// takes a width because complementing IS a window fact, so its laws
// carry one. Where a range guard survives, a position is genuinely
// being measured against the width.

package bit_arith

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/words/machine_word"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// --------------------------------------------------------------------------
// Sums: the meet and the join distribute the value of a sum
// --------------------------------------------------------------------------
//
// Adding two words is redistributing their set bits. At one position
// two bits go in; the meet holds a bit exactly when both do, the join
// exactly when either does, so between them the meet and the join hold
// exactly as many bits as the operands did — the digit table this file
// opens on. Nothing is created and nothing is lost, and because the
// meet and the join never carry against each other, the redistribution
// survives being weighted by place value and summed: over any window,
// the low parts of the two operands add up to the and-window plus the
// or-window (windowAddSplit, this part's keystone induction).
//
// The value-level laws are that identity read at ONE window — x + y,
// which word_and and word_or already carry as their own, and which is wide
// enough to hold both operands whole: a value sits under its own power
// and powers grow with the exponent, so reducing at 2^(x+y) changes
// neither operand. So the laws land width-free, hypothesis-free, with
// the moduli recognised as the operands themselves. AddAndOr says the
// sum IS meet plus join; OrAndXor splits the join into meet and
// difference; and composing the two says the sum is the difference
// with the meet counted TWICE — which is the carry, named.
//
// The window induction needs one arithmetic fact about the place it
// widens by, and that fact lives one layer down: doubling a modulus
// buys exactly one binary digit (nat_div_mod.ModDoubleSplit), read here
// at the weights 2ᵏ (modPowTwoSuc).
//
// What these identities are FOR is the next part, where the meet is
// empty and the three ways of combining two words fall together.

// ---------------------------------------------------------------------------
// bitValueAndOrSplit — the digit table
// ---------------------------------------------------------------------------

// bitValueAndOrSplit — at one position, the meet and the join hold
// exactly the bits the two operands did. The table has four rows, and
// each is one of bit_value's two readings on each of the four formulas,
// plus a zero clause of + to add the digits up. Nothing carries: the
// only row where both summands are set is the row where both operands
// are, and there both sides read 1 + 1.
var bitValueAndOrSplit = bitValueAndOrSplitThm{family.Add(registry.ProofEntry{
	Name: "bitValueAndOrSplit",
	Key:  "prop_5c8a54579ef35d72",
	Build: family.Theorem(
		"∀p q:bool. bit_value(p) + bit_value(q) = bit_value(p ∧ q) + bit_value(p ∨ q)",
		func(a *Argument, p, q Term) {
			zero := a.Ctx().Numeral(0)
			one := a.Ctx().Numeral(1)
			meet := a.Term("p ∧ q")
			join := a.Term("p ∨ q")

			a.Show(
				"row by row, each digit is decided by its own formula, "+
					"and the two sums meet on the zero clauses of +",
				// The four formulas are opaque booleans to the closer, so
				// each needs BOTH readings of its digit — the row where it
				// holds and the row where it does not. Normalized
				// clause-decomposes those eight ⇔ readings into the rows
				// before the refutation reads them; without it the refuter
				// lands on a harder leaf.
				By(
					Normalized,
					At(word_bits.BitValueEqOne, p),
					At(word_bits.BitValueEqZero, p),
					At(word_bits.BitValueEqOne, q),
					At(word_bits.BitValueEqZero, q),
					At(word_bits.BitValueEqOne, meet),
					At(word_bits.BitValueEqZero, meet),
					At(word_bits.BitValueEqOne, join),
					At(word_bits.BitValueEqZero, join),
					At(nat_arith.AddZero, one),
					At(nat_arith.AddLeftZeroClause, one),
					At(nat_arith.AddZero, zero)))
		}),
})}

// ---------------------------------------------------------------------------
// modPowTwoSuc — the window's arithmetic side
// ---------------------------------------------------------------------------

// modPowTwoSuc — widening the window by one place adds exactly that
// place: what a value keeps below 2ᵏ⁺¹ is what it keeps below 2ᵏ, plus
// its bit at k carrying the weight 2ᵏ.
//
// It is nat_div_mod.ModDoubleSplit — a residue at a doubled modulus
// splits into the quotient's parity digit weighted by the modulus,
// plus the residue at the modulus — read at m := 2ᵏ, where doubling is
// nat_pow's own step clause. The one thing left to identify is that the
// parity digit IS the bit: `word_bit` asks nat_odd of the shifted value, and
// BitValueOfOdd says a parity read as a digit is the bottom
// binary place.
//
// The place is weighted on the LEFT, matching how WordBitwiseBinaryClauses
// weights the window's step — one MulSym paid here rather than once
// per leg of the induction below.
var modPowTwoSuc = modPowTwoSucThm{family.Add(registry.ProofEntry{
	Name: "modPowTwoSuc",
	Key:  "prop_d7fea16fb4d00bda",
	Build: family.Theorem(
		"∀k x:num. "+
			"    rem(x, nat_pow(2, suc(k))) = "+
			"    nat_pow(2, k) * bit_value(word_bit(k, x)) + rem(x, nat_pow(2, k))",
		func(a *Argument, k, x Term) {
			two := a.Ctx().Numeral(2)
			weight := a.Term("nat_pow(2, k)")

			// ↦ nat_mod(x, nat_pow(2, suc(k))) = nat_pow(2, k) * bit_value(nat_odd(nat_div(x, nat_pow(2, k)))) + nat_mod(x, nat_pow(2, k))
			a.Do(Unfold(machine_word.WordBitDef))

			doubled := a.Have(
				"the next weight up is this one doubled — nat_pow's step clause, its factors swapped",
				"nat_pow(2, suc(k)) = nat_pow(2, k) * 2",
				By(
					At(nat_arith.NatPow, two, k),       // nat_pow(2, suc(k)) = 2·2ᵏ
					At(nat_arith.MulSym, two, weight))) // 2·2ᵏ = 2ᵏ·2
			swap := a.Have(
				"the digit's weight belongs on the left, where the window writes it",
				"rem(div(x, nat_pow(2, k)), 2) * nat_pow(2, k) = nat_pow(2, k) * rem(div(x, nat_pow(2, k)), 2)",
				// The claim IS the instance; the law closes it whole.
				Cite(nat_arith.MulSym))
			split := a.Have(
				"so the wider residue splits into a digit at this weight plus the narrower residue",
				"rem(x, nat_pow(2, k) * 2) = nat_pow(2, k) * rem(div(x, nat_pow(2, k)), 2) + rem(x, nat_pow(2, k))",
				// ↦ … = nat_mod(x ≫ k, 2) * nat_pow(2, k) + nat_mod(x, nat_pow(2, k)) — the
				// split in ModDoubleSplit's own orientation. Read as a
				// rewrite rather than listed as a premise: the closer keeps
				// two orderings of one product as distinct opaque atoms.
				swap.RwRev(),
				By(At(nat_arith.PowTwoNonzero, k), At(nat_div_mod.ModDoubleSplit, weight, x)))
			a.Show(
				"and that digit is the bit at k — a parity read as a digit is the bottom binary place",
				// Bare: with the two rewrites resident the law closes the
				// goal at its ∀-form install, so it names no instance.
				By(doubled, split, word_bits.BitValueOfOdd))
		}),
})}

// ---------------------------------------------------------------------------
// windowAddSplit — the window induction
// ---------------------------------------------------------------------------

// windowAddSplit — over any window, adding the operands' low parts is
// adding the and-window to the or-window. The keystone: it is the
// digit table lifted place by place, and it is why the value laws
// below need no carry analysis at all.
//
// By induction on the window. An empty window holds no places and
// keeps nothing of either operand, so both sides are 0 + 0. Widening
// by one place adds, on the left, each operand's new digit at weight
// 2ᵏ (modPowTwoSuc) and, on the right, each window's new digit at the
// same weight (WordBitwiseBinaryClauses) — and the two pairs of new digits are
// the two sides of the digit table, weighted, so they agree
// (bitValueAndOrSplit through distributivity) while the two pairs of old
// parts agree by the hypothesis. The chain below is that sentence:
// open both sides, gather new places apart from old parts, trade each
// pair, hand the places back.
var windowAddSplit = windowAddSplitThm{family.Add(registry.ProofEntry{
	Name: "windowAddSplit",
	Key:  "prop_2614fb8a2a6e7333",
	Build: family.Theorem(Statement{
		Binders: "∀k x y:num.",
		Conclusion: "rem(x, nat_pow(2, k)) + rem(y, nat_pow(2, k)) = " +
			"word_bitwise_binary(k, «WindowOpAnd», x, y) + word_bitwise_binary(k, «WindowOpOr», x, y)",
	},
		func(a *Argument) {
			a.Induct("k")
			a.Base(
				"the empty window holds no places, and below 2⁰ = 1 neither operand keeps anything",
				func(b *Argument) {
					b.Fix() // x — spelled in the claims below
					b.Fix() // y
					zero := b.Ctx().Numeral(0)
					two := b.Ctx().Numeral(2)
					// ModOne is cited bare: once the weight is known to be
					// one it rewrites both residues at its ∀-form install,
					// so no single instance is the premise.
					b.Show(
						"the empty window's weight is one, so nothing of x or y survives, "+
							"the empty windows add nothing, and nothing plus nothing is nothing",
						By(
							At(nat_arith.NatPow, two, zero),
							nat_div_mod.ModOne,
							machine_word.WordBitwiseBinaryDef,
							nat_arith.AddZero))
				})
			a.Step(
				"each side gains one weighted place — the two new places "+
					"trade by the digit table, the two old parts by the hypothesis",
				func(b *Argument, ih Fact) {
					x := b.Fix()
					y := b.Fix()
					// The chain's four stations are sums of the eight named
					// pieces below, so they are built rather than respelt.
					plus := b.Ctx().Const("+", MakeFun(NumType, MakeFun(NumType, NumType)))
					sum := func(u, v Term) Term { return plus.Apply(u, v) }

					// x's new digit, weighted
					newPlaceX := b.Term("nat_pow(2, k) * bit_value(word_bit(k, x))")
					newPlaceY := b.Term("nat_pow(2, k) * bit_value(word_bit(k, y))") // y's
					// what x kept below the old window
					oldPartX := b.Term("rem(x, nat_pow(2, k))")
					oldPartY := b.Term("rem(y, nat_pow(2, k))") // what y kept
					// the meet's new digit, weighted
					meetPlace := b.Term("nat_pow(2, k) * bit_value(word_bit(k, x) ∧ word_bit(k, y))")
					joinPlace := b.Term("nat_pow(2, k) * bit_value(word_bit(k, x) ∨ word_bit(k, y))") // the join's
					// the old and window
					andWindow := b.Term("word_bitwise_binary(k, «WindowOpAnd», x, y)")
					// the old or window
					orWindow := b.Term("word_bitwise_binary(k, «WindowOpOr», x, y)")

					digit := b.Have(
						"at the new place, the meet and the join hold exactly the operands' two bits",
						"bit_value(word_bit(k, x)) + bit_value(word_bit(k, y)) = "+
							"bit_value(word_bit(k, x) ∧ word_bit(k, y)) + bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(bitValueAndOrSplit))
					weighted := b.Have(
						"so the same trade holds once each digit carries the place's weight",
						"nat_pow(2, k) * bit_value(word_bit(k, x)) + nat_pow(2, k) * bit_value(word_bit(k, y)) = "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∧ word_bit(k, y)) + "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(digit, nat_arith.LeftAddDistrib))
					openAnd := b.Have(
						"widening the and window adds its weighted digit",
						"word_bitwise_binary(suc(k), «WindowOpAnd», x, y) = "+
							"word_bitwise_binary(k, «WindowOpAnd», x, y) + "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∧ word_bit(k, y))",
						By(machine_word.WordBitwiseBinaryDef))
					openOr := b.Have(
						"and the or window its",
						"word_bitwise_binary(suc(k), «WindowOpOr», x, y) = "+
							"word_bitwise_binary(k, «WindowOpOr», x, y) + "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(machine_word.WordBitwiseBinaryDef))

					regroup := ACRegroupWith(nat_arith.AddAC(b.Ctx()))
					b.Do(CalcEq(
						Leg(
							sum(sum(newPlaceX, oldPartX), sum(newPlaceY, oldPartY)),
							"each operand's wider residue opens into its new place on top of its old part",
							// Bare: modPowTwoSuc is wanted at both operands
							// at once, so no single instance is the premise.
							By(modPowTwoSuc)),
						Leg(
							sum(sum(newPlaceX, newPlaceY), sum(oldPartX, oldPartY)),
							"gather the two new places apart from the two old parts",
							regroup),
						Leg(
							sum(sum(meetPlace, joinPlace), sum(andWindow, orWindow)),
							"the new places trade for the meet's and the join's, the old parts for the two old windows",
							By(weighted, ih.At(x, y))),
						Leg(
							sum(sum(andWindow, meetPlace), sum(orWindow, joinPlace)),
							"hand each window back the place it gained",
							regroup),
						FinalLeg(
							"which is what widening each window by one place amounts to",
							By(openAnd, openOr)),
					))
				})
		}),
})}

// ---------------------------------------------------------------------------
// AddAndOr — the sum as meet plus join
// ---------------------------------------------------------------------------

// AddAndOr — the val-face form: adding two values is
// adding their meet to their join, at EVERY pair, with no width in
// sight. The twin's guards go because word_and and word_or are width-free:
// each is the window combinator at the window x + y, and that window
// already covers every bit either operand has.
//
// So the whole proof is windowAddSplit at that one window, once the
// two low parts are recognised as the operands themselves — which they
// are, because a value sits under its own power (LessThanPowTwoSelf) and
// that power sits under the window's (PowTwoMonotone over x ≤ x + y),
// so reducing at the window's weight changes nothing.
var AddAndOr = addAndOrThm{family.Add(registry.ProofEntry{
	Name: "AddAndOr",
	Key:  "prop_de6ec3dcbbca701c",
	Build: family.Theorem(
		"∀x y:num. x + y = word_and(x, y) + word_or(x, y)",
		func(a *Argument, x, y Term) {
			window := a.Term("x + y")
			weight := a.Term("nat_pow(2, x + y)")

			// ↦ x + y = word_bitwise_binary(x + y, ⟨∧⟩, x, y) + word_bitwise_binary(x + y, ⟨∨⟩, x, y)
			a.Do(Unfold(machine_word.WordAndDef), Unfold(machine_word.WordOrDef))

			xCover := a.Have(
				"the operators' shared window covers x — a value sits under its own power, and x ≤ x + y",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans, x, a.Term("nat_pow(2, x)"), weight)))
			yCover := a.Have(
				"and y likewise, its bound reached round the other side of the sum",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAdd, y, x),
					At(nat_arith.AddSym, y, x),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans, y, a.Term("nat_pow(2, y)"), weight)))
			a.Show(
				"what x and y keep inside the window is all of them, so the window "+
					"identity, read at x + y, is the statement about the operands themselves",
				// Bare: the identity applies whole at the window the two
				// unfolded doors already stand on.
				By(
					xCover,
					At(nat_div_mod.ModLessThan, x, weight),
					yCover,
					At(nat_div_mod.ModLessThan, y, weight),
					windowAddSplit))
		}),
})}

// ---------------------------------------------------------------------------
// OrAndXor — the join as meet plus difference
// ---------------------------------------------------------------------------

// OrAndXor — the val-face form: as plain values, the
// meet plus the difference is the join, at every pair and width-free.
// Place by place the join's digit splits as the meet's digit plus the
// exactly-one digit, and those two never collide, so the weighted
// places add with nothing to carry — which is windowOrSplit, and all
// three doors open onto the one window x + y where it applies whole.
var OrAndXor = orAndXorThm{family.Add(registry.ProofEntry{
	Name: "OrAndXor",
	Key:  "prop_1f3a58aff2781293",
	Build: family.Theorem(
		"∀x y:num. word_and(x, y) + word_xor(x, y) = word_or(x, y)",
		func(a *Argument, x, y Term) {
			a.Show(
				"the three doors open onto one window, where the window-sum identity is the goal itself",
				Unfold(machine_word.WordAndDef),
				Unfold(machine_word.WordXorDef),
				Unfold(machine_word.WordOrDef),
				// The identity applies whole — subsumption, no search.
				Cite(windowOrSplit))
		}),
})}

// ---------------------------------------------------------------------------
// AddAndXor — the carry, named
// ---------------------------------------------------------------------------

// AddAndXor — the val-face form: adding two values
// is adding their difference to TWICE their meet. It is the two laws
// above composed. The sum is the meet plus the join; the join is the
// meet plus the difference; so the meet is counted once inside the
// join and once beside it, and that doubled term is exactly the carry
// — the positions where both operands are set, each contributing to
// the next place up.
var AddAndXor = addAndXorThm{family.Add(registry.ProofEntry{
	Name: "AddAndXor",
	Key:  "prop_3e145b2726617aff",
	Build: family.Theorem(
		"∀x y:num. x + y = 2 * word_and(x, y) + word_xor(x, y)",
		func(a *Argument, x, y Term) {
			one := a.Ctx().Numeral(1)
			two := a.Ctx().Numeral(2)
			meet := a.Term("word_and(x, y)")
			difference := a.Term("word_xor(x, y)")

			sumSplit := a.Have(
				"the sum is the meet plus the join",
				"x + y = word_and(x, y) + word_or(x, y)",
				By(AddAndOr))
			joinSplit := a.Have(
				"and the join is the meet plus the difference",
				"word_and(x, y) + word_xor(x, y) = word_or(x, y)",
				By(OrAndXor))
			doubled := a.Have(
				"counting the meet twice is doubling it — two is suc(1), and a successor factor unfolds to the sum",
				"2 * word_and(x, y) = word_and(x, y) + word_and(x, y)",
				// The doubled factor is an opaque word, not a power of
				// two, so nat_arith.PowTwoSuc does not apply — the same
				// numeral chain runs inline at this factor. Nothing
				// rewrites `2` inside a product, so the closer refutes
				// rather than simplifies.
				By(
					nat_arith.Two,                   // 2 = suc(1)
					At(nat_arith.MulSym, two, meet), // 2·word_and = word_and·2
					At(nat_arith.MulSuc, meet, one), // word_and·suc(1) = word_and + word_and·1
					At(nat_arith.MulOne, meet)))     // word_and·1 = word_and
			a.Show(
				"so the meet is counted once inside the join and once "+
					"beside it, and the two copies regroup as the carry",
				By(
					Normalized,
					sumSplit,
					joinSplit,
					doubled,
					// word_and + (word_and + word_xor) = (word_and + word_and) + word_xor
					At(nat_arith.AddAssoc, meet, meet, difference)))
		}),
})}

// --------------------------------------------------------------------------
// No carry: when the meet is empty
// --------------------------------------------------------------------------
//
// The identities above hold at every pair. Spent on the pairs whose meet
// is empty_set — where position by position at most one operand is set, so
// nothing carries anywhere — they say that the three ways of combining
// two words coincide: the join loses nothing that adding keeps, and so
// does the difference. At a WIDTH that needs one thing more, since a
// width-n sum answers with a residue: the combination has to be a
// reduced word already, which it is, because its bits are the operands'
// and the range guards hold those below the width. Read the other way
// round, the same identity is a characterization — the meet is exactly
// the amount by which a plain sum overshoots the join, so the two agree
// precisely when the meet is empty (AddIsOrIff), and that reverse half
// is the one argument here that does real division: the overshoot is
// whole copies of the width, and a value below the width that is whole
// copies of it is nothing.
//
// The bound is what the width laws share, and coveredBitsBound is it: a
// value whose set bits all belong to two reduced words is itself
// reduced. AddAsAndOr needs none of it — the redistribution survives
// the width with no guard at all, both sides reducing one number.

// ---------------------------------------------------------------------------
// coveredBitsBound — bits borrowed from reduced words stay in range
// ---------------------------------------------------------------------------

// coveredBitsBound — a value whose set bits all belong to two reduced
// words is itself a reduced word. A bitwise combination of x and y
// still fits under 2ⁿ when every set bit is borrowed from an operand.
//
// The bound is ClearBitsBound's, reached in two moves. A set bit of an
// operand sits below the width, because the range guard covers it
// (BitBelowBound); so no bit of z survives at or past the width, every
// bit of z being a bit of an operand. And ClearBitsBound turns clear
// high bits into the bound — it needs SOME bound to start from, and
// every value carries one of its own (LessThanPowTwoSelf).
var coveredBitsBound = coveredBitsBoundThm{family.Add(registry.ProofEntry{
	Name: "coveredBitsBound",
	Key:  "prop_c10a0a0835c2361a",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y z:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
				"∀i:num. word_bit(i, z) ⇒ word_bit(i, x) ∨ word_bit(i, y)",
			},
			Conclusion: "z < nat_pow(2, n)",
		},
		func(a *Argument, n, x, y, z Term, xBound, yBound, covered Fact) {
			clearHigh := a.Have(
				"z has no bit at or past the width — its bits are the operands', which the range guards keep below",
				"∀i:num. ¬(n ≤ i) ∨ ¬word_bit(i, z)",
				Derive(func(b *Argument) {
					i := b.Fix()
					guardX := b.Have(
						"a set bit of x sits below the width, through the range guard",
						"word_bit(i, x) ⇒ i < n",
						By(xBound, word_bits.BitBelowBound))
					guardY := b.Have(
						"and of y",
						"word_bit(i, y) ⇒ i < n",
						By(yBound, word_bits.BitBelowBound))
					b.Show(
						"so a bit of z at position i puts i below the width, whichever operand lends it",
						By(covered.At(i), guardX, guardY, At(nat_order.NotLessThan, i, n))) // ¬(i < n) ⇔ n ≤ i
				}))
			a.Show(
				"and clear high bits ARE the bound, once any bound is in hand — a value sits under its own power",
				By(
					clearHigh,
					nat_order.LessThanPowTwoSelf,
					// ClearBitsBound reads (seed window, value, width): z sits
					// under 2^z, and that is the seed the induction wants.
					At(word_bits.ClearBitsBound, z, z, n)))
		}),
})}

// ---------------------------------------------------------------------------
// OrDisjoint — with the meet empty, the join IS the sum
// ---------------------------------------------------------------------------

// OrDisjoint — the val-face form: two words whose
// meet is zero set no position in common, so joining them keeps
// everything adding them keeps. It is AddAndOr with the meet gone —
// the sum splits into meet plus join, and here the first summand
// contributes nothing.
var OrDisjoint = orDisjointThm{family.Add(registry.ProofEntry{
	Name: "OrDisjoint",
	Key:  "prop_756862ea7e5b1ee0",
	Build: family.Theorem(
		Statement{
			Binders: "∀x y:num.",
			Hypotheses: []string{
				"word_and(x, y) = 0",
			},
			Conclusion: "word_or(x, y) = x + y",
		},
		func(a *Argument, x, y Term, disjoint Fact) {
			a.Show(
				"the split of the sum reads 0 + word_or, and adding nothing on the left changes nothing",
				// AddLeftZeroClause is cited bare: it closes the residue at
				// its ∀-form install, so it names no instance.
				By(disjoint, At(AddAndOr, x, y), nat_arith.AddLeftZeroClause))
		}),
})}

// ---------------------------------------------------------------------------
// AddAsAndOr — the redistribution survives the width
// ---------------------------------------------------------------------------

// AddAsAndOr — the val-face form: at any width, adding a
// pair is adding their meet to their join. No guard and no range
// assumption on either operand, because the two sides reduce ONE
// number at ONE modulus: AddAndOr identifies the pair's sum with the
// meet-join pair's sum before any reduction happens.
var AddAsAndOr = addAsAndOrThm{family.Add(registry.ProofEntry{
	Name: "AddAsAndOr",
	Key:  "prop_7c929893e9c9a620",
	Build: family.Theorem(
		"∀n x y:num. word_add(n, x, y) = word_add(n, word_and(x, y), word_or(x, y))",
		func(a *Argument, n, x, y Term) {
			// ↦ nat_mod(x + y, nat_pow(2, n)) = nat_mod(word_and(x, y) + word_or(x, y), nat_pow(2, n))
			a.Do(Unfold(machine_word.WordAddDef))

			a.Show(
				"so the goal is a congruence under nat_mod over one equation",
				By(AddAndOr))
		}),
})}

// ---------------------------------------------------------------------------
// AddIsOr · AddIsXor — a disjoint sum needs no reduction
// ---------------------------------------------------------------------------

// AddIsOr — the val-face form: for reduced words whose meet
// is empty, the width-n sum IS the join. The positive-width guard
// 1 ≤ n goes; the two range guards stay, and they are exactly what the
// argument spends.
//
// Two steps. With the meet empty the join is the plain sum
// (OrDisjoint), so the width-n sum is that join reduced. And the
// reduction fixes it: the join borrows its bits from x and y, which
// the range guards hold below the width, so the join is a reduced word
// and its own residue.
var AddIsOr = addIsOrThm{family.Add(registry.ProofEntry{
	Name: "AddIsOr",
	Key:  "prop_a91ee8cbd6bc6074",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
				"0 = word_and(x, y)",
			},
			Conclusion: "word_add(n, x, y) = word_or(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound, disjoint Fact) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			join := a.Term("word_or(x, y)")
			width := a.Term("nat_pow(2, n)")

			covered := a.Have(
				"every bit the join sets is a bit of an operand",
				"∀i:num. word_bit(i, word_or(x, y)) ⇒ word_bit(i, x) ∨ word_bit(i, y)",
				// Bare: the join's bit reading is this claim with an iff
				// where the claim has an implication, so it closes at its
				// ∀-form install and names no instance.
				By(word_bits.BitOfOr))
			bound := a.Have(
				"so the join is a reduced word itself",
				"word_or(x, y) < nat_pow(2, n)",
				By(xBound, yBound, covered, At(coveredBitsBound, n, x, y, join)))
			sum := a.Have(
				"and with the meet empty it is the plain sum",
				"word_or(x, y) = x + y",
				By(disjoint, At(OrDisjoint, x, y)))
			a.Show(
				"the width-n sum is that sum reduced, and reduction fixes what already sits below the width",
				By(wordAddDef, sum, bound, At(nat_div_mod.ModLessThan, join, width)))
		}),
})}

// AddIsXor — the val-face form: the same sum read as the
// difference. Nothing further about the width is needed, because here
// the join and the difference are one word — the join is the meet plus
// the difference (OrAndXor), and the meet is empty. So this is AddIsOr
// with its answer renamed.
var AddIsXor = addIsXorThm{family.Add(registry.ProofEntry{
	Name: "AddIsXor",
	Key:  "prop_3332f5cb48356892",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
				"0 = word_and(x, y)",
			},
			Conclusion: "word_add(n, x, y) = word_xor(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound, disjoint Fact) {
			difference := a.Have(
				"the meet is all that separates the difference from the join, and it is empty",
				"word_xor(x, y) = word_or(x, y)",
				By(disjoint, At(OrAndXor, x, y), nat_arith.AddLeftZeroClause))
			a.Show(
				"and the width-n sum is the join",
				// Normalized: AddIsOr arrives as a clause with its three
				// guards negated and all three are resident, so the leaf
				// settles by simplification.
				By(Normalized, xBound, yBound, disjoint, difference, At(AddIsOr, n, x, y)))
		}),
})}

// ---------------------------------------------------------------------------
// AddIsOrIff — an empty meet is exactly what makes the two agree
// ---------------------------------------------------------------------------

// AddIsOrIff — the val-face form: for reduced words the
// width-n sum equals the join PRECISELY when the meet is empty. The
// meet is the amount by which the plain sum overshoots the join, so
// the two agree exactly when there is no overshoot.
//
// The forward half is AddIsOr. The reverse half is the one argument in
// this file that divides. Agreement says the join is what the plain sum
// leaves below the width, so the plain sum is the join plus whole
// copies of the width; it is also the join plus the meet (AddAndOr);
// cancel the join and the meet IS those whole copies. Whole copies of
// the width leave nothing below it, while the meet — its bits borrowed
// from x and y — sits below it and is therefore its own residue.
// Nothing is what is left.
var AddIsOrIff = addIsOrIffThm{family.Add(registry.ProofEntry{
	Name: "AddIsOrIff",
	Key:  "prop_121caf77856cd73d",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "0 = word_and(x, y) ⇔ word_add(n, x, y) = word_or(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			a.Iff()
			a.Forward(
				"the meet is empty: then nothing carries and the sum is the join",
				func(b *Argument, disjoint Fact) {
					b.Show(
						"which is AddIsOr at this width and this pair",
						By(xBound, yBound, disjoint, At(AddIsOr, n, x, y)))
				})
			a.Backward(
				"the two agree: what the plain sum overshoots the join by is whole widths, and it is also the meet",
				func(b *Argument, agree Fact) {
					wordAddDef := b.Ctx().ConstDefNormalized("word_add")
					zero := b.Ctx().Numeral(0)
					meet := b.Term("word_and(x, y)")
					join := b.Term("word_or(x, y)")
					plain := b.Term("x + y")
					width := b.Term("nat_pow(2, n)")
					// how many whole widths the plain sum runs over
					copies := b.Term("div(x + y, nat_pow(2, n))")
					blocks := b.Term("div(x + y, nat_pow(2, n)) * nat_pow(2, n)") // what those widths amount to

					covered := b.Have(
						"every bit the meet sets is a bit of an operand",
						"∀i:num. word_bit(i, word_and(x, y)) ⇒ word_bit(i, x) ∨ word_bit(i, y)",
						Derive(func(c *Argument) {
							i := c.Fix()
							c.Show(
								"at each position the meet asks for BOTH operands, which is more than either",
								By(At(word_bits.BitOfAnd, x, y, i)))
						}))
					bound := b.Have(
						"so the meet is a reduced word itself",
						"word_and(x, y) < nat_pow(2, n)",
						By(xBound, yBound, covered, At(coveredBitsBound, n, x, y, meet)))
					residue := b.Have(
						"the agreement says the join is what the plain sum leaves below the width",
						"rem(x + y, nat_pow(2, n)) = word_or(x, y)",
						By(agree, wordAddDef))
					overshoot := b.Have(
						"so the plain sum is the join plus whole widths — and it is the join plus the meet",
						"word_and(x, y) + word_or(x, y) = div(x + y, nat_pow(2, n)) * nat_pow(2, n) + word_or(x, y)",
						// AddAndOr is cited bare: it closes its half of the
						// leaf at its ∀-form install and names no instance.
						By(At(nat_arith.PowTwoNonzero, n), residue, At(nat_div_mod.Division, plain, width), AddAndOr))
					whole := b.Have(
						"cancel the join and the meet IS those whole widths",
						"word_and(x, y) = div(x + y, nat_pow(2, n)) * nat_pow(2, n)",
						By(
							overshoot,
							At(nat_arith.AddSym, meet, join),   // word_and + word_or = word_or + word_and
							At(nat_arith.AddSym, blocks, join), // blocks + word_or = word_or + blocks
							At(nat_arith.AddEqLCancel, join, meet, blocks)))
					divisible := b.Have(
						"and whole widths leave nothing below the width",
						"rem(word_and(x, y), nat_pow(2, n)) = 0",
						// ModEq reads (value, representative, modulus,
						// multiplier): the meet is 0 plus that many widths.
						By(
							whole,
							At(nat_div_mod.ModEq, meet, zero, width, copies),
							nat_arith.AddLeftZeroClause,
							nat_div_mod.ZeroMod))
					b.Show(
						"while the meet, sitting below the width, is its own residue — so it is nothing",
						By(bound, divisible, At(nat_div_mod.ModLessThan, meet, width)))
				})
		}),
})}

// --------------------------------------------------------------------------
// Order: the meet below, the join above
// --------------------------------------------------------------------------
//
// One fact carries this part: including one word's bits in
// another's cannot decrease the value. Reading a value as its binary
// digits, turning a bit ON can only add a place value and never take
// one away, so a word whose set bits are a subset of another's is the
// smaller number. The meet turns bits off and the join turns bits on,
// which is why the operator laws below are that one fact read at the
// bit laws of the reading face, and why they need no arithmetic of
// their own.
//
// The fact is proved over a WINDOW and then read width-free.
// windowMonotone is the induction: over the low k places, an inclusion
// of bits is an order of residues, because widening by one place adds
// each side's digit at the same weight (modPowTwoSuc, part 1)
// and + is monotone in both summands. bitsSubsetLessEq is that
// induction at the one window x + y, which holds both values whole — a
// value sits under its own power and powers grow with the exponent —
// so both residues are the values themselves and the window drops out.
//
// LessEqBits is the same induction read backwards. Two values inside a
// common width that are NOT in order must fail the inclusion somewhere
// below that width, and the position where they fail is a place the
// smaller-looking value has and the other does not — the row's witness.
//
// The range guards survive only where a position is genuinely measured
// against the width, which here is LessEqBits alone. The four operator laws are width-free because
// word_and and word_or are: each is the window combinator at the window x + y,
// which already covers every bit either operand has.

// ---------------------------------------------------------------------------
// windowMonotone — the window induction
// ---------------------------------------------------------------------------

// windowMonotone — over any window, an inclusion of bits is an order of
// residues. The keystone: every order law below is this read at one
// window or another.
//
// By induction on the window. An empty window keeps nothing of either
// value, so both residues are 0. Widening by one place puts, on each
// side, that side's digit at the weight 2ᵏ on top of what the old
// window kept (modPowTwoSuc). The two new digits are ordered because
// the inclusion, now reaching k, says a bit x has y has too — and a
// clear bit contributes nothing while no digit ever exceeds the one a
// set bit contributes. The two old parts are ordered by the hypothesis,
// whose own antecedent is the widened inclusion read below k. Then +
// composes the two bounds, one summand each (nat_order.LessEqAdd2).
var windowMonotone = windowMonotoneThm{family.Add(registry.ProofEntry{
	Name: "windowMonotone",
	Key:  "prop_224a238cdcdbf4c7",
	Build: family.Theorem(
		Statement{
			Binders: "∀k x y:num.",
			Hypotheses: []string{
				"∀i:num. i < k ⇒ (word_bit(i, x) ⇒ word_bit(i, y))",
			},
			Conclusion: "rem(x, nat_pow(2, k)) ≤ rem(y, nat_pow(2, k))",
		},
		func(a *Argument) {
			k := a.Binder("k")

			a.Induct(k)
			a.Base(
				"the empty window keeps nothing of either value — below 2⁰ = 1 both residues are 0",
				func(b *Argument) {
					b.Fix() // x — spelled in the claims below
					b.Fix() // y
					two := b.Ctx().Numeral(2)
					zero := b.Ctx().Numeral(0)
					// ModOne is cited bare: once the weight is known to be
					// one it rewrites both residues at its ∀-form install,
					// so no single instance is the premise.
					b.Show(
						"nothing of x or y survives below the empty window's "+
							"weight, which is one, and nothing is at most nothing",
						By(At(nat_arith.NatPow, two, zero), nat_div_mod.ModOne, nat_order.LessEqRefl))
				})
			a.Step(
				"the new places are ordered by the inclusion at k, the "+
					"old parts by the hypothesis, and + composes the two",
				func(b *Argument, ih Fact) {
					x := b.Fix()
					y := b.Fix()
					// covers: ∀i. i < suc(k) ⇒ (word_bit(i, x) ⇒ word_bit(i, y))
					covers := b.Assume()

					weight := b.Term("nat_pow(2, k)")                                // the new place's value
					xBit := b.Term("word_bit(k, x)")                                 // x's bit there
					yBit := b.Term("word_bit(k, y)")                                 // y's
					xDigit := b.Term("bit_value(word_bit(k, x))")                    // x's digit there
					yDigit := b.Term("bit_value(word_bit(k, y))")                    // y's
					newPlaceX := b.Term("nat_pow(2, k) * bit_value(word_bit(k, x))") // x's digit, weighted
					newPlaceY := b.Term("nat_pow(2, k) * bit_value(word_bit(k, y))") // y's
					oldPartX := b.Term("rem(x, nat_pow(2, k))")                      // what x kept below the old window
					oldPartY := b.Term("rem(y, nat_pow(2, k))")                      // what y kept

					low := b.Have(
						"the old parts are ordered by the hypothesis, whose "+
							"antecedent is the widened inclusion read below k",
						"rem(x, nat_pow(2, k)) ≤ rem(y, nat_pow(2, k))",
						By(ih.At(x, y), covers, nat_order.LessThanSucIffLessEq, nat_order.LessEqOfLessThan))
					newBit := b.Have(
						"the widened window reaches the new place, so a bit x has there y has too",
						"word_bit(k, x) ⇒ word_bit(k, y)",
						By(
							covers.At(k),
							At(nat_order.LessThanSucIffLessEq, k, k), // k < suc(k) ⇔ k ≤ k
							// Bare: reflexivity closes the residual at its
							// ∀-form install, so it names no instance.
							nat_order.LessEqRefl))
					digit := b.Have(
						"so x's digit there is at most y's — a clear bit contributes "+
							"nothing, and no digit exceeds the one a set bit contributes",
						"bit_value(word_bit(k, x)) ≤ bit_value(word_bit(k, y))",
						By(
							Normalized,
							newBit,
							At(word_bits.BitValueEqZero, xBit), // bit_value(word_bit(k, x)) = 0 ⇔ ¬word_bit(k, x)
							At(word_bits.BitValueBound, xBit),  // bit_value(word_bit(k, x)) ≤ 1
							At(word_bits.BitValueEqOne, yBit),  // bit_value(word_bit(k, y)) = 1 ⇔ word_bit(k, y)
							nat_order.ZeroLessEq))
					place := b.Have(
						"and the common weight scales that bound into a bound on the new places themselves",
						"nat_pow(2, k) * bit_value(word_bit(k, x)) ≤ nat_pow(2, k) * bit_value(word_bit(k, y))",
						By(digit, At(nat_order.LessEqMulMono, weight, xDigit, yDigit)))

					b.Show(
						"each widened residue is its new place on top of its old part, and both summands are bounded",
						By(
							place,
							low,
							At(modPowTwoSuc, k, x), // nat_mod(x, 2^suc k) = 2^k·bit_value(word_bit(k, x)) + nat_mod(x, 2^k)
							At(modPowTwoSuc, k, y),
							At(nat_order.LessEqAdd2,
								newPlaceX, oldPartX, newPlaceY, oldPartY)))
				})
		}),
})}

// ---------------------------------------------------------------------------
// bitsSubsetLessEq — the window dissolved
// ---------------------------------------------------------------------------

// bitsSubsetLessEq — including one value's bits in another's cannot
// decrease the value, no bound asked: the exit every order law below
// takes back to a comparison of values. It is windowMonotone read at
// the one window x + y, which is of the two values' own making — each
// sits under its own power (LessThanPowTwoSelf) and that power only grows to
// the wider exponent (PowTwoMonotone over x ≤ x + y) — so at that
// window each residue is the value itself and the window drops out.
//
// The unbounded-order sibling of the reading face's BitsEqAll
// (`words/word_bits`), which dissolves the same window for bit
// extensionality.
var bitsSubsetLessEq = bitsSubsetLessEqThm{family.Add(registry.ProofEntry{
	Name: "bitsSubsetLessEq",
	Key:  "prop_6cbc76ae7509d91c",
	Build: family.Theorem(Statement{
		Binders: "∀x y:num.",
		Hypotheses: []string{
			"∀i:num. word_bit(i, x) ⇒ word_bit(i, y)",
		},
		Conclusion: "x ≤ y",
	},
		func(a *Argument, x, y Term, included Fact) {
			window := a.Term("x + y")
			weight := a.Term("nat_pow(2, x + y)")

			xCover := a.Have(
				"the window covers x — a value sits under its own power, which only grows to the wider exponent",
				"x < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, x),
					At(nat_order.LessEqAdd, x, y),
					At(nat_order.PowTwoMonotone, x, window),
					At(nat_order.LessThanLessEqTrans, x, a.Term("nat_pow(2, x)"), weight)))
			yCover := a.Have(
				"and y likewise, its bound reached round the other side of the sum",
				"y < nat_pow(2, x + y)",
				By(
					At(nat_order.LessThanPowTwoSelf, y),
					At(nat_order.LessEqAdd, y, x),
					At(nat_arith.AddSym, y, x),
					At(nat_order.PowTwoMonotone, y, window),
					At(nat_order.LessThanLessEqTrans, y, a.Term("nat_pow(2, y)"), weight)))
			a.Show(
				"so at that window each residue is the value itself, "+
					"and the window comparison is the comparison of values",
				By(
					Normalized,
					included,
					xCover,
					yCover,
					At(windowMonotone, window, x, y),
					At(nat_div_mod.ModLessThan, x, weight),
					At(nat_div_mod.ModLessThan, y, weight)))
		}),
})}

// ---------------------------------------------------------------------------
// AndLessEq · OrLessEq — the meet below, the join above
// ---------------------------------------------------------------------------

// AndLessEq — the val-face form: meeting two values
// cannot get you above either of them, at every pair and width-free.
// Meeting turns bits off and never on, so the meet's bits are included
// in each operand's — and inclusion of bits is order of values.
//
// The inclusion is the projection read at the meet's own window: a bit
// of the meet is the conjunction of the operands' bits there, and a
// conjunction gives back each conjunct. The window conjunct the
// projection also reports is not needed in this direction, which is
// what makes these two claims one cite each.
var AndLessEq = andLessEqThm{family.Add(registry.ProofEntry{
	Name: "AndLessEq",
	Key:  "prop_a0e563c3591c4eb4",
	Build: family.Theorem("∀x y:num. word_and(x, y) ≤ x ∧ word_and(x, y) ≤ y",
		func(a *Argument, x, y Term) {
			meet := a.Term("word_and(x, y)")

			inX := a.Have(
				"every bit of the meet is a bit of x — through the door, the "+
					"projection reads it as the conjunction of the operands' bits",
				"∀i:num. word_bit(i, word_and(x, y)) ⇒ word_bit(i, x)",
				By(machine_word.WordAndDef, word_bits.BitwiseBinaryProjection))
			inY := a.Have(
				"and a bit of y, the other conjunct",
				"∀i:num. word_bit(i, word_and(x, y)) ⇒ word_bit(i, y)",
				By(machine_word.WordAndDef, word_bits.BitwiseBinaryProjection))
			a.Show(
				"so the meet's bits are included in each operand's, and inclusion of bits is order of values",
				By(inX, inY, At(bitsSubsetLessEq, meet, x), At(bitsSubsetLessEq, meet, y)))
		}),
})}

// OrLessEq — a join is at least as large as each operand.
// BitOfOr includes each operand's set bits in the join, and bit
// inclusion gives the corresponding order of values.
var OrLessEq = orLessEqThm{family.Add(registry.ProofEntry{
	Name: "OrLessEq",
	Key:  "prop_2533ba80038bfc3e",
	Build: family.Theorem("∀x y:num. x ≤ word_or(x, y) ∧ y ≤ word_or(x, y)",
		func(a *Argument, x, y *Expr[Nat]) {
			join := a.TermAs[Nat]("word_or(x, y)")
			inX := a.Have(
				"every bit of x belongs to the join",
				"∀i:num. word_bit(i, x) ⇒ word_bit(i, word_or(x, y))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					set := b.Assume()
					b.Show(
						"x supplies one of the join's alternatives",
						By(set, word_bits.BitOfOr.At(x, y, i)))
				}))
			inY := a.Have(
				"every bit of y belongs to the join",
				"∀i:num. word_bit(i, y) ⇒ word_bit(i, word_or(x, y))",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					set := b.Assume()
					b.Show(
						"y supplies one of the join's alternatives",
						By(set, word_bits.BitOfOr.At(x, y, i)))
				}))
			a.Show(
				"inclusion of bits gives the two value bounds",
				By(inX, inY, bitsSubsetLessEq.At(x, join), bitsSubsetLessEq.At(y, join)))
		}),
})}

// ---------------------------------------------------------------------------
// AndLessEqMin · OrLessEqMax — the sharper bound, named
// ---------------------------------------------------------------------------

// AndLessEqMin — the val-face form: the meet sits
// below the SMALLER operand. AndLessEq read at the definition of the
// bound it names — nat_min is a conditional on x ≤ y, so whichever branch
// the test picks, the bound is one of the two AndLessEq already gives.
var AndLessEqMin = andLessEqMinThm{family.Add(registry.ProofEntry{
	Name: "AndLessEqMin",
	Key:  "prop_9e1213005f0d335a",
	Build: family.Theorem("∀x y:num. word_and(x, y) ≤ min(x, y)",
		func(a *Argument, x, y Term) {
			// ↦ word_and(x, y) ≤ COND(x ≤ y, x, y)
			a.Do(Unfold(nat_order.NatMinDef))
			a.Show(
				"either branch of the test is an operand, and the meet sits below both",
				By(At(AndLessEq, x, y)))
		}),
})}

// OrLessEqMax — the val-face form: the join sits above
// the LARGER operand. AndLessEqMin's mirror, on the same conditional.
var OrLessEqMax = orLessEqMaxThm{family.Add(registry.ProofEntry{
	Name: "OrLessEqMax",
	Key:  "prop_e9ae953e70f2229e",
	Build: family.Theorem("∀x y:num. max(x, y) ≤ word_or(x, y)",
		func(a *Argument, x, y Term) {
			// ↦ COND(x ≤ y, y, x) ≤ word_or(x, y)
			a.Do(Unfold(nat_order.NatMaxDef))
			a.Show(
				"either branch of the test is an operand, and the join sits above both",
				By(At(OrLessEq, x, y)))
		}),
})}

// ---------------------------------------------------------------------------
// LessEqBits — where two values out of order must differ
// ---------------------------------------------------------------------------

// LessEqBits — the val-face form: of two values inside a
// common width, either they are in order or there is a position below
// the width that the first has set and the second has clear.
//
// windowMonotone read backwards, at the stated width. Inside that width
// each residue is its own value (nat_div_mod.ModLessThan under the range
// guards), so the induction says outright that an inclusion of the bits
// below n would put x below y. If x is NOT below y, the inclusion
// therefore fails somewhere below n — and a position where it fails is
// exactly a position x has and y has not, the witness the row asks for.
//
// The ∃ sits OUTSIDE the disjunction, as the row states it: in the
// settled branch nothing is being witnessed and any position serves.
var LessEqBits = lessEqBitsThm{family.Add(registry.ProofEntry{
	Name: "LessEqBits",
	Key:  "prop_2e6173c186470dba",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "∃i:num. x ≤ y ∨ (¬word_bit(i, y) ∧ i < n ∧ word_bit(i, x))",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			weight := a.Term("nat_pow(2, n)")

			notLe := a.Unless(
				a.Term("x ≤ y"),
				"x ≤ y: the left disjunct is the assumption itself, "+
					"and nothing is being witnessed, so position 0 serves",
				Given(func(b *Argument, le Fact) {
					b.Take(b.Ctx().Numeral(0))
					b.Show(
						"the left disjunct holds outright",
						By(le))
				}))

			a.Show(
				"otherwise the inclusion below n must fail, and a "+
					"position where it fails is one x has and y has not",
				By(
					notLe,
					xBound,
					yBound,
					At(windowMonotone, n, x, y),
					At(nat_div_mod.ModLessThan, x, weight), // nat_mod(x, 2ⁿ) = x
					At(nat_div_mod.ModLessThan, y, weight)))
		}),
})}

// --------------------------------------------------------------------------
// Complement: word_not(n, x) as 2ⁿ - 1 - x
// --------------------------------------------------------------------------
//
// word_not is the chapter's one bitwise operator that takes a width, and
// the reason is that complementing IS a fact about a window. word_and,
// word_or and word_xor read the operands' own bits and so need no window at
// all; the bits word_not SETS are the ones x leaves clear BELOW
// n, so naming a different n names a different word. Every law here
// carries the width, and the ones that measure x against it carry the
// range guard too.
//
// The file turns that window fact into arithmetic, and the route
// spends no induction on x. A word and its complement have no bit in
// common, so their meet is zero; between them they hold every
// position below n, so their join is the all-ones mask word_not(n, 0).
// Those two are bit extensionality over the projections, one position
// at a time, and they are the same technique twice. AddAndOr
// (part 1) — the sum IS the meet plus the join, at every pair and
// width-free — then reads both off at once, and what is left is one
// cancellation in ℕ.
//
// The mask's own value is this part's one induction, and it runs
// additively: one more than all-ones is the modulus, place by place
// (maskPlusOne), which is 2ⁿ - 1 read the other way round (AllOnes).
// Stating it as a sum rather than a difference keeps monus out of the
// induction invariant entirely, and every cancellation the file goes
// on to perform is a single step against a sum already in hand — the
// standing hazard in ℕ is a subtraction with no such sum behind it.
//
// word_neg(n, 1) reaches the same value by pure modular arithmetic, with
// no bit argument anywhere, and the two meet in NegOneIsNotZero.
//
// The part closes by putting the complement back in the ring, where
// the sub-and-negate laws are one sentence said several ways:
// complementing is negating and stepping back one place. What those
// laws consume is not ValNot but the partition ValNot is itself a
// cancellation of — the two facts are the same fact, and the additive
// one is the one that keeps monus out.

// WindowOpNot — the operation word_not instantiates the unary window
// combinator at `machine_word.WordNotDef`. Named for the same reason its
// binary siblings in the reading face are: grounding a cite at the
// combinator needs the operation as a term.

// ---------------------------------------------------------------------------
// The all-ones mask's value
// ---------------------------------------------------------------------------

// maskPlusOne — the mask counted one place further is the modulus, by
// induction on the width. An empty window holds nothing and the empty
// modulus is one. Widening by one place: zero has no bit at the new
// position, so the complement takes it, and the place it takes weighs
// exactly what the modulus must double by (nat_arith.PowTwoSuc). The hypothesis
// fills the old span; the new place doubles it.
//
// Stated as a sum on purpose — the induction then never meets a
// monus, and the difference form below is one cancellation away.
var maskPlusOne = maskPlusOneThm{family.Add(registry.ProofEntry{
	Name: "maskPlusOne",
	Key:  "prop_1d4ced7c3a2f2d1a",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "word_not(n, 0) + 1 = nat_pow(2, n)",
	},
		func(a *Argument) {
			wordNotDef := a.Ctx().ConstDefNormalized("word_not")
			notOp := a.Term("«WindowOpNot»")
			zero := a.Ctx().Numeral(0)
			two := a.Ctx().Numeral(2)
			n := a.Binder("n")

			a.Induct(n)
			a.Base(
				"the empty window holds no place, and the empty modulus is one",
				func(b *Argument) {
					empty := b.Have(
						"an empty window holds nothing to complement",
						"word_not(0, 0) = 0",
						// Ground, and Normalized: at this one window and
						// operation the zero clause folds the goal where it
						// stands, so the leaf wants simplification and no
						// refutation at all.
						By(Normalized, wordNotDef, At(machine_word.WordBitwiseUnaryDef, zero, zero, notOp)))
					b.Show(
						"and one more than nothing is 2⁰",
						By(
							empty,
							At(nat_arith.NatPow, two, zero), // 1 = nat_pow(2, 0)
							nat_arith.AddLeftZeroClause))
				})
			a.Step(
				"zero leaves the new position clear, so the complement "+
					"takes it — and that place is what doubles the modulus",
				func(b *Argument, ih Fact) {
					digit := b.Have(
						"zero has no bit at n, so the complement's digit there is one",
						"bit_value(¬word_bit(n, 0)) = 1",
						By(word_bits.BitWordZero, word_bits.BitValueEqOne))
					open := b.Have(
						"so widening the window adds exactly the new place's weight",
						"word_not(suc(n), 0) = word_not(n, 0) + nat_pow(2, n)",
						// Ground, as the base's.
						By(digit, wordNotDef, At(machine_word.WordBitwiseUnaryDef, n, zero, notOp), nat_arith.MulOne))
					regroup := b.Have(
						"count the extra place apart from the span the hypothesis fills",
						"(word_not(n, 0) + nat_pow(2, n)) + 1 = (word_not(n, 0) + 1) + nat_pow(2, n)",
						ACRegroupWith(nat_arith.AddAC(b.Ctx())))
					b.Show(
						"the hypothesis makes that span the old modulus, "+
							"and the new place doubles it — the next modulus up",
						// Bare: the doubling fires on the goal as the
						// rewrite it is.
						By(open, regroup, ih, nat_arith.PowTwoSuc))
				})
		}),
})}

// AllOnes — the mask's value as a difference: maskPlusOne read the
// other way round. Adding one and taking it away again is
// AddSubCancel, at the mask.
var AllOnes = allOnesThm{family.Add(registry.ProofEntry{
	Name: "AllOnes",
	Key:  "prop_1699541b145dcbe",
	Build: family.Theorem("∀n:num. word_not(n, 0) = nat_pow(2, n) - 1",
		func(a *Argument, n Term) {
			mask := a.Term("word_not(n, 0)")
			one := a.Ctx().Numeral(1)

			a.Show(
				"the modulus is the mask plus one, and taking the one back off returns the mask",
				// Normalized: one equation rewrites into another, which is
				// simplification and not a refutation.
				By(Normalized, maskPlusOne, At(nat_monus.AddSubCancel, mask, one))) // (mask + 1) - 1 = mask
		}),
})}

// ---------------------------------------------------------------------------
// A word against its own complement
// ---------------------------------------------------------------------------

// meetWithComplement — a word and its complement share no bit, so
// their meet is the zero word. Bit extensionality over three tables:
// the complement holds the clear positions inside the width, the meet
// holds what both operands hold, and zero holds nothing — and no
// position is both set and clear. BitNot reads the complement inside
// its width, and BitOfAnd reads the meet without a width guard, so the
// law needs no bound on x.
var meetWithComplement = meetWithComplementThm{family.Add(registry.ProofEntry{
	Name: "meetWithComplement",
	Key:  "prop_bde05371b6cc0a1e",
	Build: family.Theorem("∀n x:num. word_and(x, word_not(n, x)) = 0",
		func(a *Argument, n, x Term) {
			zero := a.Ctx().Numeral(0)

			complementBits := a.Have(
				"the complement's bits are the positions x leaves clear inside the width",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ (¬word_bit(k, x) ∧ (k < n))",
				By(word_bits.BitNot))
			meetBits := a.Have(
				"the meet's bits are the positions both hold, width-free",
				"∀k:num. word_bit(k, word_and(x, word_not(n, x))) ⇔ (word_bit(k, x) ∧ word_bit(k, word_not(n, x)))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfAnd))
				}))
			zeroBits := a.Have(
				"and the zero word holds none",
				"∀k:num. ¬word_bit(k, 0)",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitWordZero))
				}))
			a.Show(
				"no position is both set and clear, so the meet's "+
					"table is empty — extensionality equates it to zero",
				// Grounded at the pair being equated. Bare, the cite installs
				// with v and w still universally quantified, and the leaf then
				// asks for a strictly larger refutation than this one.
				By(
					complementBits,
					meetBits,
					zeroBits,
					At(word_bits.BitsEqAll, a.Term("word_and(x, word_not(n, x))"), zero)))
		}),
})}

// joinWithComplement — a word and its complement between them hold
// every position below the width, so their join is the all-ones mask.
// The mirror of meetWithComplement, and here the range guard is
// load-bearing: reading the join's table back as the mask's needs a
// set bit of x to sit below n, which is BitBelowBound off the guard.
// The other direction is the excluded middle at each position — below
// the width, x either holds it or its complement does.
var joinWithComplement = joinWithComplementThm{family.Add(registry.ProofEntry{
	Name: "joinWithComplement",
	Key:  "prop_ffecd55059d2e4b6",
	Build: family.Theorem(Statement{
		Binders: "∀n x:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_or(x, word_not(n, x)) = word_not(n, 0)",
	},
		func(a *Argument, n, x Term, xBound Fact) {
			zero := a.Ctx().Numeral(0)

			complementBits := a.Have(
				"the complement's bits are the positions x leaves clear inside the width",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ (¬word_bit(k, x) ∧ (k < n))",
				By(word_bits.BitNot))
			maskBits := a.Have(
				"and the mask's are the width's positions outright — nothing is left clear in zero",
				"∀k:num. word_bit(k, word_not(n, 0)) ⇔ (k < n)",
				Derive(func(b *Argument) {
					k := b.Fix()
					b.Do(By(Normalized, At(word_bits.BitNot, n, zero, k), At(word_bits.BitWordZero, k)))
				}))
			guardX := a.Have(
				"a set bit of x sits below the width, which is what the guard buys",
				"∀k:num. word_bit(k, x) ⇒ (k < n)",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(xBound, word_bits.BitBelowBound))
				}))
			joinBits := a.Have(
				"the join's bits are the positions either holds, width-free",
				"∀k:num. word_bit(k, word_or(x, word_not(n, x))) ⇔ (word_bit(k, x) ∨ word_bit(k, word_not(n, x)))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfOr))
				}))
			a.Show(
				"below the width one of the two holds every position and "+
					"neither reaches past it — the join's table is the mask's",
				// Grounded at the pair being equated, as meetWithComplement's.
				By(
					complementBits,
					maskBits,
					guardX,
					joinBits,
					At(word_bits.BitsEqAll,
						a.Term("word_or(x, word_not(n, x))"), a.Term("word_not(n, 0)"))))
		}),
})}

// ---------------------------------------------------------------------------
// ValNot — the complement as arithmetic
// ---------------------------------------------------------------------------

// ValNot — the val-face form: on a reduced word the
// complement is what is left of the mask after x. The keystone the
// sub-and-negate laws are read off.
//
// AddAndOr says a sum is its operands' meet plus their join; at the
// pair (x, word_not(n, x)) the meet is empty and the join is the whole
// mask, so the sum IS the mask — a word and its complement partition
// the window's places between them. Cancelling x off that sum is the
// statement, and it is a genuine ℕ subtraction made legal by the sum
// itself: x is one summand of the mask, so the mask never falls short
// of it.
var ValNot = valNotThm{family.Add(registry.ProofEntry{
	Name: "ValNot",
	Key:  "prop_d67f8e81b187fe20",
	Build: family.Theorem(Statement{
		Binders: "∀n x:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_not(n, x) = nat_pow(2, n) - 1 - x",
	},
		func(a *Argument, n, x Term, xBound Fact) {
			complement := a.Term("word_not(n, x)")

			partition := a.Have(
				"the two share no place and between them hold every "+
					"place below the width, so their sum is the whole mask",
				"x + word_not(n, x) = word_not(n, 0)",
				By(
					xBound,
					// x + word_not(n,x) = word_and(x, word_not(n,x)) + word_or(x, word_not(n,x))
					At(AddAndOr, x, complement),
					At(meetWithComplement, n, x), // the meet is empty
					At(joinWithComplement, n, x), // the join is the whole mask
					// Bare: nothing plus the mask folds where it stands.
					nat_arith.AddLeftZeroClause))
			a.Show(
				"the mask is 2ⁿ - 1, and x cancels off the sum that produced it",
				// Normalized, as AllOnes's: three equations meeting.
				By(
					Normalized,
					partition,
					AllOnes,
					At(nat_arith.AddSym, x, complement), // x + word_not = word_not + x
					At(nat_monus.AddSubCancel, complement, x))) // (word_not + x) - x = word_not
		}),
})}

// ---------------------------------------------------------------------------
// Negating one
// ---------------------------------------------------------------------------

// ValNegOne — the val-face form: negating one lands on
// the largest word the width holds. Pure modular arithmetic, with no
// bit anywhere: the defence word_neg raises around its operand collapses
// once the unit is known to survive its own reduction, and what is
// left, 2ⁿ - 1, is already below the modulus.
//
// The twin's width guard goes because the degenerate width is true
// too, not because it is ignored: at 2ⁿ = 1 every residue is zero and
// so is 1 - 1, which is the side branch below. That degenerate case
// is also the only reason the split is here at all — it is exactly
// where nat_mod(1, 2ⁿ) is not 1.
var ValNegOne = valNegOneThm{family.Add(registry.ProofEntry{
	Name: "ValNegOne",
	Key:  "prop_42a8c14eb5c5de11",
	Build: family.Theorem("∀n:num. word_neg(n, 1) = nat_pow(2, n) - 1",
		func(a *Argument, n Term) {
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			one := a.Ctx().Numeral(1)
			modulus := a.Term("nat_pow(2, n)")
			top := a.Term("nat_pow(2, n) - 1")

			unfolded := a.Have(
				"negating is counting the modulus down by the operand's own residue, then reducing again",
				"word_neg(n, 1) = rem(nat_pow(2, n) - rem(1, nat_pow(2, n)), nat_pow(2, n))",
				By(wordNegDef))
			modPos := a.Have(
				"a power of two is never zero, so the modulus is at least one",
				"1 ≤ nat_pow(2, n)",
				By(
					At(nat_arith.PowTwoNonzero, n),
					At(nat_order.PosIffNonzero, modulus),
					// Bare: the last duality fires on the claim itself.
					nat_order.OneLessEqIffPos))
			topInside := a.Have(
				"so the one taken off the modulus can be put back, which leaves the top word one place short of it",
				"nat_pow(2, n) - 1 < nat_pow(2, n)",
				By(
					modPos,
					At(nat_monus.SubAddCancel, modulus, one),
					At(nat_arith.Add1, top), // suc(top) = top + 1
					At(nat_order.LessThanSucIffLessEq, top, top), // top < suc(top) ⇔ top ≤ top
					nat_order.LessEqRefl))
			wide := a.Assuming(
				a.Term("1 < nat_pow(2, n)"),
				"the degenerate modulus one — the width-zero word, where every residue and 1 - 1 alike are zero",
				Given(func(z *Argument, narrow Fact) {
					unitModulus := z.Have(
						"squeezed between the two bounds, the modulus is one",
						"nat_pow(2, n) = 1",
						By(
							narrow,
							modPos,
							At(nat_order.NotLessThan, one, modulus), // ¬(1 < 2ⁿ) ⇔ 2ⁿ ≤ 1
							At(nat_order.LessEqAntisym, modulus, one))) // 2ⁿ = 1 ⇔ 2ⁿ ≤ 1 ∧ 1 ≤ 2ⁿ
					z.Show(
						"and modulo one nothing survives — neither side reaches past zero",
						By(unitModulus, unfolded, nat_div_mod.ModOne, nat_monus.SubRefl))
				}))
			unitInside := a.Have(
				"above that the unit survives its own reduction",
				"rem(1, nat_pow(2, n)) = 1",
				By(wide, At(nat_div_mod.ModLessThan, one, modulus)))
			reduced := a.Have(
				"so negating one is topping the modulus down by one place",
				"word_neg(n, 1) = rem(nat_pow(2, n) - 1, nat_pow(2, n))",
				By(unitInside, unfolded))
			a.Show(
				"and the top word is already inside the window, so the outer reduction leaves it alone",
				By(reduced, topInside, At(nat_div_mod.ModLessThan, top, modulus)))
		}),
})}

// NegOneIsNotZero — the val-face form: negating one and
// complementing zero are the same word. Two routes to the same value,
// meeting: ValNegOne reaches 2ⁿ - 1 by modular arithmetic, AllOnes by
// counting places.
var NegOneIsNotZero = negOneIsNotZeroThm{family.Add(registry.ProofEntry{
	Name: "NegOneIsNotZero",
	Key:  "prop_f6811b3856ebc7d2",
	Build: family.Theorem("∀n:num. word_neg(n, 1) = word_not(n, 0)",
		func(a *Argument, n Term) {
			a.Show(
				"both sides are the width's largest word",
				By(ValNegOne, AllOnes))
		}),
})}

// ---------------------------------------------------------------------------
// The complement in the ring
// ---------------------------------------------------------------------------
//
// Everything above reads the complement as a magnitude. Here it goes
// back into the ring, where five of the six laws below are one
// sentence said five ways: complementing is negating and stepping back
// one place.
//
// The sentence is NegAsAdd, and its proof is the partition again — x
// and its complement fill the window between them (meetWithComplement
// and joinWithComplement, read through AddAndOr), and the mask is one
// place short of the modulus (maskPlusOne). Put together, x, its
// complement and that one place come to the width exactly, and the
// single monus in the whole part is that sum cancelled against x. The
// degenerate corner where the width less x is the width itself never
// becomes a case: the reduction is left standing where it is, and it
// is the reduction that sends the corner to zero.
//
// Read the other way the same sentence is NotAsSub, and from there the
// remaining three are substitutions of laws the value face already
// has.
// Complementing a negation is NegNeg (NotNeg); complementing a
// difference reverses it, which is NegSub (NotSub); and a sum is a
// difference by the negated summand, so the sum law is the difference
// law read there (NotAdd). Only NotSub pays anything further, and what
// it pays is one regrouping of three summands in the word ring.
//
// SubXor is the outlier and the only one with bits in it. Its
// hypothesis says y sets no position x leaves clear, so every place of
// y is a place of x; then the difference and y divide x's places
// between them with nothing left over and nothing to carry, so adding
// y back to the difference returns x (AddIsOr).
//
// The part opens on the cancellation NotAsSub and SubXor both spend:
// adding a word and taking it off again.

// addSubCancel — adding a word and subtracting it again returns a
// reduced word unchanged. The part's one piece of shared machinery:
// NotAsSub and SubXor each reach their answer as what is left when a
// summand is taken back off a sum already in hand, and this is the
// step that reads it off.
//
// Three moves, all in the value face's ring. A word beside its own
// negation is the zero word (SubRefl, read through word_sub's definition); that
// pair regroups out of the sum (AddAssoc); and the zero word adds
// nothing to a word already below the width (AddZero, whose guard is
// the law's own).
var addSubCancel = addSubCancelThm{family.Add(registry.ProofEntry{
	Name: "addSubCancel",
	Key:  "prop_7002e2b38bd27eb8",
	Build: family.Theorem(Statement{
		Binders: "∀n x y:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_sub(n, word_add(n, x, y), y) = x",
	},
		func(a *Argument, n, x, y Term, xBound Fact) {
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			negY := a.Term("word_neg(n, y)")

			inverse := a.Have(
				"a word beside its own negation is the zero word",
				"word_add(n, y, word_neg(n, y)) = 0",
				By(machine_word.SubRefl, wordSubDef))
			a.Show(
				"so the pair regroups out of the sum, and the zero word leaves a reduced x alone",
				// Normalized: three equations meeting, and no refutation
				// wanted between them.
				By(
					Normalized,
					xBound,
					inverse,
					wordSubDef,
					// word_add(n, x, word_add(n, y, −y)) = word_add(n, word_add(n, x, y), −y)
					At(machine_word.AddAssoc, n, x, y, negY),
					At(machine_word.AddZero, n, x)))
		}),
})}

// NegAsAdd — the val-face form: negating a reduced word
// is complementing it and counting one place further. The keystone the
// rest of this part is read off.
//
// x and its complement partition the window's places, so their sum is
// the mask; the mask counted one further is the modulus. So x together
// with the complement and that extra place come to the width exactly —
// which says the width less x IS the complement counted one further,
// and that is what word_neg reduces.
var NegAsAdd = negAsAddThm{family.Add(registry.ProofEntry{
	Name: "NegAsAdd",
	Key:  "prop_142e6dbcbd263061",
	Build: family.Theorem(Statement{
		Binders: "∀n x:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_neg(n, x) = word_add(n, word_not(n, x), 1)",
	},
		func(a *Argument, n, x Term, xBound Fact) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			complement := a.Term("word_not(n, x)")
			stepped := a.Term("word_not(n, x) + 1")

			partition := a.Have(
				"the two share no place and between them hold every "+
					"place below the width, so their sum is the whole mask",
				"x + word_not(n, x) = word_not(n, 0)",
				By(
					xBound,
					// x + word_not(n,x) = word_and(x, word_not(n,x)) + word_or(x, word_not(n,x))
					At(AddAndOr, x, complement),
					At(meetWithComplement, n, x), // the meet is empty
					At(joinWithComplement, n, x), // the join is the whole mask
					// Bare: nothing plus the mask folds where it stands.
					nat_arith.AddLeftZeroClause))
			regroup := a.Have(
				"count the extra place with the complement rather than with x",
				"(word_not(n, x) + 1) + x = (x + word_not(n, x)) + 1",
				ACRegroupWith(nat_arith.AddAC(a.Ctx())))
			whole := a.Have(
				"so x, its complement and the place between them come to the width exactly",
				"(word_not(n, x) + 1) + x = nat_pow(2, n)",
				// Bare: the mask's own count fires on the claim as the
				// rewrite it is.
				By(partition, regroup, maskPlusOne))
			leftover := a.Have(
				"which says the stepped complement is what the width has left over x",
				"nat_pow(2, n) - x = word_not(n, x) + 1",
				By(whole, At(nat_monus.AddSubCancel, stepped, x))) // ((~x + 1) + x) − x
			a.Show(
				"and negating a reduced word is that leftover, reduced once",
				// Normalized: two equations meeting under a bound already in
				// hand.
				By(
					Normalized,
					xBound,
					leftover,
					wordAddDef,
					At(machine_word.ValNeg, n, x))) // word_neg(n, x) = nat_mod(2ⁿ − x, 2ⁿ)
		}),
})}

// NotAsSub — the val-face form: the complement is the
// negation one place back. NegAsAdd read the other way round: negating
// steps one place forward from the complement, so stepping back
// returns it. The cancellation needs the complement to be a reduced
// word, which it is at every width — a window combinator sets no place
// its window does not hold (Bitop1Bound).
var NotAsSub = notAsSubThm{family.Add(registry.ProofEntry{
	Name: "NotAsSub",
	Key:  "prop_841cc4ea35673a6b",
	Build: family.Theorem(Statement{
		Binders: "∀n x:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_not(n, x) = word_sub(n, word_neg(n, x), 1)",
	},
		func(a *Argument, n, x Term, xBound Fact) {
			complement := a.Term("word_not(n, x)")
			one := a.Ctx().Numeral(1)

			bound := a.Have(
				"a complement is a reduced word at every width",
				"word_not(n, x) < nat_pow(2, n)",
				// ↦ word_bitwise_unary(n, ¬, x) < nat_pow(2, n), which the combinator's
				// own bound closes at its ∀-form install.
				Unfold(machine_word.WordNotDef),
				Cite(word_bits.BitwiseUnaryBound))
			a.Show(
				"negating steps one place forward from the complement, so stepping back returns it",
				// Normalized: both cites arrive as clauses with their
				// guards negated, and both guards are resident.
				By(
					Normalized,
					xBound,
					bound,
					At(NegAsAdd, n, x),                    // word_neg(n, x) = word_add(n, ~x, 1)
					At(addSubCancel, n, complement, one))) // word_sub(n, word_add(n, ~x, 1), 1)
		}),
})}

// NotNeg — the val-face form: complementing a negation
// steps one place back from x. NotAsSub at the negation, where the
// double negation of a reduced word is the word again (NegNeg). A
// negation is a reduction, so it is a reduced word and NotAsSub's
// guard is met.
var NotNeg = notNegThm{family.Add(registry.ProofEntry{
	Name: "NotNeg",
	Key:  "prop_ea6c1e487668c2de",
	Build: family.Theorem(Statement{
		Binders: "∀n x:num.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "word_not(n, word_neg(n, x)) = word_sub(n, x, 1)",
	},
		func(a *Argument, n, x Term, xBound Fact) {
			negX := a.Term("word_neg(n, x)")

			negBound := a.Have(
				"a negation is a reduction, hence a reduced word",
				"word_neg(n, x) < nat_pow(2, n)",
				// ↦ nat_mod(2ⁿ − nat_mod(x, 2ⁿ), 2ⁿ) < 2ⁿ, which is the division
				// bound at that dividend.
				Unfold(machine_word.WordNegDef),
				By(
					At(nat_arith.PowTwoNonzero, n),
					At(nat_div_mod.Division,
						a.Term("nat_pow(2, n) - rem(x, nat_pow(2, n))"), a.Term("nat_pow(2, n)"))))
			a.Show(
				"so the negation may be complemented in turn, and negating it again returns x",
				// Normalized: both cites arrive as clauses with their guards
				// negated, and both guards are resident.
				By(
					Normalized,
					xBound,
					negBound,
					At(NotAsSub, n, negX),          // ~(−x) = word_sub(n, −(−x), 1)
					At(machine_word.NegNeg, n, x))) // −(−x) = x
		}),
})}

// NotSub — the val-face form: complementing a difference
// adds the subtrahend back to the complement of the minuend.
//
// A difference is a reduced word, so NotAsSub applies to it, and
// negating a difference reverses it (NegSub): the complement of x − y
// is y − x stepped one place back. The other side is x's own
// complement, which NotAsSub reads as x's negation stepped back. Both
// sides are then y together with the negations of x and of one, and
// only the grouping differs.
var NotSub = notSubThm{family.Add(registry.ProofEntry{
	Name: "NotSub",
	Key:  "prop_e7fbe5c6c8009be0",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_not(n, word_sub(n, x, y)) = word_add(n, word_not(n, x), y)",
		},
		func(a *Argument, n, x, y Term, xBound Fact) {
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			difference := a.Term("word_sub(n, x, y)")

			subBound := a.Have(
				"a difference is a reduction, hence a reduced word",
				"word_sub(n, x, y) < nat_pow(2, n)",
				// ↦ nat_mod(x + −y, 2ⁿ) < 2ⁿ, which is the division bound at
				// that dividend.
				Unfold(machine_word.WordSubDef),
				Unfold(machine_word.WordAddDef),
				By(
					At(nat_arith.PowTwoNonzero, n),
					At(nat_div_mod.Division,
						a.Term("x + word_neg(n, y)"), a.Term("nat_pow(2, n)"))))
			reversed := a.Have(
				"so the difference may be complemented, and negating a difference reverses it — written as a sum",
				"word_not(n, word_sub(n, x, y)) = word_add(n, word_add(n, y, word_neg(n, x)), word_neg(n, 1))",
				// NegSub bare: it fires on the claim as the rewrite it is.
				// wordSubDef spells the two differences on the right as sums.
				By(subBound, At(NotAsSub, n, difference), machine_word.NegSub, wordSubDef))
			notX := a.Have(
				"and the complement of x is x's negation one place back — written as a sum too",
				"word_not(n, x) = word_add(n, word_neg(n, x), word_neg(n, 1))",
				By(xBound, At(NotAsSub, n, x), wordSubDef))
			a.Show(
				"so both sides are y with the negations of x and of one, and only the grouping differs",
				CalcEq(
					Leg(
						a.Term("word_add(n, word_add(n, y, word_neg(n, x)), word_neg(n, 1))"),
						"the complement of the difference, written out",
						By(reversed)),
					Leg(
						a.Term("word_add(n, y, word_add(n, word_neg(n, x), word_neg(n, 1)))"),
						"regroup the two negations together",
						// Bare: the leg names its own instance, so the law
						// closes it at its ∀-form install.
						Cite(machine_word.AddAssoc)),
					Leg(
						a.Term("word_add(n, word_add(n, word_neg(n, x), word_neg(n, 1)), y)"),
						"and put y last",
						Cite(machine_word.AddSym)),
					FinalLeg(
						"which leaves the complement of x with y added",
						By(notX)),
				))
		}),
})}

// NotAdd — the val-face form: complementing a sum
// complements the first summand and negates the second. A sum is a
// difference by the negated summand — subtracting a negation is adding
// the word back (NegNeg, at the reduced y) — so this is NotSub read at
// that negation, which is itself a reduced word.
var NotAdd = notAddThm{family.Add(registry.ProofEntry{
	Name: "NotAdd",
	Key:  "prop_a4df83936be7f485",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_not(n, word_add(n, x, y)) = word_add(n, word_not(n, x), word_neg(n, y))",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			negY := a.Term("word_neg(n, y)")

			negBound := a.Have(
				"a negation is a reduction, hence a reduced word",
				"word_neg(n, y) < nat_pow(2, n)",
				// ↦ nat_mod(2ⁿ − nat_mod(y, 2ⁿ), 2ⁿ) < 2ⁿ, which is the division
				// bound at that dividend.
				Unfold(machine_word.WordNegDef),
				By(
					At(nat_arith.PowTwoNonzero, n),
					At(nat_div_mod.Division,
						a.Term("nat_pow(2, n) - rem(y, nat_pow(2, n))"), a.Term("nat_pow(2, n)"))))
			asDifference := a.Have(
				"adding a reduced y is subtracting its negation",
				"word_add(n, x, y) = word_sub(n, x, word_neg(n, y))",
				// ↦ word_add(n, x, y) = word_add(n, x, −(−y)), which is the double
				// negation under one summand.
				Unfold(machine_word.WordSubDef),
				By(Normalized, yBound, At(machine_word.NegNeg, n, y))) // −(−y) = y
			a.Show(
				"so the sum law is the difference law, read at that negation",
				By(xBound, negBound, asDifference, At(NotSub, n, x, negY)))
		}),
})}

// SubXor — the val-face form: when y's places all belong to
// x, subtracting y is turning those places off, which is the
// difference. The one law in this part with bits in it.
//
// The hypothesis says y sets no position x leaves clear; since y
// reaches no position past the width either, every place of y is a
// place of x. Then x ⊕ y and y share no place — a place both hold
// would be one where x is clear and y is set — and between them they
// hold exactly x's places. Nothing carries, so adding y back to the
// difference returns x (AddIsOr), and taking y off again is
// addSubCancel.
var SubXor = subXorThm{family.Add(registry.ProofEntry{
	Name: "SubXor",
	Key:  "prop_d1f85cbf6dd8a68c",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
				"0 = word_and(word_not(n, x), y)",
			},
			Conclusion: "word_sub(n, x, y) = word_xor(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound, disjoint Fact) {
			zero := a.Ctx().Numeral(0)
			complement := a.Term("word_not(n, x)")
			difference := a.Term("word_xor(x, y)")

			complementBits := a.Have(
				"the complement's bits are the positions x leaves clear inside the width",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ (¬word_bit(k, x) ∧ (k < n))",
				By(word_bits.BitNot))
			inside := a.Have(
				"so every place of y is a place of x — y sets none x leaves clear, and none past the width either",
				"∀k:num. word_bit(k, y) ⇒ word_bit(k, x)",
				Derive(func(b *Argument) {
					k := b.Fix()
					b.Do(By(
						Normalized,
						complementBits.At(k),
						yBound,
						disjoint,
						At(word_bits.BitOfAnd, complement, y, k),
						At(word_bits.BitBelowBound, n, y, k), // word_bit(k, y) ⇒ k < n
						At(word_bits.BitWordZero, k)))
				}))
			xorBits := a.Have(
				"the difference holds the places where one of the two is set and the other clear",
				"∀k:num. word_bit(k, word_xor(x, y)) ⇔ (¬word_bit(k, x) ⇔ word_bit(k, y))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					// ↦ closes: the leaf IS the difference's bit reading.
					b.Do(Cite(word_bits.BitOfXor))
				}))

			meetTerm := a.Term("word_and(word_xor(x, y), y)")
			meetBits := a.Have(
				"the difference and y hold no place in common — a place both hold is "+
					"one where x is clear and y is set — so their table is the zero word's",
				"∀k:num. word_bit(k, 0) ⇔ word_bit(k, word_and(word_xor(x, y), y))",
				Derive(func(b *Argument) {
					k := b.Fix()
					b.Do(By(
						inside.At(k),
						xorBits.At(k),
						At(word_bits.BitOfAnd, difference, y, k),
						At(word_bits.BitWordZero, k),
						nat_order.LessEqRefl))
				}))
			meet := a.Have(
				"so their meet is the zero word",
				"0 = word_and(word_xor(x, y), y)",
				// Grounded at the pair being equated, as meetWithComplement's
				// — bare, the cite installs with v and w still quantified.
				By(meetBits, At(word_bits.BitsEqAll, zero, meetTerm)))

			joinTerm := a.Term("word_or(word_xor(x, y), y)")
			joinBits := a.Have(
				"and between them they hold exactly x's places — one of the two answers for each",
				"∀k:num. word_bit(k, word_or(word_xor(x, y), y)) ⇔ word_bit(k, x)",
				Derive(func(b *Argument) {
					k := b.Fix()
					b.Do(By(Normalized, inside.At(k), xorBits.At(k), At(word_bits.BitOfOr, difference, y, k)))
				}))
			join := a.Have(
				"so their join is x itself",
				"word_or(word_xor(x, y), y) = x",
				By(joinBits, At(word_bits.BitsEqAll, joinTerm, x)))
			covered := a.Have(
				"every place the difference sets belongs to one of the operands",
				"∀i:num. word_bit(i, word_xor(x, y)) ⇒ word_bit(i, x) ∨ word_bit(i, y)",
				Derive(func(b *Argument) {
					i := b.Fix()
					b.Show(
						"a place neither operand holds is one where the two agree, and there the difference is clear",
						By(xorBits.At(i)))
				}))
			bound := a.Have(
				"so the difference is a reduced word itself",
				"word_xor(x, y) < nat_pow(2, n)",
				// covered stays ∀-shaped: it IS the bound's third
				// antecedent, which the refuter reads at its own position.
				// The part's one refutation.
				By(xBound, yBound, covered, At(coveredBitsBound, n, x, y, difference)))
			sum := a.Have(
				"with the meet empty nothing carries, so adding y back to the difference returns x",
				"word_add(n, word_xor(x, y), y) = x",
				// Normalized: the cite arrives as a clause with its three
				// guards negated, and all three are resident.
				By(Normalized, yBound, bound, meet, join, At(AddIsOr, n, difference, y)))
			a.Show(
				"and taking y off what y was added to returns the difference",
				// Normalized, as above.
				By(Normalized, bound, sum, At(addSubCancel, n, difference, y)))
		}),
})}

// ---------------------------------------------------------------------------
// OrXorEq — where disjunction and difference agree
// ---------------------------------------------------------------------------

// OrXorEq — the meet is empty exactly when join and difference agree.
// The join is the sum of meet and difference; that sum equals its
// right summand exactly when the meet is zero.
var OrXorEq = orXorEqThm{family.Add(registry.ProofEntry{
	Name: "OrXorEq",
	Key:  "prop_c915d13a8cfe9e40",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x y:num.",
			Conclusion: "0 = word_and(x, y) ⇔ word_or(x, y) = word_xor(x, y)",
		},
		func(a *Argument, x, y *Expr[Nat]) {
			a.Show(
				"the join equals the difference exactly when its other summand vanishes",
				By(
					Normalized,
					OrAndXor.At(x, y),
					nat_arith.AddEqSelfRight.At(a.TermAs[Nat]("word_and(x, y)"), a.TermAs[Nat]("word_xor(x, y)"))))
		}),
})}

// ---------------------------------------------------------------------------
// OrXorGen — disjunction as the sum of conjunction and difference
// ---------------------------------------------------------------------------

// bitValueOrSplit — the digit identity under OrXorGen: at one position,
// the or digit is the and digit plus the exactly-one digit. Never both
// summands are set, so the digits add with nothing to carry — the
// whole reason the value-level sum below needs no carry either. The
// table has four rows, and each is one of bit_value's two readings plus a
// zero clause of +.
var bitValueOrSplit = bitValueOrSplitThm{family.Add(registry.ProofEntry{
	Name: "bitValueOrSplit",
	Key:  "prop_3a49a66fc1297243",
	Build: family.Theorem(
		"∀p q:bool. bit_value(p ∧ q) + bit_value((p ∨ q) ∧ ¬(p ∧ q)) = bit_value(p ∨ q)",
		func(a *Argument, p, q Term) {
			zero := a.Ctx().Numeral(0)
			one := a.Ctx().Numeral(1)
			andC := a.Term("p ∧ q")
			xorC := a.Term("(p ∨ q) ∧ ¬(p ∧ q)")
			orC := a.Term("p ∨ q")
			a.Show(
				"row by row: at most one summand digit is ever one, and "+
					"the sum reads the or digit off the zero clauses of +",
				By(
					At(word_bits.BitValueEqOne, andC),
					At(word_bits.BitValueEqZero, andC),
					At(word_bits.BitValueEqOne, xorC),
					At(word_bits.BitValueEqZero, xorC),
					At(word_bits.BitValueEqOne, orC),
					At(word_bits.BitValueEqZero, orC),
					At(nat_arith.AddZero, one),
					At(nat_arith.AddLeftZeroClause, one),
					At(nat_arith.AddZero, zero)))
		}),
})}

// windowOrSplit — the window-sum identity under OrXorGen: over any
// window, the and combinator plus the xor combinator IS the or
// combinator. By induction on the window: empty windows contribute
// nothing, and widening by one place adds each side's weighted digit —
// the or digit splits as the and digit plus the exactly-one digit
// (bitValueOrSplit), the split lifts through the place's weight by
// distributivity, and the previous windows regroup by the hypothesis.
var windowOrSplit = windowOrSplitThm{family.Add(registry.ProofEntry{
	Name: "windowOrSplit",
	Key:  "prop_44ce9e49277ff83",
	Build: family.Theorem(Statement{
		Binders: "∀k x y:num.",
		Conclusion: "word_bitwise_binary(k, «WindowOpAnd», x, y) + " +
			"word_bitwise_binary(k, «WindowOpXor», x, y) = " +
			"word_bitwise_binary(k, «WindowOpOr», x, y)",
		Abbrev: Abbrev{
			{Name: "WindowOpXor", Text: "(λa:bool.λb:bool. (a ∨ b) ∧ (¬a ∨ ¬b))"},
		},
	},
		func(a *Argument) {
			a.Induct("k")
			a.Base(
				"every empty window contributes nothing, and nothing plus nothing is nothing",
				func(b *Argument) {
					b.Fix() // x — spelled in the claims below
					b.Fix() // y
					b.Show(
						"the definition's empty clause opens all three windows to 0",
						By(machine_word.WordBitwiseBinaryDef, nat_arith.AddZero))
				})
			a.Step(
				"each side widens by its weighted digit — digits split by the "+
					"table, places by distributivity, windows by the hypothesis",
				func(b *Argument, ih Fact) {
					x := b.Fix()
					y := b.Fix()
					openAnd := b.Have(
						"widening the and window adds its weighted digit",
						"word_bitwise_binary(suc(k), «WindowOpAnd», x, y) = "+
							"word_bitwise_binary(k, «WindowOpAnd», x, y) + "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∧ word_bit(k, y))",
						By(machine_word.WordBitwiseBinaryDef))
					openXor := b.Have(
						"and the xor window its",
						"word_bitwise_binary(suc(k), «WindowOpXor», x, y) = "+
							"word_bitwise_binary(k, «WindowOpXor», x, y) + "+
							"nat_pow(2, k) * "+
							"bit_value((word_bit(k, x) ∨ word_bit(k, y)) ∧ (¬word_bit(k, x) ∨ ¬word_bit(k, y)))",
						By(machine_word.WordBitwiseBinaryDef))
					openOr := b.Have(
						"and the or window its",
						"word_bitwise_binary(suc(k), «WindowOpOr», x, y) = "+
							"word_bitwise_binary(k, «WindowOpOr», x, y) + "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(machine_word.WordBitwiseBinaryDef))
					digit := b.Have(
						"the or digit splits as the and digit plus the exactly-one digit",
						"bit_value(word_bit(k, x) ∧ word_bit(k, y)) + "+
							"bit_value((word_bit(k, x) ∨ word_bit(k, y)) ∧ (¬word_bit(k, x) ∨ ¬word_bit(k, y))) = "+
							"bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(bitValueOrSplit))
					place := b.Have(
						"so the weighted places split the same way",
						"nat_pow(2, k) * bit_value(word_bit(k, x) ∧ word_bit(k, y)) + "+
							"nat_pow(2, k) * "+
							"bit_value((word_bit(k, x) ∨ word_bit(k, y)) ∧ (¬word_bit(k, x) ∨ ¬word_bit(k, y))) = "+
							"nat_pow(2, k) * bit_value(word_bit(k, x) ∨ word_bit(k, y))",
						By(digit, nat_arith.LeftAddDistrib))
					ihContent, _ := ih.BoundContent()
					prevSplit := NewHypHandle("prevSplit")
					b.Do(
						// Open all three widened windows where they stand;
						// ground the hypothesis at these operands (a kernel
						// specialize, no search) and pull the or side back
						// through it and the place split — the leftover is
						// a pure rearrangement, which the AC kit derives by
						// kernel steps alone.
						prevSplit.FromResident(ihContent),
						openAnd.Rw(), openXor.Rw(), openOr.Rw(),
						prevSplit.Ground(x, y),
						prevSplit.RwRev(), place.RwRev(),
						ACRegroupWith(nat_arith.AddAC(b.Ctx())))
				})
		}),
})}

// OrXorGen — on reduced words, the width-n sum of meet and
// difference is the join. OrAndXor gives the value sum; the join stays
// reduced because every set bit belongs to one of the operands.
var OrXorGen = orXorGenThm{family.Add(registry.ProofEntry{
	Name: "OrXorGen",
	Key:  "prop_4833eb0538de0dd5",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_add(n, word_and(x, y), word_xor(x, y)) = word_or(x, y)",
		},
		func(a *Argument, n, x, y *Expr[Nat], xBound, yBound Fact) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			join := a.TermAs[Nat]("word_or(x, y)")
			covered := a.Have(
				"every set bit of the join belongs to an operand",
				"∀i:num. word_bit(i, word_or(x, y)) ⇒ word_bit(i, x) ∨ word_bit(i, y)",
				Derive(func(b *Argument) {
					i := b.FixAs[Nat]()
					set := b.Assume()
					b.Show(
						"a set bit of the join comes from one of its alternatives",
						By(set, word_bits.BitOfOr.At(x, y, i)))
				}))
			wordOrBound := a.Have(
				"the join is a reduced word",
				"word_or(x, y) < nat_pow(2, n)",
				By(xBound, yBound, covered, coveredBitsBound.At(n, x, y, join)))
			a.Show(
				"the value sum is the join, and reduction fixes that reduced value",
				By(
					wordAddDef,
					OrAndXor,
					wordOrBound,
					nat_div_mod.ModLessThan.At(join, a.TermAs[Nat]("nat_pow(2, n)"))))
		}),
})}
