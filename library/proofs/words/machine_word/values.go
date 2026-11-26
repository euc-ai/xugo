// values.go — the chapter's value face: a word read as a number mod 2^n.
//
// Five parts, marked by banners:
//
// - The val/word translation cluster of the bridge chapter
// - The val-face interface of the width-n word operations
// - The ring laws of width-n word arithmetic, in the STRONG form
// - The additive inverse of width-n words
// - The quantifier transports of the bridge

package machine_word

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_congruence"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// ---------------------------------------------------------------------------
// The val/word translation cluster of the bridge chapter
// ---------------------------------------------------------------------------
//
// the round trip between a word and its value, read on the val face,
// where a word IS its value. The injection word(k) is the reduction
// nat_mod(k, 2^n) and val is the identity, so every member lands as a
// raw-nat_mod fact about residues and their representatives: below the
// width a value is its own remainder (nat_div_mod.ModLessThan), among
// values below the width the remainder pins the value
// (ModInjectiveBelow), and a congruence is an equality of remainders by
// nat_cong's definition, which the members unfold.
//
// The val face never needs the width positive, so these members state
// no such guard. A primed width binder (n') is kept wherever the
// statement's own word binder already claimed the letter n.

// ValModRefl — below the width, a value is its own reduction: the
// round trip val ∘ word fixes exactly the values already in range.
// One statement serves the val-face and the word-face readings, which
// translate identically here because word is the reduction
// and val forgets nothing, and the disjunctive spelling of the same
// fact (¬(n < 2^n') ∨ n = nat_mod(n, 2^n')) normalizes to this statement
// as well.
var ValModRefl = valModReflThm{family.Add(registry.ProofEntry{
	Name: "ValModRefl",
	Key:  "prop_3e61f4a7d054dc6e",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "x = rem(x, nat_pow(2, n))",
		},
		func(a *Argument, n, x Term, xBound Fact) {
			width := a.Term("nat_pow(2, n)")
			a.Show(
				"below the width, a value is its own remainder",
				By(xBound, At(nat_div_mod.ModLessThan, x, width)))
		}),
})}

// ValWordEqEq — the fixed-point fact in the biconditional spelling,
// where the converse carries content: a fixed point of the reduction
// is a remainder, and a remainder sits below its divisor (Division's
// bound, live because a power of two is never zero).
var ValWordEqEq = valWordEqEqThm{family.Add(registry.ProofEntry{
	Name: "ValWordEqEq",
	Key:  "prop_63af8f98dc516725",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n' n:num.",
			Conclusion: "n < nat_pow(2, n') ⇔ n = rem(n, nat_pow(2, n'))",
		},
		func(a *Argument, np, n Term) {
			width := a.Term("nat_pow(2, n')")
			forward := a.Have(
				"below the width, a value is its own remainder",
				"n < nat_pow(2, n') ⇒ n = rem(n, nat_pow(2, n'))",
				Derive(func(b *Argument) {
					below := b.Assume()
					b.Do(By(below, At(nat_div_mod.ModLessThan, n, width)))
				}))
			backward := a.Have(
				"a fixed point of the reduction is a remainder, hence below the width",
				"n = rem(n, nat_pow(2, n')) ⇒ n < nat_pow(2, n')",
				Derive(func(b *Argument) {
					fixed := b.Assume()
					b.Do(By(Normalized, fixed, At(nat_arith.PowTwoNonzero, np), At(nat_div_mod.Division, n, width)))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ValWordCong — reducing loses no residue: a value and its reduction
// are congruent modulo the width. It is ℕ's own residue law read at the
// width, and nothing more.
var ValWordCong = valWordCongThm{family.Add(registry.ProofEntry{
	Name: "ValWordCong",
	Key:  "prop_de2cedc55ec22eeb",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n x:num.",
			Conclusion: "rem(x, nat_pow(2, n)) ≡ x (mod nat_pow(2, n))",
		},
		func(a *Argument, n, x Term) {
			width := a.Term("nat_pow(2, n)")
			a.Show(
				"a number is congruent to its own residue, at the width",
				By(At(nat_congruence.ResidueCongruent, x, width)))
		}),
})}

// ValCong — on values below the width, congruence IS equality: the
// residues of a width form a system of representatives. Forward is
// reflexivity read through the congruence; backward, congruent values
// leave the same remainder, and below the width the remainder pins the
// value.
var ValCong = valCongThm{family.Add(registry.ProofEntry{
	Name: "ValCong",
	Key:  "prop_91ede854d1fe3af4",
	Build: family.Theorem(
		Statement{
			Binders: "∀n v w:num.",
			Hypotheses: []string{
				"v < nat_pow(2, n)",
				"w < nat_pow(2, n)",
			},
			Conclusion: "v = w ⇔ v ≡ w (mod nat_pow(2, n))",
		},
		func(a *Argument, n, v, w Term, vBound, wBound Fact) {
			width := a.Term("nat_pow(2, n)")
			forward := a.Have(
				"equal values are congruent outright",
				"v = w ⇒ v ≡ w (mod nat_pow(2, n))",
				Derive(func(b *Argument) {
					same := b.Assume() // v = w
					// Unfolding the congruence asks for equal residues, which
					// putting w for v makes reflexive.
					b.Do(Unfold(nat_congruence.CongDef), same.Rw(), Basic())
				}))
			backward := a.Have(
				"below the width, congruence pins the value",
				"v ≡ w (mod nat_pow(2, n)) ⇒ v = w",
				Derive(func(b *Argument) {
					cong := b.Assume()
					sameRem := b.Have(
						"congruent values leave the same remainder",
						"rem(v, nat_pow(2, n)) = rem(w, nat_pow(2, n))",
						// The chapter's own characterization, read at (n, v, w): the
						// definition cited bare does not find this instance by
						// search under the canonical binder order.
						By(cong, At(WordEq, n, v, w)))
					b.Do(By(vBound, wBound, sameRem, At(nat_div_mod.ModInjectiveBelow, v, w, width)))
				}))
			a.Do(By(forward, backward))
		}),
})}

// WordEq — two words are equal exactly when their values are
// congruent: on the val face, word equality is equality of reductions,
// which is nat_cong's definition read right to left.
var WordEq = wordEqThm{family.Add(registry.ProofEntry{
	Name: "WordEq",
	Key:  "prop_cd208942e11c5a99",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n x y:num.",
			Conclusion: "rem(x, nat_pow(2, n)) = rem(y, nat_pow(2, n)) ⇔ x ≡ y (mod nat_pow(2, n))",
		},
		func(a *Argument, n, x, y Term) {
			// Unfolding the congruence leaves the two sides identical, which
			// closes the section; the definition cited bare does not close
			// this by search under the canonical binder order.
			a.Do(Unfold(nat_congruence.CongDef))
		}),
})}

// WordModSize — a word carries no residue beyond its width: reducing a
// reduction changes nothing, so the injection is idempotent on values.
var WordModSize = wordModSizeThm{family.Add(registry.ProofEntry{
	Name: "WordModSize",
	Key:  "prop_ae647a49933d5331",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n' n:num.",
			Conclusion: "rem(n, nat_pow(2, n')) = rem(rem(n, nat_pow(2, n')), nat_pow(2, n'))",
		},
		func(a *Argument, np, n Term) {
			a.Show(
				"reducing twice by the width is reducing once",
				By(nat_div_mod.ModModRefl))
		}),
})}

// ValWordGalois — the round trip as an adjunction: a value below the
// width equals w exactly when it is in range and w is its reduction.
// Forward, the value is its own reduction under the guard; backward, a
// reduced witness below the width already is the word itself.
var ValWordGalois = valWordGaloisThm{family.Add(registry.ProofEntry{
	Name: "ValWordGalois",
	Key:  "prop_5c17d672323dda33",
	Build: family.Theorem(
		Statement{
			Binders: "∀n' w n:num.",
			Hypotheses: []string{
				"w < nat_pow(2, n')",
			},
			Conclusion: "n = w ⇔ n < nat_pow(2, n') ∧ w = rem(n, nat_pow(2, n'))",
		},
		func(a *Argument, np, w, n Term, wBound Fact) {
			width := a.Term("nat_pow(2, n')")
			forward := a.Have(
				"a value already below the width is its own reduction",
				"n = w ⇒ (n < nat_pow(2, n')) ∧ (w = rem(n, nat_pow(2, n')))",
				Derive(func(b *Argument) {
					eq := b.Assume()
					b.Do(By(eq, wBound, At(nat_div_mod.ModLessThan, w, width)))
				}))
			backward := a.Have(
				"a reduced witness below the width is the word itself",
				"(n < nat_pow(2, n')) ∧ (w = rem(n, nat_pow(2, n'))) ⇒ n = w",
				Derive(func(b *Argument) {
					both := b.Assume()
					collapse := b.Have(
						"below the width, n survives its reduction",
						"rem(n, nat_pow(2, n')) = n",
						By(both, At(nat_div_mod.ModLessThan, n, width)))
					b.Do(By(Normalized, both, collapse))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ---------------------------------------------------------------------------
// The val-face interface of the width-n word operations
// ---------------------------------------------------------------------------
//
// under the range guards, each minted operation reads back as a raw ℕ
// expression. Where the ring laws below hold for ALL inputs because
// nat_mod absorbs everything, the members here are the guards' own
// content: x < 2^n is exactly what
// collapses an inner reduction nat_mod(x, 2^n) to x (nat_div_mod's
// ModLessThan), so a reduced word's operation forgets its defensive
// reductions and the plain arithmetic surfaces. The Cases members carry
// the guard one step further: with both operands reduced, the raw
// result lands under 2·2^n, and ModSmallCases turns the outer
// reduction into an explicit overflow case split.

// ValNeg — on a reduced word, negation is the plain complement to 2^n,
// still reduced once: word_neg's inner defensive reduction of x is the
// guard's first casualty (ModLessThan), and nothing else moves.
var ValNeg = valNegThm{family.Add(registry.ProofEntry{
	Name: "ValNeg",
	Key:  "prop_3082acbcf120cf6d",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_neg(n, x) = rem(nat_pow(2, n) - x, nat_pow(2, n))",
		},
		func(a *Argument, n, x Term, xBound Fact) {
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			width := a.Term("nat_pow(2, n)")
			a.Show(
				"the inner reduction of x collapses under the guard",
				By(xBound, wordNegDef, At(nat_div_mod.ModLessThan, x, width)))
		}),
})}

// ValSub — on reduced words, subtraction is addition of the plain
// complement, under one reduction: unfolding word_sub through word_add leaves
// nat_mod(x + word_neg(n, y), 2^n), ValNeg reads the negation as nat_mod(2^n − y, 2^n),
// and ModAddModRight absorbs that inner reduction into the sum's.
var ValSub = valSubThm{family.Add(registry.ProofEntry{
	Name: "ValSub",
	Key:  "prop_acc1179779fa9dac",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y.",
			Hypotheses: []string{
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_sub(n, x, y) = rem(x + (nat_pow(2, n) - y), nat_pow(2, n))",
		},
		func(a *Argument, n, x, y Term, yBound Fact) {
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			width := a.Term("nat_pow(2, n)")
			unfold := a.Have(
				"subtraction is one reduction of x plus the negation",
				"word_sub(n, x, y) = rem(x + word_neg(n, y), nat_pow(2, n))",
				By(wordSubDef, wordAddDef))
			negY := a.Have(
				"the negation of the reduced y is its plain complement, reduced",
				"word_neg(n, y) = rem(nat_pow(2, n) - y, nat_pow(2, n))",
				By(yBound, ValNeg))
			a.Show(
				"the sum absorbs the complement's reduction",
				By(unfold, negY, At(nat_div_mod.ModAddModRight, x, a.Term("nat_pow(2, n) - y"), width)))
		}),
})}

// ValUnsignedDiv — on reduced words, unsigned division is plain division:
// both defensive reductions collapse under their guards, and nat_div sees
// the raw operands.
var ValUnsignedDiv = valUnsignedDivThm{family.Add(registry.ProofEntry{
	Name: "ValUnsignedDiv",
	Key:  "prop_fa17d6b77cdb310f",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_unsigned_div(n, x, y) = div(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			wordUnsignedDivDef := a.Ctx().ConstDefNormalized("word_unsigned_div")
			width := a.Term("nat_pow(2, n)")
			a.Show(
				"both operand reductions collapse under their guards",
				By(
					xBound,
					yBound,
					wordUnsignedDivDef,
					At(nat_div_mod.ModLessThan, x, width),
					At(nat_div_mod.ModLessThan, y, width)))
		}),
})}

// ValUnsignedMod — and unsigned remainder is plain remainder, by the same
// double collapse.
var ValUnsignedMod = valUnsignedModThm{family.Add(registry.ProofEntry{
	Name: "ValUnsignedMod",
	Key:  "prop_694cde040da5724",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_unsigned_mod(n, x, y) = rem(x, y)",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			wordUnsignedModDef := a.Ctx().ConstDefNormalized("word_unsigned_mod")
			width := a.Term("nat_pow(2, n)")
			a.Show(
				"both operand reductions collapse under their guards",
				By(
					xBound,
					yBound,
					wordUnsignedModDef,
					At(nat_div_mod.ModLessThan, x, width),
					At(nat_div_mod.ModLessThan, y, width)))
		}),
})}

// AddCases — word addition of reduced words is the overflow case
// split: the raw sum either fits and is the answer, or overflows
// once and pays back one 2^n. The two guards put the sum under 2·2^n
// (strict pairwise add-monotonicity), which is precisely where
// ModSmallCases reads the reduction as that COND.
var AddCases = addCasesThm{family.Add(registry.ProofEntry{
	Name: "AddCases",
	Key:  "prop_22bbc2507717939",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_add(n, x, y) = COND(x + y < nat_pow(2, n), x + y, x + y - nat_pow(2, n))",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			width := a.Term("nat_pow(2, n)")
			small := a.Have(
				"two reduced words sum to under twice the modulus",
				"x + y < nat_pow(2, n) + nat_pow(2, n)",
				By(xBound, yBound, At(nat_order.LessThanAdd2, x, y, width, width)))
			a.Show(
				"under twice the modulus, the reduction is the overflow case split",
				By(small, wordAddDef, At(nat_div_mod.ModSmallCases, a.Term("x + y"), width)))
		}),
})}

// SubCases — word subtraction of reduced words is the borrow case
// split: x − y where it does not borrow, and x + (2^n − y) where
// it does. Through ValSub the operation is one reduction of
// s := x + (2^n − y), which sits under 2·2^n, and ModSmallCases's own
// case split CROSSES the borrow's: when y ≤ x the complement makes s
// overflow — s is (x − y) + 2^n on the nose — so paying back the 2^n
// is exactly the borrow-free difference; when x < y the sum stays
// short of 2^n and survives reduction whole.
var SubCases = subCasesThm{family.Add(registry.ProofEntry{
	Name: "SubCases",
	Key:  "prop_f56eed241e2495dd",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x y.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_sub(n, x, y) = COND(y ≤ x, x - y, x + (nat_pow(2, n) - y))",
		},
		func(a *Argument, n, x, y Term, xBound, yBound Fact) {
			width := a.Term("nat_pow(2, n)")
			comp := a.Term("nat_pow(2, n) - y") // y's complement to the modulus
			s := a.Term("x + (nat_pow(2, n) - y)")
			diff := a.Term("x - y")

			yLeWidth := a.Have(
				"the guard on y, weakened to what the monus algebra asks",
				"y ≤ nat_pow(2, n)",
				By(yBound, At(nat_order.LessEqOfLessThan, y, width)))
			topUp := a.Have(
				"the complement tops y back up to the modulus",
				"(nat_pow(2, n) - y) + y = nat_pow(2, n)",
				By(yLeWidth, At(nat_monus.SubAddCancel, width, y)))
			compLe := a.Have(
				"so the complement is at most the modulus",
				"nat_pow(2, n) - y ≤ nat_pow(2, n)",
				By(topUp, At(nat_order.LessEqAdd, comp, y)))
			sBound := a.Have(
				"and s sits under twice the modulus",
				"x + (nat_pow(2, n) - y) < nat_pow(2, n) + nat_pow(2, n)",
				By(
					xBound,
					compLe,
					At(nat_order.LessEqLessThanAdd2, comp, x, width, width),
					At(nat_arith.AddSym, x, comp)))
			valsub := a.Have(
				"through the val-face, the subtraction is one reduction of s",
				"word_sub(n, x, y) = rem(x + (nat_pow(2, n) - y), nat_pow(2, n))",
				By(yBound, ValSub))

			a.Cases(a.Term("y ≤ x"))
			a.When(
				"y ≤ x: the complement makes s overflow, and paying back the modulus is the borrow-free difference",
				func(b *Argument, le Fact) {
					split := b.Have(
						"the difference and y reassemble x",
						"(x - y) + y = x",
						By(le, At(nat_monus.SubAddCancel, x, y)))
					rep := b.Have(
						"so s is the difference plus one whole modulus",
						"x + (nat_pow(2, n) - y) = (x - y) + nat_pow(2, n)",
						By(split, topUp, At(nat_arith.AddAssoc, diff, y, comp), At(nat_arith.AddSym, y, comp)))
					grows := b.Have(
						"a whole modulus plus a difference is at least the modulus",
						"nat_pow(2, n) ≤ (x - y) + nat_pow(2, n)",
						Cite(nat_order.LessEqAddLeft))
					over := b.Have(
						"which puts s at or above the modulus",
						"¬(x + (nat_pow(2, n) - y) < nat_pow(2, n))",
						By(rep, grows, nat_order.NotLessThan))
					payBack := b.Have(
						"and paying the modulus back leaves the difference",
						"(x + (nat_pow(2, n) - y)) - nat_pow(2, n) = x - y",
						By(rep, At(nat_monus.AddSubCancel, diff, width)))
					inner := b.Have(
						"so the reduction of s is the borrow-free difference",
						"rem(x + (nat_pow(2, n) - y), nat_pow(2, n)) = x - y",
						By(sBound, At(nat_div_mod.ModSmallCases, s, width), over, payBack))
					b.Show(
						"and the case split takes it",
						By(le, valsub, inner))
				})
			a.Otherwise(
				"x < y: the sum stays short of the modulus and survives reduction whole",
				func(b *Argument, gt Fact) {
					xLtY := b.Have(
						"the failed borrow test is the strict order the other way",
						"x < y",
						By(gt, nat_order.NotLessEq))
					under := b.Have(
						"so s stays under the modulus — x is short of the y the complement tops up",
						"x + (nat_pow(2, n) - y) < nat_pow(2, n)",
						By(
							xLtY,
							topUp,
							At(nat_order.LessEqRefl, comp),
							At(nat_order.LessEqLessThanAdd2, comp, x, comp, y),
							At(nat_arith.AddSym, x, comp)))
					inner := b.Have(
						"and survives its reduction whole",
						"rem(x + (nat_pow(2, n) - y), nat_pow(2, n)) = x + (nat_pow(2, n) - y)",
						By(sBound, At(nat_div_mod.ModSmallCases, s, width), under))
					b.Show(
						"and the case split keeps it",
						By(gt, valsub, inner))
				})
		}),
})}

// NegCases — word negation of a reduced word is a case split at
// zero: zero is its own negation (the complement is the whole
// modulus, whose reduction vanishes), and a nonzero word's negation is
// its plain complement, which lands strictly under the modulus and
// survives reduction.
var NegCases = negCasesThm{family.Add(registry.ProofEntry{
	Name: "NegCases",
	Key:  "prop_9458e69cf3232f4a",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_neg(n, x) = COND(0 = x, 0, nat_pow(2, n) - x)",
		},
		func(a *Argument, n, x Term, xBound Fact) {
			width := a.Term("nat_pow(2, n)")
			comp := a.Term("nat_pow(2, n) - x") // x's complement to the modulus
			zero := a.Ctx().Numeral(0)

			valneg := a.Have(
				"through the val-face, the negation is the reduced complement",
				"word_neg(n, x) = rem(nat_pow(2, n) - x, nat_pow(2, n))",
				By(xBound, ValNeg))

			a.Cases(a.Term("0 = x"))
			a.When(
				"0 = x: the complement is the whole modulus, whose reduction vanishes",
				func(b *Argument, isZero Fact) {
					whole := b.Have(
						"taking nothing away leaves the modulus",
						"nat_pow(2, n) - 0 = nat_pow(2, n)",
						By(At(nat_monus.AddSubCancel, width, zero), nat_arith.AddZero))
					b.Show(
						"and a whole modulus reduces to zero",
						By(isZero, valneg, whole, At(nat_div_mod.ModRefl, width)))
				})
			a.Otherwise(
				"x ≠ 0: the complement falls strictly under the modulus and survives reduction",
				func(b *Argument, nonzero Fact) {
					pos := b.Have(
						"a nonzero word is positive",
						"0 < x",
						By(nonzero, nat_order.PosIffNonzero))
					xLeWidth := b.Have(
						"the guard, weakened to what the monus algebra asks",
						"x ≤ nat_pow(2, n)",
						By(xBound, At(nat_order.LessEqOfLessThan, x, width)))
					under := b.Have(
						"so the complement is short of the modulus by that positive x",
						"nat_pow(2, n) - x < nat_pow(2, n)",
						By(
							pos,
							xLeWidth,
							At(nat_order.LessEqRefl, comp),
							At(nat_order.LessEqLessThanAdd2, comp, zero, comp, x),
							At(nat_arith.AddZero, comp),
							At(nat_monus.SubAddCancel, width, x)))
					collapse := b.Have(
						"and survives its reduction",
						"rem(nat_pow(2, n) - x, nat_pow(2, n)) = nat_pow(2, n) - x",
						By(under, At(nat_div_mod.ModLessThan, comp, width)))
					b.Show(
						"so the case split keeps the plain complement",
						By(nonzero, valneg, collapse))
				})
		}),
})}

// ---------------------------------------------------------------------------
// The ring laws of width-n word arithmetic, in the STRONG form
// ---------------------------------------------------------------------------
//
// Hypothesis-free and ∀-quantified over the width.
//
// Each member here states the strong form: a uniform term-level
// reading of the type-level law would relativize every word binder with
// a range guard `x < 2^n`, but nat_mod absorbs those guards, so the true
// law needs none. The
// mathematical content sits one level down, in nat_div_mod's raw-nat_mod
// algebra (mint-once); a member here is the width-instantiated
// reading of that layer through word_add's definition.

// AddAssoc — width-n addition associates, for every width and ALL
// values (reduced or not): the strong form. Unfolding
// word_add turns both sides into raw-nat_mod reductions at 2^n, which is
// nat_div_mod.ModAddAssoc at that modulus.
var AddAssoc = addAssocThm{family.Add(registry.ProofEntry{
	Name: "AddAssoc",
	Key:  "prop_7cd680de8dc4d08e",
	Build: family.Theorem(
		"∀n x y z:num. word_add(n, x, word_add(n, y, z)) = word_add(n, word_add(n, x, y), z)",
		func(a *proof.Argument, n, x, y, z proof.Term) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			a.Do(proof.By(nat_div_mod.ModAddAssoc, wordAddDef))
		}),
})}

// AddSym — width-n addition commutes, for every width and all values:
// the strong form. Unfolding word_add puts the commutation
// under the one shared reduction, where it is + commuting.
var AddSym = addSymThm{family.Add(registry.ProofEntry{
	Name: "AddSym",
	Key:  "prop_264328db31ac12bc",
	Build: family.Theorem(
		"∀n x y:num. word_add(n, x, y) = word_add(n, y, x)",
		func(a *proof.Argument, n, x, y proof.Term) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			a.Do(proof.By(nat_arith.AddSym, wordAddDef))
		}),
})}

// AddZero — zero is the additive identity on the words of width n:
// the one ring law here that KEEPS its range
// guard. Both sums collapse to the bare x by the zero clauses of +, but
// what word_add then answers is nat_mod(x, 2^n) — the reduction fixes exactly
// the values already below the modulus, so `x = word_add(n, x, 0)` reads x
// in range and the guard is the law's real content, not the walker's
// scaffolding. ModLessThan is that reading.
var AddZero = addZeroThm{family.Add(registry.ProofEntry{
	Name: "AddZero",
	Key:  "prop_f87b15b873d2884a",
	Build: family.Theorem(
		Statement{
			Binders: "∀n:num. ∀x.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "x = word_add(n, x, 0) ∧ x = word_add(n, 0, x)",
		},
		func(a *proof.Argument, n, x proof.Term, small proof.Fact) {
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			a.Do(proof.By(
				small,
				nat_arith.AddZero,
				nat_arith.AddLeftZeroClause,
				// x < nat_pow(2, n) ⇒ nat_mod(x, nat_pow(2, n)) = x
				proof.At(nat_div_mod.ModLessThan, x, a.Term("nat_pow(2, n)")),
				wordAddDef))
		}),
})}

// MulSym — width-n multiplication commutes, for every width and all
// values: the strong form. AddSym's multiplicative twin,
// with · commuting under the reduction.
var MulSym = mulSymThm{family.Add(registry.ProofEntry{
	Name: "MulSym",
	Key:  "prop_aa2ea3bbea9ba938",
	Build: family.Theorem(
		"∀n x y:num. word_mul(n, x, y) = word_mul(n, y, x)",
		func(a *proof.Argument, n, x, y proof.Term) {
			wordMulDef := a.Ctx().ConstDefNormalized("word_mul")
			a.Do(proof.By(nat_arith.MulSym, wordMulDef))
		}),
})}

// MulAssoc — width-n multiplication associates, for every width and ALL
// values (reduced or not): the strong form. Unfolding
// word_mul turns both sides into raw-nat_mod reductions at 2^n, which is
// nat_div_mod.ModMulAssoc at that modulus — AddAssoc mutatis mutandis.
var MulAssoc = mulAssocThm{family.Add(registry.ProofEntry{
	Name: "MulAssoc",
	Key:  "prop_732106871cf6afe5",
	Build: family.Theorem(
		"∀n x y z:num. word_mul(n, x, word_mul(n, y, z)) = word_mul(n, word_mul(n, x, y), z)",
		func(a *proof.Argument, n, x, y, z proof.Term) {
			wordMulDef := a.Ctx().ConstDefNormalized("word_mul")
			a.Do(proof.By(nat_div_mod.ModMulAssoc, wordMulDef))
		}),
})}

// MulZero — zero absorbs width-n multiplication: the strong
// form. Guard-free where AddZero is not: both products collapse to the
// literal 0 by the zero clauses of ·, and zero is its own remainder at
// EVERY modulus (ZeroMod), so no range hypothesis is consumed.
var MulZero = mulZeroThm{family.Add(registry.ProofEntry{
	Name: "MulZero",
	Key:  "prop_9209cfe1a966b6b",
	Build: family.Theorem(
		"∀n x:num. (0 = word_mul(n, x, 0)) ∧ (0 = word_mul(n, 0, x))",
		func(a *proof.Argument, n, x proof.Term) {
			wordMulDef := a.Ctx().ConstDefNormalized("word_mul")
			a.Do(proof.By(
				Normalized,
				nat_arith.MulZero,
				nat_arith.MulLeftZeroClause,
				nat_div_mod.ZeroMod,
				wordMulDef))
		}),
})}

// CongAdd — word_add answers congruent to the raw sum, mod 2^n: the reading
// that makes word_add "addition mod 2^n", and the bridge every
// residue-arithmetic consumer crosses first. Unfolding the congruence
// makes it an equality of two remainders; unfolding word_add makes the left
// one a reduction applied twice, and the double reduction collapses.
var CongAdd = congAddThm{family.Add(registry.ProofEntry{
	Name: "CongAdd",
	Key:  "prop_7dd0485aa78f45d",
	Build: family.Theorem(
		"∀n x y:num. word_add(n, x, y) ≡ x + y (mod nat_pow(2, n))",
		func(a *proof.Argument, n, x, y proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			a.Do(proof.By(natCongDef, nat_div_mod.ModModRefl, wordAddDef))
		}),
})}

// CongMul — word_mul answers congruent to the raw product, mod 2^n:
// CongAdd's multiplicative twin, same three sentences with word_mul's
// defining reduction in place of word_add's.
var CongMul = congMulThm{family.Add(registry.ProofEntry{
	Name: "CongMul",
	Key:  "prop_bc21871e584e47ba",
	Build: family.Theorem(
		"∀n x y:num. word_mul(n, x, y) ≡ x * y (mod nat_pow(2, n))",
		func(a *proof.Argument, n, x, y proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordMulDef := a.Ctx().ConstDefNormalized("word_mul")
			a.Do(proof.By(natCongDef, nat_div_mod.ModModRefl, wordMulDef))
		}),
})}

// ---------------------------------------------------------------------------
// The additive inverse of width-n words
// ---------------------------------------------------------------------------
//
// `word_neg` is the complement to the next multiple of the width, and
// `word_sub` is addition of that complement.
//
// The congruence laws (CongNeg, CongSub, and the equations built on
// them) are hypothesis-free like the ring laws: nat_mod absorbs unreduced
// inputs. A range guard `x < 2^n` appears exactly where a statement
// reads a VALUE back — a reduced word is pinned by its residue
// (nat_div_mod.ModInjectiveBelow), an unreduced one is not — and there
// the guard is genuine, not the walker's decoration. The mathematics
// again sits one level down, in nat_div_mod's raw-nat_mod algebra: the
// complement fact is ModAddComplement at modulus 2^n, and everything
// here is bookkeeping around it through the definitions.

// NegZero — the zero word is its own negation. Unfolding word_neg, the
// inner residue of 0 vanishes, the monus hands the width back whole,
// and the width's own remainder is zero.
var NegZero = negZeroThm{family.Add(registry.ProofEntry{
	Name: "NegZero",
	Key:  "prop_a352753ff555244d",
	Build: family.Theorem("∀n:num. 0 = word_neg(n, 0)",
		func(a *proof.Argument, n proof.Term) {
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			survives := a.Have(
				"subtracting nothing leaves the width whole",
				"nat_pow(2, n) - 0 = nat_pow(2, n)",
				proof.By(nat_monus.AddSubCancel, nat_arith.AddZero))
			a.Do(proof.By(wordNegDef, nat_div_mod.ZeroMod, survives, nat_div_mod.ModRefl))
		}),
})}

// SubZero — subtracting the zero word returns a reduced word intact:
// through NegZero the subtraction is addition of zero, so word_sub
// collapses to bare reduction, and the guard pins the value.
var SubZero = subZeroThm{family.Add(registry.ProofEntry{
	Name: "SubZero",
	Key:  "prop_b43d76c729679af5",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "x = word_sub(n, x, 0)",
	},
		func(a *proof.Argument, n, x proof.Term, below proof.Fact) {
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			reduced := a.Have(
				"subtracting the zero word is bare reduction",
				"word_sub(n, x, 0) = rem(x, nat_pow(2, n))",
				proof.By(wordSubDef, wordAddDef, NegZero, nat_arith.AddZero))
			a.Do(proof.By(Normalized, below, reduced, nat_div_mod.ModLessThan))
		}),
})}

// CongNeg — a word and its negation sum to zero modulo the width, for
// EVERY input: word_neg(n, x) is by definition the complement that tops
// the residue of x up to the width, so the sum lands on a multiple of
// 2^n. This is the group law the whole file spends: subtraction
// inherits its algebra from it one member at a time.
var CongNeg = congNegThm{family.Add(registry.ProofEntry{
	Name: "CongNeg",
	Key:  "prop_b716ad5cbbb8206f",
	Build: family.Theorem("∀n x:num. word_neg(n, x) + x ≡ 0 (mod nat_pow(2, n))",
		func(a *proof.Argument, n, x proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			absorbed := a.Have(
				"the negation's outer reduction is absorbed into the sum",
				"rem(word_neg(n, x) + x, nat_pow(2, n)) = "+
					"rem(x + (nat_pow(2, n) - rem(x, nat_pow(2, n))), nat_pow(2, n))",
				proof.By(wordNegDef, nat_div_mod.ModAddModLeft, nat_arith.AddSym))
			complement := a.Have(
				"topping x up to the next multiple leaves no remainder",
				"rem(x + (nat_pow(2, n) - rem(x, nat_pow(2, n))), nat_pow(2, n)) = 0",
				proof.By(proof.At(nat_arith.PowTwoNonzero, n), nat_div_mod.ModAddComplement))
			a.Do(proof.By(natCongDef, absorbed, complement, nat_div_mod.ZeroMod))
		}),
})}

// SubRefl — a word minus itself is the zero word, for every input:
// word_sub unfolds to the sum CongNeg reduces to zero.
var SubRefl = subReflThm{family.Add(registry.ProofEntry{
	Name: "SubRefl",
	Key:  "prop_8c8d5bf19a6b91e2",
	Build: family.Theorem("∀n x:num. 0 = word_sub(n, x, x)",
		func(a *proof.Argument, n, x proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			cancels := a.Have(
				"the negation cancels its own word modulo the width",
				"rem(word_neg(n, x) + x, nat_pow(2, n)) = 0",
				proof.By(CongNeg, natCongDef, nat_div_mod.ZeroMod))
			a.Do(proof.By(wordSubDef, wordAddDef, nat_arith.AddSym, cancels))
		}),
})}

// CongSub — subtraction inverts addition modulo the width, for every
// input: (x − y) + y ≡ x. Unfolding word_sub places y's negation block
// beside y; CongNeg reduces the block to zero and x is what remains.
var CongSub = congSubThm{family.Add(registry.ProofEntry{
	Name: "CongSub",
	Key:  "prop_ec43dba89f7989c4",
	Build: family.Theorem("∀n x y:num. word_sub(n, x, y) + y ≡ x (mod nat_pow(2, n))",
		func(a *proof.Argument, n, x, y proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			negBlock := a.Have(
				"y's negation block reduces to zero",
				"rem(word_neg(n, y) + y, nat_pow(2, n)) = 0",
				proof.By(CongNeg, natCongDef, nat_div_mod.ZeroMod))
			unfolded := a.Have(
				"the difference, written raw",
				"word_sub(n, x, y) = rem(x + word_neg(n, y), nat_pow(2, n))",
				proof.By(wordSubDef, wordAddDef))
			regrouped := a.Have(
				"the difference plus y, absorbed and regrouped around the block",
				"rem(word_sub(n, x, y) + y, nat_pow(2, n)) = rem(x + (word_neg(n, y) + y), nat_pow(2, n))",
				proof.By(unfolded, nat_div_mod.ModAddModLeft, nat_arith.AddAssoc))
			collapsed := a.Have(
				"the zero block vanishes beside x",
				"rem(x + (word_neg(n, y) + y), nat_pow(2, n)) = rem(x, nat_pow(2, n))",
				proof.By(negBlock, nat_div_mod.ModAddModRight, nat_arith.AddZero))
			a.Do(proof.By(natCongDef, regrouped, collapsed))
		}),
})}

// NegEqZero — among reduced words, only zero is its own image under
// negation-to-zero: 0 = word_neg(n, x) forces x = 0. A nonzero reduced x
// has a complement strictly between zero and the width, and a value
// strictly below the width is its own remainder — so the negation is
// the bare complement, and the complement of a value strictly below
// the width is not zero.
var NegEqZero = negEqZeroThm{family.Add(registry.ProofEntry{
	Name: "NegEqZero",
	Key:  "prop_205a3ec2d428158d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "x = 0 ⇔ 0 = word_neg(n, x)",
	},
		func(a *proof.Argument, n, x proof.Term, below proof.Fact) {
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			nonzero := a.Unless(
				a.Term("x = 0"),
				"x = 0: both sides hold — the left outright, the right by NegZero",
				proof.Given(func(z *proof.Argument, isZero proof.Fact) {
					z.Show(
						"the zero word is its own negation",
						proof.By(isZero, NegZero))
				}))
			xle := a.Have(
				"the bound, weakened to what the monus asks",
				"x ≤ nat_pow(2, n)",
				proof.By(below, nat_order.LessEqOfLessThan))
			rep := a.Have(
				"the complement restores the width",
				"(nat_pow(2, n) - x) + x = nat_pow(2, n)",
				proof.By(xle, nat_monus.SubAddCancel))
			dle := a.Have(
				"so the complement is at most the width",
				"nat_pow(2, n) - x ≤ nat_pow(2, n)",
				proof.By(rep, nat_order.LessEqAdd))
			dBelow := a.Have(
				"and strictly below it — at the width itself x would vanish",
				"nat_pow(2, n) - x < nat_pow(2, n)",
				proof.By(nonzero, rep, dle, nat_order.LessEqSplit, nat_arith.AddEqSelfLeft))
			negIs := a.Have(
				"the negation of a reduced word is the bare complement",
				"word_neg(n, x) = nat_pow(2, n) - x",
				proof.By(wordNegDef, below, dBelow, nat_div_mod.ModLessThan))
			negNonzero := a.Have(
				"which is nonzero while x sits below the width",
				"¬(nat_pow(2, n) - x = 0)",
				proof.By(below, nat_monus.SubEqZero, nat_order.NotLessEq))
			a.Do(proof.By(Normalized, nonzero, negIs, negNonzero))
		}),
})}

// NegNeg — negation is an involution on reduced words. For nonzero x
// both negations are bare complements, and the double complement
// cancels: (2^n − x) + x and (2^n − (2^n − x)) + (2^n − x) both
// restore the width, so the two leftovers agree by cancellation.
var NegNeg = negNegThm{family.Add(registry.ProofEntry{
	Name: "NegNeg",
	Key:  "prop_86fa0a4e7a7f9132",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
		},
		Conclusion: "x = word_neg(n, word_neg(n, x))",
	},
		func(a *proof.Argument, n, x proof.Term, below proof.Fact) {
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			nonzero := a.Unless(
				a.Term("x = 0"),
				"x = 0: negating zero twice is NegZero twice",
				proof.Given(func(z *proof.Argument, isZero proof.Fact) {
					z.Show(
						"both negations collapse on the zero word",
						proof.By(isZero, NegZero))
				}))
			xle := a.Have(
				"the bound, weakened to what the monus asks",
				"x ≤ nat_pow(2, n)",
				proof.By(below, nat_order.LessEqOfLessThan))
			rep := a.Have(
				"the complement restores the width",
				"(nat_pow(2, n) - x) + x = nat_pow(2, n)",
				proof.By(xle, nat_monus.SubAddCancel))
			dle := a.Have(
				"so the complement is at most the width",
				"nat_pow(2, n) - x ≤ nat_pow(2, n)",
				proof.By(rep, nat_order.LessEqAdd))
			dBelow := a.Have(
				"and strictly below it — at the width itself x would vanish",
				"nat_pow(2, n) - x < nat_pow(2, n)",
				proof.By(nonzero, rep, dle, nat_order.LessEqSplit, nat_arith.AddEqSelfLeft))
			negIs := a.Have(
				"the negation of a reduced word is the bare complement",
				"word_neg(n, x) = nat_pow(2, n) - x",
				proof.By(wordNegDef, below, dBelow, nat_div_mod.ModLessThan))
			rep2 := a.Have(
				"the complement's own complement restores the width as well",
				"(nat_pow(2, n) - (nat_pow(2, n) - x)) + (nat_pow(2, n) - x) = nat_pow(2, n)",
				proof.By(dle, nat_monus.SubAddCancel))
			flipped := a.Have(
				"read with the complement first",
				"(nat_pow(2, n) - x) + (nat_pow(2, n) - (nat_pow(2, n) - x)) = nat_pow(2, n)",
				proof.By(rep2, nat_arith.AddSym))
			cancel := a.Have(
				"so taking the complement twice returns x",
				"nat_pow(2, n) - (nat_pow(2, n) - x) = x",
				proof.By(rep, flipped, nat_arith.AddEqLCancel))
			outer := a.Have(
				"the outer negation reads the double complement",
				"word_neg(n, word_neg(n, x)) = rem(nat_pow(2, n) - (nat_pow(2, n) - x), nat_pow(2, n))",
				proof.By(wordNegDef, negIs, dBelow, nat_div_mod.ModLessThan))
			a.Do(proof.By(Normalized, outer, cancel, below, nat_div_mod.ModLessThan))
		}),
})}

// SubEqZero — two reduced words are equal exactly when their
// difference is the zero word: forward is SubRefl; backward, CongSub
// reads a zero difference as equal remainders, and below the width the
// remainder determines the value. The word-face and val-face
// forms of the law both translate to this one statement.
var SubEqZero = subEqZeroThm{family.Add(registry.ProofEntry{
	Name: "SubEqZero",
	Key:  "prop_f15fc60aa692fd99",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x y.",
		Hypotheses: []string{
			"x < nat_pow(2, n)",
			"y < nat_pow(2, n)",
		},
		Conclusion: "x = y ⇔ 0 = word_sub(n, x, y)",
	},
		func(a *proof.Argument, n, x, y proof.Term, xBelow, yBelow proof.Fact) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			forward := a.Have(
				"equal words subtract to the zero word",
				"x = y ⇒ 0 = word_sub(n, x, y)",
				proof.Derive(func(b *proof.Argument) {
					eq := b.Assume()
					b.Do(proof.By(eq, SubRefl))
				}))
			backward := a.Have(
				"a zero difference forces equality",
				"0 = word_sub(n, x, y) ⇒ x = y",
				proof.Derive(func(b *proof.Argument) {
					vanishes := b.Assume()
					sameRem := b.Have(
						"both words leave the same remainder",
						"rem(y, nat_pow(2, n)) = rem(x, nat_pow(2, n))",
						proof.By(vanishes, proof.At(CongSub, n, x, y), natCongDef, nat_arith.AddLeftZeroClause))
					b.Do(proof.By(xBelow, yBelow, sameRem, nat_div_mod.ModInjectiveBelow))
				}))
			a.Do(proof.By(Normalized, forward, backward))
		}),
})}

// NegSub — negating a difference reverses it, for every input. Both
// sides are single reductions, hence below the width; and both are
// congruent to the same residue — appending the cancelling pair
// (x − y) + (y − x), itself a sum of the two negation blocks, carries
// one side onto the other. Below the width, congruent means equal.
var NegSub = negSubThm{family.Add(registry.ProofEntry{
	Name: "NegSub",
	Key:  "prop_7b1fdb103f6c7b6a",
	Build: family.Theorem("∀n x y:num. word_neg(n, word_sub(n, x, y)) = word_sub(n, y, x)",
		func(a *proof.Argument, n, x, y proof.Term) {
			natCongDef := a.Ctx().ConstDefNormalized("nat_cong")
			wordNegDef := a.Ctx().ConstDefNormalized("word_neg")
			wordSubDef := a.Ctx().ConstDefNormalized("word_sub")
			wordAddDef := a.Ctx().ConstDefNormalized("word_add")
			lhsBelow := a.Have(
				"the negated difference is a reduction, hence below the width",
				"word_neg(n, word_sub(n, x, y)) < nat_pow(2, n)",
				proof.By(proof.At(nat_arith.PowTwoNonzero, n), wordNegDef, nat_div_mod.Division))
			rhsBelow := a.Have(
				"and so is the reversed difference",
				"word_sub(n, y, x) < nat_pow(2, n)",
				proof.By(proof.At(nat_arith.PowTwoNonzero, n), wordSubDef, wordAddDef, nat_div_mod.Division))
			negX := a.Have(
				"x's negation block reduces to zero",
				"rem(word_neg(n, x) + x, nat_pow(2, n)) = 0",
				proof.By(CongNeg, natCongDef, nat_div_mod.ZeroMod))
			negY := a.Have(
				"and y's",
				"rem(word_neg(n, y) + y, nat_pow(2, n)) = 0",
				proof.By(CongNeg, natCongDef, nat_div_mod.ZeroMod))
			subBlock := a.Have(
				"the difference is a word like any other: its negation block reduces too",
				"rem(word_neg(n, word_sub(n, x, y)) + word_sub(n, x, y), nat_pow(2, n)) = 0",
				proof.By(CongNeg, natCongDef, nat_div_mod.ZeroMod))
			rawXY := a.Have(
				"one difference, written raw",
				"word_sub(n, x, y) = rem(x + word_neg(n, y), nat_pow(2, n))",
				proof.By(wordSubDef, wordAddDef))
			rawYX := a.Have(
				"and the other",
				"word_sub(n, y, x) = rem(y + word_neg(n, x), nat_pow(2, n))",
				proof.By(wordSubDef, wordAddDef))
			raw := a.Have(
				"the two opposite differences, unfolded into one raw sum",
				"rem(word_sub(n, x, y) + word_sub(n, y, x), nat_pow(2, n)) = "+
					"rem((x + word_neg(n, y)) + (y + word_neg(n, x)), nat_pow(2, n))",
				proof.By(rawXY, rawYX, nat_div_mod.ModAddMod))
			regrouped := a.Have(
				"whose summands regroup into the two negation blocks",
				"(x + word_neg(n, y)) + (y + word_neg(n, x)) = (word_neg(n, x) + x) + (word_neg(n, y) + y)",
				// The ac solver composes the permutation out of the
				// deriver's two certificates by kernel steps, so this leaf
				// carries no refutation and a mis-stated regrouping fails
				// with both leaf lists printed rather than as a refute
				// that quietly does not close.
				proof.ACRegroupWith(nat_arith.AddAC(a.Ctx())))
			blocks := a.Have(
				"two zero blocks reduce to zero together",
				"rem((word_neg(n, x) + x) + (word_neg(n, y) + y), nat_pow(2, n)) = 0",
				proof.By(negX, negY, nat_div_mod.ModAddMod, nat_arith.AddZero, nat_div_mod.ZeroMod))
			cancelling := a.Have(
				"so the two opposite differences cancel modulo the width",
				"rem(word_sub(n, x, y) + word_sub(n, y, x), nat_pow(2, n)) = 0",
				proof.By(raw, regrouped, blocks))
			viaRight := a.Have(
				"append the cancelling pair: the negated difference survives",
				"rem(word_neg(n, word_sub(n, x, y)), nat_pow(2, n)) = "+
					"rem(word_neg(n, word_sub(n, x, y)) + (word_sub(n, x, y) + word_sub(n, y, x)), nat_pow(2, n))",
				proof.By(cancelling, nat_div_mod.ModAddModRight, nat_arith.AddZero))
			viaLeft := a.Have(
				"group the same sum the other way: the reversed difference survives",
				"rem(word_sub(n, y, x), nat_pow(2, n)) = "+
					"rem((word_neg(n, word_sub(n, x, y)) + word_sub(n, x, y)) + word_sub(n, y, x), nat_pow(2, n))",
				proof.By(subBlock, nat_div_mod.ModAddModLeft, nat_arith.AddLeftZeroClause))
			sameRem := a.Have(
				"both sides leave the same remainder",
				"rem(word_neg(n, word_sub(n, x, y)), nat_pow(2, n)) = rem(word_sub(n, y, x), nat_pow(2, n))",
				proof.By(viaRight, viaLeft, nat_arith.AddAssoc))
			a.Do(proof.By(lhsBelow, rhsBelow, sameRem, nat_div_mod.ModInjectiveBelow))
		}),
})}

// ---------------------------------------------------------------------------
// The quantifier transports of the bridge
// ---------------------------------------------------------------------------
//
// A claim about every word is a claim about every value in range, and
// a witness among words is a witness among values in range. The predicate binder P ranges over ALL predicates
// on num — these are the strong forms that carry whole statements across
// the val/word boundary at once.
//
// Both ride the same two facts, in the two directions' natural split:
// toward the range, a reduction below the width is the identity
// (nat_div_mod.ModLessThan) — the equality that carries P between a
// value and its reduction by congruence; toward the words, every
// reduction lands in range (Division's bound, live because a power of
// two is never zero).
//
// (A third transport — the disjunctive spelling
// `∀n. P(n) ∨ ¬(n < 2^n')` against the guarded one — has no member
// here: an implication IS a canonical disjunction to the engine's
// normalizer, so the two spellings are one statement and the
// biconditional normalizes to ⊤. There is nothing to prove.)

// ForallWord — a claim about every word is a claim about every value
// in range. Toward the range, the reduction of a value already in
// range is the value itself, and P travels along that equality by
// congruence; toward the words, every reduction lands in range, where
// the guarded claim already speaks.
var ForallWord = forallWordThm{family.Add(registry.ProofEntry{
	Name: "ForallWord",
	Key:  "prop_732542bee152fcab",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n':num. ∀P:(num → bool).",
			Conclusion: "(∀n:num. P(rem(n, nat_pow(2, n')))) ⇔ ∀x:num. x < nat_pow(2, n') ⇒ P(x)",
		},
		func(a *Argument, np, P Term) {
			width := a.Term("nat_pow(2, n')")
			forward := a.Have(
				"P at every word reaches every value in range — its own reduction",
				"(∀n:num. P(rem(n, nat_pow(2, n')))) ⇒ ∀x:num. x < nat_pow(2, n') ⇒ P(x)",
				Derive(func(b *Argument) {
					wordwise := b.Assume()
					x := b.Fix()
					inRange := b.Assume()
					collapse := b.Have(
						"below the width the reduction is the identity",
						"rem(x, nat_pow(2, n')) = x",
						By(inRange, At(nat_div_mod.ModLessThan, x, width)))
					b.Do(By(Normalized, wordwise.At(x), collapse))
				}))
			backward := a.Have(
				"and P on the range reaches every word — reductions land in range",
				"(∀x:num. x < nat_pow(2, n') ⇒ P(x)) ⇒ ∀n:num. P(rem(n, nat_pow(2, n')))",
				Derive(func(b *Argument) {
					guarded := b.Assume()
					n := b.Fix()
					landed := b.Have(
						"the reduction lands below the width — a power of two is never zero",
						"rem(n, nat_pow(2, n')) < nat_pow(2, n')",
						By(At(nat_arith.PowTwoNonzero, np), At(nat_div_mod.Division, n, width)))
					b.Do(By(guarded.At(b.Term("rem(n, nat_pow(2, n'))")), landed))
				}))
			a.Do(By(forward, backward))
		}),
})}

// ExistsWord — the ∃ mirror: some word satisfies P exactly when some
// value in range does. Toward the range the witness is the word's own
// reduction — in range by Division's bound, carrying P directly;
// toward the words the in-range witness is its own reduction, and P
// travels along that equality by congruence.
var ExistsWord = existsWordThm{family.Add(registry.ProofEntry{
	Name: "ExistsWord",
	Key:  "prop_dd58fd2aeefaadef",
	Build: family.Theorem(
		Statement{
			Binders:    "∀n':num. ∀P:(num → bool).",
			Conclusion: "(∃n:num. P(rem(n, nat_pow(2, n')))) ⇔ ∃x:num. x < nat_pow(2, n') ∧ P(x)",
		},
		func(a *Argument, np, P Term) {
			width := a.Term("nat_pow(2, n')")
			forward := a.Have(
				"a word satisfying P hands over its reduction",
				"(∃n:num. P(rem(n, nat_pow(2, n')))) ⇒ ∃x:num. x < nat_pow(2, n') ∧ P(x)",
				Derive(func(b *Argument) {
					someWord := b.Assume()
					_, pAtWord := b.Unpack(someWord)
					landed := b.Have(
						"its reduction lands below the width — a power of two is never zero",
						"rem(n, nat_pow(2, n')) < nat_pow(2, n')",
						By(At(nat_arith.PowTwoNonzero, np), At(nat_div_mod.Division, b.Term("n"), width)))
					b.Take(b.Term("rem(n, nat_pow(2, n'))"))
					b.Do(By(landed, pAtWord))
				}))
			backward := a.Have(
				"and an in-range witness is its own reduction — a word already",
				"(∃x:num. x < nat_pow(2, n') ∧ P(x)) ⇒ ∃n:num. P(rem(n, nat_pow(2, n')))",
				Derive(func(b *Argument) {
					someValue := b.Assume()
					_, both := b.Unpack(someValue)
					collapse := b.Have(
						"below the width the reduction is the identity",
						"rem(x, nat_pow(2, n')) = x",
						By(both, At(nat_div_mod.ModLessThan, b.Term("x"), width)))
					b.Take(b.Term("x"))
					b.Do(By(Normalized, both, collapse))
				}))
			a.Do(By(forward, backward))
		}),
})}
