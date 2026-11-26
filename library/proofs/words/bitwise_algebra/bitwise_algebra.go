// bitwise_algebra.go — the pointwise boolean algebra of the term-level word:
// the equational laws of word_and/word_or/word_xor/word_not — symmetry, associativity,
// units and idempotents, De Morgan, the all-ones mask against the two
// algebras, the complement laws, and the difference as an equality
// test. The reading face that these laws project through lives in
// words/word_bits; the algebra-against-arithmetic interface in
// words/bit_arith.

package bitwise_algebra

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/words/word_bits"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The pointwise algebra of AND and OR
// ---------------------------------------------------------------------------
//
// The width-free projections in words/word_bits read each conjunction or
// disjunction as the corresponding operation on bits. BitsEqAll turns
// pointwise agreement into an equation of values. The paired zero and
// all-ones-mask laws establish one operand order by bits and obtain the
// other by symmetry. Complement laws keep the width of word_not; a
// bound on a bare operand clears its bits beyond that width.

// ---------------------------------------------------------------------------
// The AND laws — bits through the projection, BitsEqAll back to values
// ---------------------------------------------------------------------------

// AndSym — the conjunction commutes: the strong form.
// Both sides' tables are the same conjunction of bits, read in either
// order.
var AndSym = andSymThm{family.Add(registry.ProofEntry{
	Name: "AndSym",
	Key:  "prop_d1f6316aa4421a37",
	Build: family.Theorem(
		"∀x y:num. word_and(x, y) = word_and(y, x)",
		func(a *Argument, x, y Term) {
			lhsBits := a.Have(
				"the left side's bits, through the projection",
				"∀k:num. word_bit(k, word_and(x, y)) ⇔ (word_bit(k, x) ∧ word_bit(k, y))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitOfAnd))
				}))
			rhsBits := a.Have(
				"and the right side's",
				"∀k:num. word_bit(k, word_and(y, x)) ⇔ (word_bit(k, y) ∧ word_bit(k, x))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfAnd))
				}))
			a.Show(
				"a conjunction read in either order is the same table — extensionality equates the values",
				// Grounded: bare, the cite's free value pair unifies
				// against every bit literal in scope and the search
				// outgrows the budget.
				By(
					Normalized,
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll, a.Term("word_and(x, y)"), a.Term("word_and(y, x)"))))
		}),
})}

// AndAssoc — the conjunction associates: the strong
// form. Both tables flatten to the same three-bit conjunction.
var AndAssoc = andAssocThm{family.Add(registry.ProofEntry{
	Name: "AndAssoc",
	Key:  "prop_ca0c1d25ae95b0df",
	Build: family.Theorem(
		"∀x y z:num. word_and(x, word_and(y, z)) = word_and(word_and(x, y), z)",
		func(a *Argument, x, y, z Term) {
			lhsBits := a.Have(
				"the left side's bits — the inner conjunction first, then the outer",
				"∀k:num. "+
					"    word_bit(k, word_and(x, word_and(y, z))) ⇔ "+
					"    ((word_bit(k, x) ∧ word_bit(k, y)) ∧ word_bit(k, z))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claims below
					inner := b.Have(
						"the inner conjunction's bit",
						"word_bit(k, word_and(y, z)) ⇔ (word_bit(k, y) ∧ word_bit(k, z))",
						By(word_bits.BitOfAnd))
					b.Do(By(Normalized, inner, word_bits.BitOfAnd))
				}))
			rhsBits := a.Have(
				"and the right side's, to the same flat table",
				"∀k:num. "+
					"    word_bit(k, word_and(word_and(x, y), z)) ⇔ "+
					"    ((word_bit(k, x) ∧ word_bit(k, y)) ∧ word_bit(k, z))",
				Derive(func(b *Argument) {
					b.Fix()
					inner := b.Have(
						"the inner conjunction's bit",
						"word_bit(k, word_and(x, y)) ⇔ (word_bit(k, x) ∧ word_bit(k, y))",
						By(word_bits.BitOfAnd))
					b.Do(By(inner, word_bits.BitOfAnd))
				}))
			a.Show(
				"one table under two bracketings — extensionality equates the values",
				// Grounded, as AndSym's.
				By(
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll,
						a.Term("word_and(x, word_and(y, z))"), a.Term("word_and(word_and(x, y), z)"))))
		}),
})}

// AndRefl — the conjunction is idempotent: the strong
// form, oriented as the twin states it. One side is the bare x, so one
// pointwise Have suffices: a bit conjoined with itself is itself.
var AndRefl = andReflThm{family.Add(registry.ProofEntry{
	Name: "AndRefl",
	Key:  "prop_212305a1bd7aca74",
	Build: family.Theorem(
		"∀x:num. x = word_and(x, x)",
		func(a *Argument, x Term) {
			rhsBits := a.Have(
				"the conjunction's bits at equal operands",
				"∀k:num. word_bit(k, word_and(x, x)) ⇔ (word_bit(k, x) ∧ word_bit(k, x))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitOfAnd))
				}))
			a.Show(
				"a table conjoined with itself is itself — extensionality equates the values",
				// Grounded, as AndSym's.
				By(Normalized, rhsBits, At(word_bits.BitsEqAll, x, a.Term("word_and(x, x)"))))
		}),
})}

// AndZero — zero absorbs the conjunction. The zero word has no bits,
// so the right-zero conjunction is zero; symmetry gives the other order.
var AndZero = andZeroThm{family.Add(registry.ProofEntry{
	Name: "AndZero",
	Key:  "prop_9677a889e99e11eb",
	Build: family.Theorem(
		"∀x:num. (0 = word_and(x, 0)) ∧ (0 = word_and(0, x))",
		func(a *Argument, x *Expr[Nat]) {
			zero := a.TermAs[Nat]("0")
			zeroBits := a.Have(
				"the zero word has no bits",
				"∀k:num. ¬word_bit(k, 0)",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitWordZero))
				}))
			leftBits := a.Have(
				"the right-zero conjunction's bits",
				"∀k:num. word_bit(k, word_and(x, 0)) ⇔ (word_bit(k, x) ∧ word_bit(k, 0))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfAnd))
				}))
			left := a.Have(
				"nothing survives a zero operand",
				"0 = word_and(x, 0)",
				// Grounded, as AndSym's.
				By(Normalized, zeroBits, leftBits, At(word_bits.BitsEqAll, zero, a.Term("word_and(x, 0)"))))
			a.Show(
				"zero absorbs from either side",
				By(Normalized, left, AndSym.At(x, zero)))
		}),
})}

// ---------------------------------------------------------------------------
// The OR laws — the disjunctive mirrors
// ---------------------------------------------------------------------------

// OrSym — the disjunction commutes: the strong form.
var OrSym = orSymThm{family.Add(registry.ProofEntry{
	Name: "OrSym",
	Key:  "prop_369cbfd80547ec7",
	Build: family.Theorem(
		"∀x y:num. word_or(x, y) = word_or(y, x)",
		func(a *Argument, x, y Term) {
			lhsBits := a.Have(
				"the left side's bits, through the projection",
				"∀k:num. word_bit(k, word_or(x, y)) ⇔ (word_bit(k, x) ∨ word_bit(k, y))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitOfOr))
				}))
			rhsBits := a.Have(
				"and the right side's",
				"∀k:num. word_bit(k, word_or(y, x)) ⇔ (word_bit(k, y) ∨ word_bit(k, x))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfOr))
				}))
			a.Show(
				"a disjunction read in either order is the same table — extensionality equates the values",
				// Grounded, as AndSym's.
				By(
					Normalized,
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll, a.Term("word_or(x, y)"), a.Term("word_or(y, x)"))))
		}),
})}

// OrAssoc — the disjunction associates: the strong
// form. AndAssoc's mirror.
var OrAssoc = orAssocThm{family.Add(registry.ProofEntry{
	Name: "OrAssoc",
	Key:  "prop_90c7d16eb458508d",
	Build: family.Theorem(
		"∀x y z:num. word_or(x, word_or(y, z)) = word_or(word_or(x, y), z)",
		func(a *Argument, x, y, z Term) {
			lhsBits := a.Have(
				"the left side's bits — the inner disjunction first, then the outer",
				"∀k:num. "+
					"    word_bit(k, word_or(x, word_or(y, z))) ⇔ ((word_bit(k, x) ∨ word_bit(k, y)) ∨ word_bit(k, z))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claims below
					inner := b.Have(
						"the inner disjunction's bit",
						"word_bit(k, word_or(y, z)) ⇔ (word_bit(k, y) ∨ word_bit(k, z))",
						By(word_bits.BitOfOr))
					b.Do(By(Normalized, inner, word_bits.BitOfOr))
				}))
			rhsBits := a.Have(
				"and the right side's, to the same flat table",
				"∀k:num. "+
					"    word_bit(k, word_or(word_or(x, y), z)) ⇔ ((word_bit(k, x) ∨ word_bit(k, y)) ∨ word_bit(k, z))",
				Derive(func(b *Argument) {
					b.Fix()
					inner := b.Have(
						"the inner disjunction's bit",
						"word_bit(k, word_or(x, y)) ⇔ (word_bit(k, x) ∨ word_bit(k, y))",
						By(word_bits.BitOfOr))
					b.Do(By(inner, word_bits.BitOfOr))
				}))
			a.Show(
				"one table under two bracketings — extensionality equates the values",
				// Grounded, as AndSym's.
				By(
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll,
						a.Term("word_or(x, word_or(y, z))"), a.Term("word_or(word_or(x, y), z)"))))
		}),
})}

// OrRefl — the disjunction is idempotent: the strong
// form, oriented as the twin states it.
var OrRefl = orReflThm{family.Add(registry.ProofEntry{
	Name: "OrRefl",
	Key:  "prop_9b7e69cf9d31345e",
	Build: family.Theorem(
		"∀x:num. x = word_or(x, x)",
		func(a *Argument, x Term) {
			rhsBits := a.Have(
				"the disjunction's bits at equal operands",
				"∀k:num. word_bit(k, word_or(x, x)) ⇔ (word_bit(k, x) ∨ word_bit(k, x))",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitOfOr))
				}))
			a.Show(
				"a table disjoined with itself is itself — extensionality equates the values",
				// Grounded, as AndSym's.
				By(Normalized, rhsBits, At(word_bits.BitsEqAll, x, a.Term("word_or(x, x)"))))
		}),
})}

// OrZero — zero is the disjunction's unit. The zero word contributes
// no bits on the right; symmetry gives the other order.
var OrZero = orZeroThm{family.Add(registry.ProofEntry{
	Name: "OrZero",
	Key:  "prop_bc65ca0cb4d01e17",
	Build: family.Theorem(
		"∀x:num. (x = word_or(x, 0)) ∧ (x = word_or(0, x))",
		func(a *Argument, x *Expr[Nat]) {
			zeroBits := a.Have(
				"the zero word has no bits",
				"∀k:num. ¬word_bit(k, 0)",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitWordZero))
				}))
			leftBits := a.Have(
				"the right-zero disjunction's bits",
				"∀k:num. word_bit(k, word_or(x, 0)) ⇔ (word_bit(k, x) ∨ word_bit(k, 0))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfOr))
				}))
			left := a.Have(
				"a zero operand contributes nothing",
				"x = word_or(x, 0)",
				// Grounded, as AndSym's.
				By(Normalized, zeroBits, leftBits, At(word_bits.BitsEqAll, x, a.Term("word_or(x, 0)"))))
			a.Show(
				"zero is a unit on either side",
				By(Normalized, left, OrSym.At(x, a.TermAs[Nat]("0"))))
		}),
})}

// OrEqZero — a disjunction vanishes exactly when both operands do.
// Forward, a vanished disjunction clears both operands' bits and
// extensionality zeroes each; backward is the unit law at zero and
// congruence.
var OrEqZero = orEqZeroThm{family.Add(registry.ProofEntry{
	Name: "OrEqZero",
	Key:  "prop_e74916680588e37b",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x y:num.",
			Conclusion: "0 = word_or(x, y) ⇔ x = 0 ∧ y = 0",
		},
		func(a *Argument, x, y Term) {
			zero := a.Ctx().Numeral(0)
			zeroBits := a.Have(
				"the zero word has no bits",
				"∀k:num. ¬word_bit(k, 0)",
				Derive(func(b *Argument) {
					b.Fix() // k — spelled in the claim
					b.Do(By(word_bits.BitWordZero))
				}))
			orBits := a.Have(
				"a bit of the disjunction is the disjunction of bits",
				"∀k:num. word_bit(k, word_or(x, y)) ⇔ (word_bit(k, x) ∨ word_bit(k, y))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfOr))
				}))
			forward := a.Have(
				"a vanished disjunction clears both operands, bit by bit",
				"(0 = word_or(x, y)) ⇒ ((x = 0) ∧ (y = 0))",
				Derive(func(b *Argument) {
					vanished := b.Assume()
					xAgree := b.Have(
						"x's table is the zero word's",
						"∀k:num. word_bit(k, x) ⇔ word_bit(k, 0)",
						Derive(func(c *Argument) {
							c.Fix()
							c.Do(By(Normalized, vanished, orBits, zeroBits))
						}))
					yAgree := b.Have(
						"and y's",
						"∀k:num. word_bit(k, y) ⇔ word_bit(k, 0)",
						Derive(func(c *Argument) {
							c.Fix()
							c.Do(By(Normalized, vanished, orBits, zeroBits))
						}))
					xZero := b.Have(
						"so x is zero",
						"x = 0",
						// Grounded, as AndSym's.
						By(xAgree, At(word_bits.BitsEqAll, x, zero)))
					yZero := b.Have(
						"and y",
						"y = 0",
						By(yAgree, At(word_bits.BitsEqAll, y, zero)))
					b.Do(By(xZero, yZero))
				}))
			backward := a.Have(
				"and zero operands vanish the disjunction — the unit law read at zero, then congruence",
				"((x = 0) ∧ (y = 0)) ⇒ (0 = word_or(x, y))",
				Derive(func(b *Argument) {
					both := b.Assume()
					b.Do(By(both, OrZero))
				}))
			a.Show(
				"a disjunction vanishes exactly when both operands do",
				By(Normalized, forward, backward))
		}),
})}

// ---------------------------------------------------------------------------
// De Morgan — the complement swaps the two algebras
// ---------------------------------------------------------------------------

// NotAnd — complementing a conjunction disjoins the complements.
// Both bit tables say not-both below the shared width; the width guard
// factors out of the disjunction of complemented bits.
var NotAnd = notAndThm{family.Add(registry.ProofEntry{
	Name: "NotAnd",
	Key:  "prop_6d9bfd221b3596a5",
	Build: family.Theorem(
		"∀n x y:num. word_not(n, word_and(x, y)) = word_or(word_not(n, x), word_not(n, y))",
		func(a *Argument, n, x, y *Expr[Nat]) {
			lhsBits := a.Have(
				"a bit of the complemented conjunction: not-both, inside the width",
				"∀k:num. word_bit(k, word_not(n, word_and(x, y))) ⇔ (¬(word_bit(k, x) ∧ word_bit(k, y)) ∧ (k < n))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitOfAnd.At(x, y, k),
						word_bits.BitNot.At(n, b.TermAs[Nat]("word_and(x, y)"), k)))
				}))
			rhsBits := a.Have(
				"a bit of the disjoined complements: the same table — "+
					"the shared width guard factors out of the disjunction",
				"∀k:num. "+
					"    word_bit(k, word_or(word_not(n, x), word_not(n, y))) ⇔ "+
					"    (¬(word_bit(k, x) ∧ word_bit(k, y)) ∧ (k < n))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						word_bits.BitNot.At(n, x, k),
						word_bits.BitNot.At(n, y, k),
						word_bits.BitOfOr.At(b.TermAs[Nat]("word_not(n, x)"), b.TermAs[Nat]("word_not(n, y)"), k)))
				}))
			a.Show(
				"one table on both sides — De Morgan is extensionality at the bits",
				By(
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll,
						a.Term("word_not(n, word_and(x, y))"),
						a.Term("word_or(word_not(n, x), word_not(n, y))"))))
		}),
})}

// NotOr — complementing a disjunction conjoins the complements.
// At each position below the shared width, both tables say neither
// operand's bit is set. The width guard factors out of the conjunction.
var NotOr = notOrThm{family.Add(registry.ProofEntry{
	Name: "NotOr",
	Key:  "prop_9ebe05b692870220",
	Build: family.Theorem(
		"∀n x y:num. word_not(n, word_or(x, y)) = word_and(word_not(n, x), word_not(n, y))",
		func(a *Argument, n, x, y *Expr[Nat]) {
			lhsBits := a.Have(
				"a bit of the complemented disjunction: neither, inside the width",
				"∀k:num. word_bit(k, word_not(n, word_or(x, y))) ⇔ (¬(word_bit(k, x) ∨ word_bit(k, y)) ∧ (k < n))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitOfOr.At(x, y, k),
						word_bits.BitNot.At(n, b.TermAs[Nat]("word_or(x, y)"), k)))
				}))
			rhsBits := a.Have(
				"a bit of the conjoined complements: the same table — "+
					"the shared width guard factors out of the conjunction",
				"∀k:num. "+
					"    word_bit(k, word_and(word_not(n, x), word_not(n, y))) ⇔ "+
					"    (¬(word_bit(k, x) ∨ word_bit(k, y)) ∧ (k < n))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						word_bits.BitNot.At(n, x, k),
						word_bits.BitNot.At(n, y, k),
						word_bits.BitOfAnd.At(b.TermAs[Nat]("word_not(n, x)"), b.TermAs[Nat]("word_not(n, y)"), k)))
				}))
			a.Show(
				"one table on both sides — De Morgan is extensionality at the bits",
				By(
					lhsBits,
					rhsBits,
					At(word_bits.BitsEqAll,
						a.Term("word_not(n, word_or(x, y))"),
						a.Term("word_and(word_not(n, x), word_not(n, y))"))))
		}),
})}

// ---------------------------------------------------------------------------
// The all-ones mask — word_not(n, 0) against the two algebras
// ---------------------------------------------------------------------------

// AndNotZero — the all-ones mask is the conjunction's unit on the
// width's words. Its bits occupy exactly the positions below the width,
// which contain every set bit of x by the range guard. Masking on the
// right changes no bit; symmetry gives the other order.
var AndNotZero = andNotZeroThm{family.Add(registry.ProofEntry{
	Name: "AndNotZero",
	Key:  "prop_58fba925f2344a2b",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "x = word_and(x, word_not(n, 0)) ∧ x = word_and(word_not(n, 0), x)",
		},
		func(a *Argument, n, x *Expr[Nat], xBound Fact) {
			maskBits := a.Have(
				"the all-ones mask has exactly the width's positions",
				"∀k:num. word_bit(k, word_not(n, 0)) ⇔ (k < n)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(word_bits.BitNot.At(n, b.TermAs[Nat]("0"), k), word_bits.BitWordZero))
				}))
			guardX := a.Have(
				"and a set bit of x sits below the width",
				"∀k:num. word_bit(k, x) ⇒ (k < n)",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(xBound, word_bits.BitBelowBound))
				}))
			leftBits := a.Have(
				"the conjunction's bits against the mask",
				"∀k:num. word_bit(k, word_and(x, word_not(n, 0))) ⇔ (word_bit(k, x) ∧ word_bit(k, word_not(n, 0)))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfAnd))
				}))
			left := a.Have(
				"masking with all-ones changes no bit",
				"x = word_and(x, word_not(n, 0))",
				By(maskBits, guardX, leftBits, At(word_bits.BitsEqAll, x, a.Term("word_and(x, word_not(n, 0))"))))
			a.Show(
				"the mask is a unit on either side",
				By(Normalized, left, AndSym.At(x, a.TermAs[Nat]("word_not(n, 0)"))))
		}),
})}

// OrNotZero — the all-ones mask absorbs the disjunction on the width's
// words. The mask holds every position a bounded x could contribute,
// so disjoining x on the left changes no bit; symmetry gives the other
// order.
var OrNotZero = orNotZeroThm{family.Add(registry.ProofEntry{
	Name: "OrNotZero",
	Key:  "prop_444a32836309d4cc",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_not(n, 0) = word_or(x, word_not(n, 0)) ∧ " +
				"word_not(n, 0) = word_or(word_not(n, 0), x)",
		},
		func(a *Argument, n, x *Expr[Nat], xBound Fact) {
			maskBits := a.Have(
				"the all-ones mask has exactly the width's positions",
				"∀k:num. word_bit(k, word_not(n, 0)) ⇔ (k < n)",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(word_bits.BitNot.At(n, b.TermAs[Nat]("0"), k), word_bits.BitWordZero))
				}))
			guardX := a.Have(
				"and a set bit of x sits below the width",
				"∀k:num. word_bit(k, x) ⇒ (k < n)",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(xBound, word_bits.BitBelowBound))
				}))
			leftBits := a.Have(
				"the disjunction's bits against the mask",
				"∀k:num. word_bit(k, word_or(x, word_not(n, 0))) ⇔ (word_bit(k, x) ∨ word_bit(k, word_not(n, 0)))",
				Derive(func(b *Argument) {
					b.Fix()
					b.Do(By(word_bits.BitOfOr))
				}))
			left := a.Have(
				"every bit x could add is already the mask's",
				"word_not(n, 0) = word_or(x, word_not(n, 0))",
				By(
					maskBits,
					guardX,
					leftBits,
					At(word_bits.BitsEqAll, a.Term("word_not(n, 0)"), a.Term("word_or(x, word_not(n, 0))"))))
			a.Show(
				"the mask absorbs on either side",
				By(Normalized, left, OrSym.At(x, a.TermAs[Nat]("word_not(n, 0)"))))
		}),
})}

// ---------------------------------------------------------------------------
// The pointwise algebra of XOR and NOT
// ---------------------------------------------------------------------------
//
// BitOfXor reads a difference as disagreement of the operand bits.
// BitNot reads a complement as negation below its width and false
// beyond it. The width-free xor laws follow from boolean identities;
// the complement laws use range bounds to clear bare operands' high
// bits. BitsEqAll returns the resulting pointwise agreements to values.

// ---------------------------------------------------------------------------
// XorSym · XorAssoc · XorZero · XorRefl — the strong xor laws
// ---------------------------------------------------------------------------

// XorSym — the difference commutes, at every pair of values:
// the strong form. Disagreement does not care which side
// disagrees; BitsEqAll does the rest.
var XorSym = xorSymThm{family.Add(registry.ProofEntry{
	Name: "XorSym",
	Key:  "prop_2413d6dc95838319",
	Build: family.Theorem(
		"∀x y:num. word_xor(x, y) = word_xor(y, x)",
		func(a *Argument, x, y Term) {
			agree := a.Have(
				"position by position, both sides read the same disagreement of operand bits",
				"∀i:num. word_bit(i, word_xor(x, y)) ⇔ word_bit(i, word_xor(y, x))",
				Derive(func(b *Argument) {
					b.Fix() // i — spelled in the claims below
					lhsRead := b.Have(
						"one side's bit is the operands' disagreement",
						"word_bit(i, word_xor(x, y)) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, y))",
						By(word_bits.BitOfXor))
					rhsRead := b.Have(
						"and the other's, the same disagreement read backwards",
						"word_bit(i, word_xor(y, x)) ⇔ ¬(word_bit(i, y) ⇔ word_bit(i, x))",
						By(word_bits.BitOfXor))
					b.Do(By(Normalized, lhsRead, rhsRead))
				}))
			a.Show(
				"agreeing everywhere, the two differences are equal",
				By(agree, word_bits.BitsEqAll))
		}),
})}

// XorAssoc — the difference associates, at every triple of values:
// the strong form. Each side's bit reads down to the
// three operand bits through BitOfXor twice, and parity of
// disagreement is associative on the truth table.
var XorAssoc = xorAssocThm{family.Add(registry.ProofEntry{
	Name: "XorAssoc",
	Key:  "prop_d6e15f12f35b887d",
	Build: family.Theorem(
		"∀x y z:num. word_xor(x, word_xor(y, z)) = word_xor(word_xor(x, y), z)",
		func(a *Argument, x, y, z Term) {
			agree := a.Have(
				"position by position, both groupings read the same "+
					"parity of disagreement among the three operand bits",
				"∀i:num. word_bit(i, word_xor(x, word_xor(y, z))) ⇔ word_bit(i, word_xor(word_xor(x, y), z))",
				Derive(func(b *Argument) {
					b.Fix() // i — spelled in the claims below
					outerLeft := b.Have(
						"the left grouping disagrees x with the inner difference",
						"word_bit(i, word_xor(x, word_xor(y, z))) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, word_xor(y, z)))",
						By(word_bits.BitOfXor))
					innerLeft := b.Have(
						"whose bit is y's disagreement with z's",
						"word_bit(i, word_xor(y, z)) ⇔ ¬(word_bit(i, y) ⇔ word_bit(i, z))",
						By(word_bits.BitOfXor))
					outerRight := b.Have(
						"the right grouping disagrees the inner difference with z",
						"word_bit(i, word_xor(word_xor(x, y), z)) ⇔ ¬(word_bit(i, word_xor(x, y)) ⇔ word_bit(i, z))",
						By(word_bits.BitOfXor))
					innerRight := b.Have(
						"whose bit is x's disagreement with y's",
						"word_bit(i, word_xor(x, y)) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, y))",
						By(word_bits.BitOfXor))
					b.Do(By(Normalized, outerLeft, innerLeft, outerRight, innerRight))
				}))
			a.Show(
				"agreeing everywhere, the two groupings are equal",
				By(
					agree,
					At(word_bits.BitsEqAll,
						a.Term("word_xor(x, word_xor(y, z))"),
						a.Term("word_xor(word_xor(x, y), z)"))))
		}),
})}

// XorZero — zero is the unit of the difference. With no set bits to
// disagree with, the right-zero difference has x's bits; symmetry gives
// the other order.
var XorZero = xorZeroThm{family.Add(registry.ProofEntry{
	Name: "XorZero",
	Key:  "prop_7193429252ec6977",
	Build: family.Theorem(
		"∀x:num. (x = word_xor(x, 0)) ∧ (x = word_xor(0, x))",
		func(a *Argument, x *Expr[Nat]) {
			zeroBits := a.Have(
				"the zero word has no bits",
				"∀i:num. ¬word_bit(i, 0)",
				Derive(func(b *Argument) {
					b.Fix() // i — spelled in the claim
					b.Do(By(word_bits.BitWordZero))
				}))
			agreeRight := a.Have(
				"with nothing to disagree with on the right, each bit of the difference is x's own",
				"∀i:num. word_bit(i, x) ⇔ word_bit(i, word_xor(x, 0))",
				Derive(func(b *Argument) {
					i := b.Fix()
					read := b.Have(
						"the difference's bit disagrees x with the zero word",
						"word_bit(i, word_xor(x, 0)) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, 0))",
						By(word_bits.BitOfXor))
					b.Do(By(Normalized, read, zeroBits.At(i)))
				}))
			eqRight := a.Have(
				"agreeing everywhere, the right unit law",
				"x = word_xor(x, 0)",
				By(agreeRight, word_bits.BitsEqAll))
			a.Show(
				"both units together",
				By(Normalized, eqRight, XorSym.At(x, a.TermAs[Nat]("0"))))
		}),
})}

// XorRefl — every value is its own inverse under the difference:
// the strong form. A value never disagrees with
// itself, and a word with no bits is the zero word.
var XorRefl = xorReflThm{family.Add(registry.ProofEntry{
	Name: "XorRefl",
	Key:  "prop_e886f5eeac95f61",
	Build: family.Theorem(
		"∀x:num. 0 = word_xor(x, x)",
		func(a *Argument, x Term) {
			zeroBits := a.Have(
				"the zero word has no bits — at whatever width; one covers itself",
				"∀i:num. ¬word_bit(i, 0)",
				Derive(func(b *Argument) {
					b.Fix() // i — spelled in the claim
					b.Do(By(word_bits.BitWordZero))
				}))
			agree := a.Have(
				"a value never disagrees with itself, so both sides are clear everywhere",
				"∀i:num. word_bit(i, 0) ⇔ word_bit(i, word_xor(x, x))",
				Derive(func(b *Argument) {
					i := b.Fix()
					read := b.Have(
						"the difference's bit is x's disagreement with itself",
						"word_bit(i, word_xor(x, x)) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, x))",
						By(word_bits.BitOfXor))
					b.Do(By(read, zeroBits.At(i)))
				}))
			a.Show(
				"agreeing everywhere, the difference is the zero word",
				By(agree, word_bits.BitsEqAll))
		}),
})}

// ---------------------------------------------------------------------------
// NotNot · XorNot · XorNotZero — the complement laws
// ---------------------------------------------------------------------------

// NotNot — complementing twice returns a bounded word. Inside the
// width the two negations cancel; beyond it the range bound clears
// x's bits as well as the double complement's.
var NotNot = notNotThm{family.Add(registry.ProofEntry{
	Name: "NotNot",
	Key:  "prop_94034acd88dc8636",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "x = word_not(n, word_not(n, x))",
		},
		func(a *Argument, n, x *Expr[Nat], xBound Fact) {
			agree := a.Have(
				"position by position: inside the width the two negations cancel; past it both sides are clear",
				"∀k:num. word_bit(k, x) ⇔ word_bit(k, word_not(n, word_not(n, x)))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitNot.At(n, x, k),
						word_bits.BitNot.At(n, b.TermAs[Nat]("word_not(n, x)"), k),
						xBound,
						word_bits.BitBelowBound.At(n, x, k)))
				}))
			a.Show(
				"agreeing everywhere, complementing twice returns the value",
				By(agree, word_bits.BitsEqAll))
		}),
})}

// XorNot — complementing a difference equals differencing with
// either operand complemented. Inside the width, negating one input
// negates disagreement. Each range bound clears the bare operand's
// high bits in the corresponding equation.
var XorNot = xorNotThm{family.Add(registry.ProofEntry{
	Name: "XorNot",
	Key:  "prop_f5f5d86989afff4c",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x y:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
				"y < nat_pow(2, n)",
			},
			Conclusion: "word_not(n, word_xor(x, y)) = word_xor(x, word_not(n, y)) ∧ " +
				"word_not(n, word_xor(x, y)) = word_xor(word_not(n, x), y)",
		},
		func(a *Argument, n, x, y *Expr[Nat], xBound, yBound Fact) {
			agreeRight := a.Have(
				"position by position: inside the width both sides negate one disagreement; past it both are clear",
				"∀k:num. word_bit(k, word_not(n, word_xor(x, y))) ⇔ word_bit(k, word_xor(x, word_not(n, y)))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitNot.At(n, b.TermAs[Nat]("word_xor(x, y)"), k),
						word_bits.BitOfXor.At(x, y, k),
						word_bits.BitOfXor.At(x, b.TermAs[Nat]("word_not(n, y)"), k),
						word_bits.BitNot.At(n, y, k),
						xBound,
						word_bits.BitBelowBound.At(n, x, k)))
				}))
			agreeLeft := a.Have(
				"and complementing the left operand likewise, with y the bare operand this time",
				"∀k:num. word_bit(k, word_not(n, word_xor(x, y))) ⇔ word_bit(k, word_xor(word_not(n, x), y))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitNot.At(n, b.TermAs[Nat]("word_xor(x, y)"), k),
						word_bits.BitOfXor.At(x, y, k),
						word_bits.BitOfXor.At(b.TermAs[Nat]("word_not(n, x)"), y, k),
						word_bits.BitNot.At(n, x, k),
						yBound,
						word_bits.BitBelowBound.At(n, y, k)))
				}))
			eqRight := a.Have(
				"agreeing everywhere, the right-complemented law",
				"word_not(n, word_xor(x, y)) = word_xor(x, word_not(n, y))",
				By(
					agreeRight,
					At(word_bits.BitsEqAll,
						a.Term("word_not(n, word_xor(x, y))"), a.Term("word_xor(x, word_not(n, y))"))))
			eqLeft := a.Have(
				"and the left-complemented",
				"word_not(n, word_xor(x, y)) = word_xor(word_not(n, x), y)",
				By(
					agreeLeft,
					At(word_bits.BitsEqAll,
						a.Term("word_not(n, word_xor(x, y))"), a.Term("word_xor(word_not(n, x), y)"))))
			a.Show(
				"both complements together",
				By(eqRight, eqLeft))
		}),
})}

// XorNotZero — differencing with the all-ones mask complements a
// bounded word. The mask is set exactly below the width, so the right
// difference complements x there and is clear beyond it. Symmetry
// gives the other order.
var XorNotZero = xorNotZeroThm{family.Add(registry.ProofEntry{
	Name: "XorNotZero",
	Key:  "prop_5b9ccf26366497e1",
	Build: family.Theorem(
		Statement{
			Binders: "∀n x:num.",
			Hypotheses: []string{
				"x < nat_pow(2, n)",
			},
			Conclusion: "word_not(n, x) = word_xor(x, word_not(n, 0)) ∧ " +
				"word_not(n, x) = word_xor(word_not(n, 0), x)",
		},
		func(a *Argument, n, x *Expr[Nat], xBound Fact) {
			agreeRight := a.Have(
				"position by position: the mask is set exactly inside "+
					"the width, so disagreeing with it complements there",
				"∀k:num. word_bit(k, word_not(n, x)) ⇔ word_bit(k, word_xor(x, word_not(n, 0)))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					b.Do(By(
						Normalized,
						word_bits.BitNot.At(n, x, k),
						word_bits.BitNot.At(n, b.TermAs[Nat]("0"), k),
						word_bits.BitWordZero,
						word_bits.BitOfXor.At(x, b.TermAs[Nat]("word_not(n, 0)"), k),
						xBound,
						word_bits.BitBelowBound.At(n, x, k)))
				}))
			eqRight := a.Have(
				"agreeing everywhere, the mask-on-the-right law",
				"word_not(n, x) = word_xor(x, word_not(n, 0))",
				By(
					agreeRight,
					At(word_bits.BitsEqAll, a.Term("word_not(n, x)"), a.Term("word_xor(x, word_not(n, 0))"))))
			a.Show(
				"both maskings together",
				By(Normalized, eqRight, XorSym.At(x, a.TermAs[Nat]("word_not(n, 0)"))))
		}),
})}

// ---------------------------------------------------------------------------
// XorEqZero — the difference as an equality test
// ---------------------------------------------------------------------------

// XorEqZero — the val-face form: the difference vanishes
// exactly when the operands agree. Forward, a vanishing difference has
// no bits — so no position disagrees, and agreement everywhere pins
// the values equal. Backward is congruence into XorRefl: equal
// operands difference to a value differenced with itself.
var XorEqZero = xorEqZeroThm{family.Add(registry.ProofEntry{
	Name: "XorEqZero",
	Key:  "prop_925c083a464b8748",
	Build: family.Theorem(
		Statement{
			Binders:    "∀x y:num.",
			Conclusion: "x = y ⇔ 0 = word_xor(x, y)",
		},
		func(a *Argument, x, y Term) {
			forward := a.Have(
				"equal operands leave no disagreement — the difference of a value with itself",
				"(x = y) ⇒ (0 = word_xor(x, y))",
				Derive(func(b *Argument) {
					eq := b.Assume()
					b.Do(By(eq, At(XorRefl, x)))
				}))
			backward := a.Have(
				"a vanishing difference forces agreement position by "+
					"position, and agreement everywhere pins the values equal",
				"(0 = word_xor(x, y)) ⇒ (x = y)",
				Derive(func(b *Argument) {
					vanishes := b.Assume()
					agree := b.Have(
						"no position disagrees — each bit of the difference is a bit of the zero word",
						"∀i:num. word_bit(i, x) ⇔ word_bit(i, y)",
						Derive(func(c *Argument) {
							c.Fix() // i — spelled in the claims below
							clear := c.Have(
								"the difference has no bit here",
								"¬word_bit(i, word_xor(x, y))",
								By(Normalized, vanishes, word_bits.BitWordZero))
							read := c.Have(
								"and its bit would be the operands' disagreement",
								"word_bit(i, word_xor(x, y)) ⇔ ¬(word_bit(i, x) ⇔ word_bit(i, y))",
								By(word_bits.BitOfXor))
							c.Do(By(clear, read))
						}))
					b.Do(By(agree, word_bits.BitsEqAll))
				}))
			a.Show(
				"both directions together",
				By(Normalized, forward, backward))
		}),
})}
