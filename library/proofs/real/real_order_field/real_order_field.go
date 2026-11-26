// real_order_field.go — the chapter: where ℝ's order meets its inverse.
//
// Three parts, marked by banners:
//
// - An inverse cannot change sign
// - Clearing a positive denominator
// - Inversion reverses the order on the positives

package real_order_field

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// An inverse cannot change sign
// ---------------------------------------------------------------------------
//
// an inverse cannot change sign, and a quotient is a product with an
// inverse in it.
//
// README §"The chapter's arc", movements 1–2 (the sign of an inverse,
// the sign of a quotient).

// invPosOfPos — the sign of an inverse, in the direction that carries
// the chapter's work.
//
// Multiply the claim through by x. On the left the product is &0, on the
// right it is &1, so the scaled comparison is one the order already
// knows; and x is positive, so it cancels back off again. The single
// hypothesis does both jobs at once — it licenses the cancellation, and
// it makes x non-zero, which is the side condition the inverse law
// carries.
//
// It does not unfold `<`. The two order facts it leans on — the
// cancellation law and &0 < &1 — state the strict order and keep it
// folded, so unfolding the goal alone would leave a claim about `≤` with
// nothing in the chapter to meet it.
var invPosOfPos = invPosOfPosThm{family.Add(registry.ProofEntry{
	Name: "invPosOfPos",
	Key:  "prop_bb9738b7e8bc21ac",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 < x",
		},
		Conclusion: "&0 < real_inv(x)",
	},
		func(a *Argument, x Term, pos Fact) {
			v := ops(a.Ctx())
			zero, invX := v.Lit(0), v.Invert(x)

			nonzero := a.Have(
				"positivity rules x = &0 out",
				"x ≠ &0",
				By(pos, At(real_order_ring.NonzeroOfPositive, x))) // &0 < x₀ ⇒ x₀ ≠ &0

			scaled := a.Have(
				"scaled by x on the right, the comparison is &0 against &1",
				"&0 * x < real_inv(x) * x",
				// Consumed as a rewrite of the claim's own left side rather
				// than as a premise: ↦ &0 < real_inv(x₀) * x₀.
				Cite(real_ring.MulLeftZero),
				By(
					nonzero,
					At(real_construction.MulLeftInverse, x), // x₀ ≠ &0 ⇒ real_inv(x₀) * x₀ = &1
					real_order_ring.ZeroLessThanOne,
				))

			a.Show(
				"x is positive, so it cancels off the right of both products again",
				// &0 < x₀ ∧ &0 * x₀ < real_inv(x₀) * x₀ ⇒ &0 < real_inv(x₀)
				By(pos, scaled, At(real_order_ring.LessThanCancelMulRight, zero, invX, x)))
		}),
})}

// InvPos — the chapter's statement of the sign of an inverse, and the
// form later members use: it moves a strict positivity across real_inv
// in whichever direction the argument needs.
//
// Only one implication has content, and both readings of the ⇔ are that
// same implication at different arguments. Read at x it is one direction
// outright. Read at real_inv(x) it says that a positive inverse has a
// positive inverse of its own — and inverting twice returns the argument,
// so that inner double inverse is x, which is the other direction.
//
// The involution is what makes the two directions one theorem, and it is
// the only fact here besides the implication itself.
var InvPos = invPosThm{family.Add(registry.ProofEntry{
	Name: "InvPos",
	Key:  "prop_cc84418cbb39a412",
	Build: family.Theorem("∀x:real. &0 < real_inv(x) ⇔ &0 < x",
		func(a *Argument, x Term) {
			invX := ops(a.Ctx()).Invert(x)
			a.Iff()
			a.Forward(
				"read the same implication at real_inv(x), and undo the extra inversion",
				func(b *Argument, posInv Fact) {
					invTwicePos := b.Have(
						"a positive inverse has a positive inverse of its own",
						"&0 < real_inv(real_inv(x₀))",
						// &0 < real_inv(x₀) ⇒ &0 < real_inv(real_inv(x₀))
						By(posInv, At(invPosOfPos, invX)))

					b.Show(
						"and inverting twice returns x, so that is the positivity of x",
						By(invTwicePos, field.InvInv.Read(real_field.Field)))
				})
			a.Backward(
				"the implication read at x, which is the direction it is stated in",
				func(b *Argument, pos Fact) {
					b.Show(
						"x is positive, so its inverse is",
						By(pos, At(invPosOfPos, x)))
				})
		}),
})}

// InvNonneg — the non-strict reading of InvPos, and it needs no case
// analysis of its own.
//
// Each side of the ⇔ splits into a strict half and an equality half, and
// the chapter already has an ⇔ for each: InvPos matches the strict
// halves, and the convention that makes real_inv total matches the
// equality halves. So the two two-piece decompositions agree piece by
// piece, which is the whole statement.
//
// InvPos carries the strict half; the only new ingredient is the
// degenerate one, and it holds because real_inv sends &0 to &0 and sends
// nothing else there — so a vanishing side stays a vanishing side.
var InvNonneg = invNonnegThm{family.Add(registry.ProofEntry{
	Name: "InvNonneg",
	Key:  "prop_43fe122ab2c04298",
	Build: family.Theorem("∀x:real. &0 ≤ real_inv(x) ⇔ &0 ≤ x",
		func(a *Argument, x Term) {
			v := ops(a.Ctx())
			zero, invX := v.Lit(0), v.Invert(x)

			a.Show(
				"split each side into its strict part and its equality, and match the two halves",
				By(
					// &0 ≤ real_inv(x₀) ⇔ &0 < real_inv(x₀) ∨ &0 = real_inv(x₀)
					At(real_order_ring.LessEqSplit, zero, invX),
					At(real_order_ring.LessEqSplit, zero, x), // &0 ≤ x₀ ⇔ &0 < x₀ ∨ &0 = x₀
					At(InvPos, x),                            // the strict halves: &0 < real_inv(x₀) ⇔ &0 < x₀
					field.InvEqZero.Read(real_field.Field),   // the equality halves
				))
		}),
})}

// invNonnegOfNonneg — one half of InvNonneg, and nothing else.
var invNonnegOfNonneg = invNonnegOfNonnegThm{family.Add(registry.ProofEntry{
	Name: "invNonnegOfNonneg",
	Key:  "prop_a908999808ba31f9",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "&0 ≤ real_inv(x)",
	},
		func(a *Argument) {
			// Left ∀-closed and unstripped, the goal IS one half of the ⇔, so
			// the cite closes it outright and has no hypothesis slot to ground.
			a.Do(Cite(InvNonneg))
		}),
})}

// DivPos — a quotient of positives is positive.
//
// Dividing by y is multiplying by its inverse, and once the quotient is
// written that way the statement is the product rule applied to a pair
// the chapter already knows to be positive: x by hypothesis, and the
// inverse of y because y is.
//
// This is the chapter's one member that reads `/` as what it is defined
// to be, and the unfold is forced rather than chosen. Elsewhere a
// quotient is consumed whole by a real_field law; here there is no law
// to consume it, because none of them says anything about the SIGN of a
// quotient — which is exactly what makes this the member where that sign
// is first established.
var DivPos = divPosThm{family.Add(registry.ProofEntry{
	Name: "DivPos",
	Key:  "prop_86ebe7d5efe5a90f",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"&0 < y",
		},
		Conclusion: "&0 < x / y",
	},
		func(a *Argument, x, y Term) {
			invY := ops(a.Ctx()).Invert(y)

			a.Do(
				// ↦ &0 < x₀ * real_inv(y₀), the two positivity hypotheses
				// discharged into the context alongside it.
				Unfold(real_field.RealDivDef),
				// &0 < x₀ ∧ &0 < real_inv(y₀) ⇒ &0 < x₀ * real_inv(y₀), so
				// what is left to supply is the positivity of the inverse.
				Cite(real_order_ring.MulPos, x, invY),
				// ↦ reads that as the positivity of y₀ itself, which is a
				// hypothesis — so the cite closes the section.
				Cite(InvPos),
			)
		}),
})}

// ---------------------------------------------------------------------------
// Clearing a positive denominator
// ---------------------------------------------------------------------------
//
// clearing a positive denominator: the six laws that move a division
// across a relation and turn it into a multiplication.
//
// Named for the side the resulting PRODUCT lands on, as in
// real_order_ring's LessEqSubAddLeft family.
//
// README §"The chapter's arc", movement 3.

// LessEqDivMulLeft — the first of the cross-multiplication laws, and the
// chapter's method for all of them.
//
// Rescale both sides by z. Since z is positive the rescaling neither
// creates nor destroys the comparison, so the ≤ may be read at the
// scaled pair instead; and a quotient scaled by its own denominator is
// the numerator again, which is what clears the division away. So the
// positivity does both jobs at once — it licenses the rescaling, and it
// makes z non-zero, which is the side condition the quotient law
// carries.
var LessEqDivMulLeft = lessEqDivMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessEqDivMulLeft",
	Key:  "prop_413073b46773500",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x ≤ y / z ⇔ x * z ≤ y",
	},
		func(a *Argument, x, y, z Term, pos Fact) {
			quot := ops(a.Ctx()).Quot(y, z)

			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"rescale by z, and the quotient meets its own denominator",
				By(
					Normalized,
					pos,
					// &0 < z₀ ⇒ (x₀ * z₀ ≤ y₀ / z₀ * z₀ ⇔ x₀ ≤ y₀ / z₀)
					At(real_order_ring.LessEqMulRightEq, x, quot, z),
					At(field.DivRightMul.Read(real_field.Field), y, z), // z₀ ≠ &0 ⇒ y₀ / z₀ * z₀ = y₀
					At(real_order_ring.NonzeroOfPositive, z),           // &0 < z₀ ⇒ z₀ ≠ &0
				))
		}),
})}

// LessEqDivMulRight — LessEqDivMulLeft's method with the quotient on the
// other side of the comparison, which is a second theorem rather than a
// second reading of the first: ≤ is not symmetric, so which side carries
// the denominator is part of what is being said.
//
// The proof changes only where the scaled quotient appears — the
// rescaling law is grounded at the pair the statement is actually about,
// and the quotient law at that side's numerator.
var LessEqDivMulRight = lessEqDivMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessEqDivMulRight",
	Key:  "prop_65a03a483d3e2586",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x / z ≤ y ⇔ x ≤ y * z",
	},
		func(a *Argument, x, y, z Term, pos Fact) {
			quot := ops(a.Ctx()).Quot(x, z)

			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"rescale by z, and the quotient meets its own denominator",
				By(
					Normalized,
					pos,
					// &0 < z₀ ⇒ (x₀ / z₀ * z₀ ≤ y₀ * z₀ ⇔ x₀ / z₀ ≤ y₀)
					At(real_order_ring.LessEqMulRightEq, quot, y, z),
					At(field.DivRightMul.Read(real_field.Field), x, z), // z₀ ≠ &0 ⇒ x₀ / z₀ * z₀ = x₀
					At(real_order_ring.NonzeroOfPositive, z),           // &0 < z₀ ⇒ z₀ ≠ &0
				))
		}),
})}

// LessThanDivMulLeft — the strict twin of LessEqDivMulLeft, reached the
// way LessThanDivMulRight reaches its own.
//
// Unfolding `<` negates both sides of the equivalence at once and leaves
// the two pairs compared the other way round, which crosses the
// denominator to the other side: the law underneath is
// LessEqDivMulRight.
var LessThanDivMulLeft = lessThanDivMulLeftThm{family.Add(registry.ProofEntry{
	Name: "LessThanDivMulLeft",
	Key:  "prop_5866c025560084ca",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x < y / z ⇔ x * z < y",
	},
		func(a *Argument, x, y, z Term) {
			a.Do(
				Cite(LessEqDivMulRight, y, x, z), // &0 < z₀ ⇒ (y₀ / z₀ ≤ x₀ ⇔ y₀ ≤ x₀ * z₀)
				// ↦ the unfold makes the goal that equivalence, negated on
				// both sides — which closes it.
				Unfold(real_order_ring.NotLessEq),
			)
		}),
})}

// LessThanDivMulRight — the strict cross-multiplication law, and
// unfolding `<` makes it the non-strict one.
//
// Here the unfold is what the member is: `x < y` is `¬(y ≤ x)`, so both
// sides of the equivalence are negations, `¬A ⇔ ¬B` is `A ⇔ B`, and the
// two cancel together. What survives compares the same two pairs the
// other way round — and reversing a comparison moves the denominator
// from the smaller side to the larger one, so the law it lands on is
// LessEqDivMulLeft rather than this member's own non-strict twin.
var LessThanDivMulRight = lessThanDivMulRightThm{family.Add(registry.ProofEntry{
	Name: "LessThanDivMulRight",
	Key:  "prop_7ad9899303ae3925",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x / z < y ⇔ x < y * z",
	},
		func(a *Argument, x, y, z Term) {
			a.Do(
				Cite(LessEqDivMulLeft, y, x, z), // &0 < z₀ ⇒ (y₀ ≤ x₀ / z₀ ⇔ y₀ * z₀ ≤ x₀)
				// ↦ the unfold makes the goal that equivalence, negated on
				// both sides — which closes it.
				Unfold(real_order_ring.NotLessEq),
			)
		}),
})}

// EqDivMulLeft — LessEqDivMulLeft's rescaling, performed on an equation
// instead of a comparison.
//
// Only the law that undoes the rescaling changes. An order needs z to be
// positive to keep a comparison; a ring needs only that z be non-zero to
// keep an equation, and it says so by offering z = &0 as the alternative
// to cancelling. Positivity rules that alternative out, and it is the
// same non-vanishing that the quotient law wants — so one hypothesis
// still does both jobs.
var EqDivMulLeft = eqDivMulLeftThm{family.Add(registry.ProofEntry{
	Name: "EqDivMulLeft",
	Key:  "prop_cce11a769057969e",
	Build: family.Theorem(Statement{
		Binders: "∀x y z:real.",
		Hypotheses: []string{
			"&0 < z",
		},
		Conclusion: "x = y / z ⇔ x * z = y",
	},
		func(a *Argument, x, y, z Term, pos Fact) {
			quot := ops(a.Ctx()).Quot(y, z)

			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"cancel z off both sides — positivity rules out the vanishing "+
					"alternative — and the quotient meets its own denominator",
				By(
					Normalized,
					pos,
					At(real_ring.MulRightCancel, x, quot, z), // x₀ * z₀ = y₀ / z₀ * z₀ ⇔ x₀ = y₀ / z₀ ∨ z₀ = &0
					At(field.DivRightMul.Read(real_field.Field), y, z), // z₀ ≠ &0 ⇒ y₀ / z₀ * z₀ = y₀
					At(real_order_ring.NonzeroOfPositive, z),           // &0 < z₀ ⇒ z₀ ≠ &0
				))
		}),
})}

// ---------------------------------------------------------------------------
// Inversion reverses the order on the positives
// ---------------------------------------------------------------------------
//
// inversion reverses the order on the positives, and no positive real is
// least.
//
// README §"The chapter's arc", movement 4, and §"Why `ExistsSmallerPos`
// lives here" for its placement.

// InvAntitone — of two positive reals, the larger has the smaller
// inverse.
//
// Scale x < y on the left by real_inv(x), which is positive because x
// is. The left-hand product is then the inverse meeting its own
// argument, so the scaled comparison reads &1 < real_inv(x) * y. And &1
// is also what real_inv(y) * y is, by the same collision at y — which is
// positive, being above x. So the comparison in hand is already between
// two products sharing the factor y; and y is positive, so that shared
// factor cancels off the right, leaving the two inverses compared
// directly.
//
// Only the smaller endpoint is assumed positive. The larger inherits it,
// which is why the hypothesis names &0 once rather than twice.
var InvAntitone = invAntitoneThm{family.Add(registry.ProofEntry{
	Name: "InvAntitone",
	Key:  "prop_ece908a182ea5191",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"x < y",
		},
		Conclusion: "real_inv(y) < real_inv(x)",
	},
		func(a *Argument, x, y Term, posBelow Fact) {
			v := ops(a.Ctx())
			zero, invX, invY := v.Lit(0), v.Invert(x), v.Invert(y)

			posY := a.Have(
				"y inherits the positivity of x, being above it",
				"&0 < y",
				By(posBelow, At(real_order_ring.LessThanTrans, zero, x, y))) // &0 < x₀ ∧ x₀ < y₀ ⇒ &0 < y₀

			invXPos := a.Have(
				"and positivity survives the inverse",
				"&0 < real_inv(x)",
				By(posBelow, InvPos))

			// The two collapses below are the member's only Normalized sites:
			// engine shaping, not part of the argument.
			scaledLeft := a.Have(
				"scaling by real_inv(x) collides it with its own argument, leaving &1",
				"&1 < real_inv(x) * y",
				By(
					Normalized,
					posBelow,
					invXPos,
					// &0 < real_inv(x₀) ∧ x₀ < y₀ ⇒ real_inv(x₀) * x₀ < real_inv(x₀) * y₀
					At(real_order_ring.LessThanMulLeft, invX, x, y),
					At(real_construction.MulLeftInverse, x),  // x₀ ≠ &0 ⇒ real_inv(x₀) * x₀ = &1
					At(real_order_ring.NonzeroOfPositive, x), // &0 < x₀ ⇒ x₀ ≠ &0
				))

			sharedFactor := a.Have(
				"and &1 is what the same collision at y produces",
				"real_inv(y) * y < real_inv(x) * y",
				By(
					Normalized,
					posY,
					scaledLeft,
					At(real_construction.MulLeftInverse, y),  // y₀ ≠ &0 ⇒ real_inv(y₀) * y₀ = &1
					At(real_order_ring.NonzeroOfPositive, y), // &0 < y₀ ⇒ y₀ ≠ &0
				))

			a.Show(
				"both sides now carry the positive factor y, which cancels",
				// &0 < y₀ ∧ real_inv(y₀) * y₀ < real_inv(x₀) * y₀ ⇒ real_inv(y₀) < real_inv(x₀)
				By(posY, sharedFactor, At(real_order_ring.LessThanCancelMulRight, invY, invX, y)))
		}),
})}

// InvAntitoneWeak — inversion reverses the order on the positives in the
// weak reading too: of two positive reals, the one that is no larger has
// the inverse that is no smaller. InvAntitone says it strictly; this
// says it with both comparisons weakened.
//
// A non-strict comparison is a strict one or an equality, and that one
// law opens BOTH sides here: cited at (x, y) it takes the hypothesis
// apart, cited at the two inverses it takes the goal apart, and the
// halves then correspond. Only the strict half has content, and that is
// InvAntitone; the equal half needs no lemma, since x = y makes the two
// inverses the same term. Splitting both sides is what makes this one
// action rather than a case block, and it is why the premise list names
// the splitting law and the strict member and nothing else.
var InvAntitoneWeak = invAntitoneWeakThm{family.Add(registry.ProofEntry{
	Name: "InvAntitoneWeak",
	Key:  "prop_766ac74edca7e0e7",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"x ≤ y",
		},
		Conclusion: "real_inv(y) ≤ real_inv(x)",
	},
		func(a *Argument, x, y Term, bounds Fact) {
			v := ops(a.Ctx())
			invX, invY := v.Invert(x), v.Invert(y)

			// Normalized — engine shaping, not part of the argument.
			a.Show(
				"split hypothesis and conclusion the same way, and match the halves",
				By(
					Normalized,
					bounds,
					At(real_order_ring.LessEqSplit, x, y), // x₀ ≤ y₀ ⇔ x₀ < y₀ ∨ x₀ = y₀
					// real_inv(y₀) ≤ real_inv(x₀) ⇔ real_inv(y₀) < real_inv(x₀) ∨ real_inv(y₀) = real_inv(x₀)
					At(real_order_ring.LessEqSplit, invY, invX),
					At(InvAntitone, x, y), // &0 < x₀ ∧ x₀ < y₀ ⇒ real_inv(y₀) < real_inv(x₀)
				))
		}),
})}

// ExistsSmallerPos — below every positive real there is another: the
// positives have no minimum, and no positive real is the least one.
//
// This is what an ε-argument appeals to when it needs room to shrink:
// whatever tolerance has been fixed, a strictly smaller positive
// tolerance is available.
//
// Halving is the witness: e is d / (&1 + &1). It is positive because
// both d and &1 + &1 are, and it is below d because clearing the
// denominator turns the claim into d < d * (&1 + &1), which distributes
// to d < d + d — and that is the positivity of d read back.
//
// The denominator is spelled &1 + &1 rather than &2 deliberately. The
// two are the same real, and the proof uses two things about it: that it
// is positive, which it is by sitting above &1; and its SHAPE, since
// distributing d across it is what turns d * (&1 + &1) into d + d. As a
// sum of units both are immediate — as the literal &2 both would be
// facts about ℕ numerals, and would drag the numeral tower in behind
// them. Written this way the whole proof stays inside the ordered field.
var ExistsSmallerPos = existsSmallerPosThm{family.Add(registry.ProofEntry{
	Name: "ExistsSmallerPos",
	Key:  "prop_7e9e3a9ee710b0cf",
	Build: family.Theorem(Statement{
		Binders: "∀d:real.",
		Hypotheses: []string{
			"&0 < d",
		},
		Conclusion: "∃e:real. &0 < e ∧ e < d",
	},
		func(a *Argument, d Term, pos Fact) {
			v := ops(a.Ctx())
			zero, one := v.Lit(0), v.Lit(1)
			onePlusOne := v.Add(one, one)
			half := v.Quot(d, onePlusOne)

			a.Take(half) // e := d₀ / (&1 + &1)

			denomPos := a.Have(
				"the denominator is above &1, which is above &0",
				"&0 < &1 + &1",
				By(
					At(real_order_ring.LessThanSelfAddRight, one, one), // &1 < &1 + &1 ⇔ &0 < &1
					real_order_ring.ZeroLessThanOne,
					At(real_order_ring.LessThanTrans, zero, one, onePlusOne), // &0 < &1 ∧ &1 < &1 + &1 ⇒ &0 < &1 + &1
				))

			halfPos := a.Have(
				"so the halved d is a quotient of positives",
				"&0 < d / (&1 + &1)",
				By(pos, denomPos, At(DivPos, d, onePlusOne))) // &0 < d₀ ∧ &0 < &1 + &1 ⇒ &0 < d₀ / (&1 + &1)

			halfBelow := a.Have(
				"and clearing the denominator asks only that d be below d + d",
				"d / (&1 + &1) < d",
				By(
					pos,
					denomPos,
					// &0 < &1 + &1 ⇒ (d₀ / (&1 + &1) < d₀ ⇔ d₀ < d₀ * (&1 + &1))
					At(LessThanDivMulRight, d, d, onePlusOne),
					At(real_construction.LeftDistrib, d, one, one), // d₀ * (&1 + &1) = d₀ * &1 + d₀ * &1
					At(real_ring.MulRightId, d),                    // d₀ * &1 = d₀
					real_order_ring.LessThanSelfAddRight,
				))

			a.Show(
				"half of d is the smaller positive the statement asks for",
				By(halfPos, halfBelow))
		}),
})}

// NonposOfSmallMultiples — a real that is at most C·ε for every small
// enough positive ε is at most 0: if x ≤ C·ε whenever 0 < ε ≤ η, for some
// positive η, then x ≤ 0.
//
// Suppose x positive. At ε = η, x is at most C·η, which is at most 0 when
// C is. When C is positive, take ε = x/(2C) if that is at most η: there x
// is at most C·x/(2C) = x/2. Otherwise η < x/(2C), that is 2C·η < x, and x
// is at most C·η, below x/2. Either way x is at most half of itself, which
// no positive real is.
var NonposOfSmallMultiples = nonposOfSmallMultiplesThm{family.Add(registry.ProofEntry{
	Name: "NonposOfSmallMultiples",
	Key:  "prop_38a8cb534f27781",
	Build: family.Theorem(Statement{
		Binders: "∀x C η:real.",
		Hypotheses: []string{
			"&0 < η",
			"∀ε:real. &0 < ε ∧ ε ≤ η ⇒ x ≤ C * ε",
		},
		Conclusion: "x ≤ &0",
	},
		func(a *Argument, x, C, η *Expr[Real], positive, small Fact) {
			contrary := a.SupposeNot()
			a.Cases(a.Term("C ≤ &0"))
			a.When(
				"if C is at most 0, so is C·η, which x is below",
				func(b *Argument, nonpositive Fact) {
					b.Show(
						"x ≤ C·η ≤ 0",
						ByArith(
							contrary,
							positive,
							nonpositive,
							small.At(η),
							real_order_ring.LessEqMulRight.At(C, b.TermAs[Real]("&0"), η)))
				})
			a.Otherwise(
				"if C is positive, at ε = x/(2C) or at ε = η, C·ε is at most x/2",
				func(b *Argument, notNonpositive Fact) {
					twice := b.TermAs[Real]("C + C")
					ratio := b.TermAs[Real]("x / (C + C)")
					double := b.Have(
						"2C is positive",
						"&0 < C + C",
						ByArith(notNonpositive))
					cleared := b.Have(
						"x/(2C) times 2C is x",
						"x / (C + C) * (C + C) = x",
						By(
							double,
							field.DivRightMul.Read(real_field.Field).At(x, twice),
							real_order_ring.NonzeroOfPositive.At(twice)))
					b.Cases(b.Term("x / (C + C) ≤ η"))
					b.When(
						"if x/(2C) is at most η, x is at most C·x/(2C) = x/2",
						func(c *Argument, within Fact) {
							c.Show(
								"x ≤ x/2 with x positive",
								ByArith(contrary, double, cleared, within, DivPos.At(x, twice), small.At(ratio)))
						})
					b.Otherwise(
						"otherwise 2C·η is below x, and x is at most C·η",
						func(c *Argument, beyond Fact) {
							c.Show(
								"x ≤ C·η < x/2 with x positive",
								ByArith(contrary, positive, double, beyond, LessThanDivMulLeft.At(η, x, twice), small.At(η)))
						})
				})
		}),
})}
