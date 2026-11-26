// cone.go — the cone over a convex set, and the two facts a fold needs
// of it.
//
// Above a convex set sits its cone: the points of the set scaled to an
// arbitrary height, each read together with the height it was scaled
// to. `PositiveCombination` is the law that makes it a cone — two of
// its points, at heights whose total is positive, sum to a point of it
// at the summed height. Convexity is what supplies the underlying
// point of the set: the two heights, taken against their total, are
// weights totalling one, and the point they average out of the two
// given ones is the one the sum stands above.
//
// The two heights are named separately rather than parameterized as t
// and 1 - t, and neither is required to be positive — only their total
// is. That is the form a fold needs. A fold over a finite family
// reaches each step holding the weight of one new point beside the
// total weight of everything already summed; either may be zero, their
// total is not, and no subtraction relates them, so the law applies to
// those two numbers as they stand and nothing is rescaled between
// steps.
//
// `VanishingWeights` is the one case the law cannot reach: a total
// weight of zero. Nonnegative numbers totalling zero are each zero, so
// a combination carried by such weights scales every one of its points
// by zero, and a fold all of whose terms are the element it starts
// from is that element — here the zero vector. Convexity takes no part
// in it; the subject is a fold of scaled vectors over an arbitrary
// finite index set, the points unconstrained.

package convex

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PositiveCombination — a convex set's cone is closed under addition.
//
// The witness is the average of p and q at the two heights rescaled by
// their total, and the proof is that rescaling read in both directions.
// One way it makes the weights legitimate: each is a nonnegative height
// against the nonnegative inverse of the total, and the two total one
// because that inverse factors out of the sum — which is what convexity
// asks for, and what lands the average in s. The other way it undoes
// itself: the total multiplied back into a weight is the height it came
// from, so scaling the average to the total height returns the
// combination it was built out of.
var PositiveCombination = positiveCombinationThm{family.Add(registry.ProofEntry{
	Name: "PositiveCombination",
	Key:  "prop_7d99b18058072c52",
	Build: family.Theorem(
		Statement{
			Binders: "∀s:set(num → real). ∀a b:real. ∀p q:(num → real).",
			Hypotheses: []string{
				"convex(s)",
				"&0 ≤ a",
				"&0 ≤ b",
				"&0 < a + b",
				"p ∈ s",
				"q ∈ s",
			},
			Conclusion: "∃w:(num → real). w ∈ s ∧ a • p + b • q = (a + b) • w",
			Abbrev: Abbrev{
				{Name: "pWeight", Text: "a * real_inv(a + b)"},
				{Name: "qWeight", Text: "b * real_inv(a + b)"},
				{Name: "weightedMean", Text: "(«pWeight») • p + («qWeight») • q"},
			},
		},
		func(
			arg *Argument,
			s *Expr[Set[Fun[Nat, Real]]],
			a, b *Expr[Real],
			p, q *Expr[Fun[Nat, Real]],
			convexity, aNonneg, bNonneg, totalPos, pInSet, qInSet Fact,
		) {

			// Positivity of the total is what the argument spends, and it
			// spends it twice: on the total being invertible at all, and
			// on the sign of that inverse. Nothing below asks more of the
			// individual heights than that they are nonnegative.
			nonzero := arg.Have(
				"a positive total is not zero",
				"a + b ≠ &0",
				By(totalPos, real_order_ring.NonzeroOfPositive))
			unit := arg.Have(
				"so the total and its inverse multiply to one",
				"(a + b) * real_inv(a + b) = &1",
				By(nonzero, field.MulRightInverse.Read(real_field.Field)))

			invNonneg := arg.Have(
				"the inverse of a positive number is itself nonnegative",
				"&0 ≤ real_inv(a + b)",
				By(totalPos, real_order_field.InvPos, real_order_ring.LessEqOfLessThan))

			// Read one way, the rescaling turns the two heights into
			// legitimate convexity weights.
			pWeightNonneg := arg.Have(
				"p's weight is a nonnegative height against a nonnegative inverse",
				"&0 ≤ «pWeight»",
				By(aNonneg, invNonneg, real_order_ring.LessEqMulRight, real_ring.MulLeftZero))
			qWeightNonneg := arg.Have(
				"and q's weight likewise",
				"&0 ≤ «qWeight»",
				By(bNonneg, invNonneg, real_order_ring.LessEqMulRight, real_ring.MulLeftZero))
			weightsSumOne := arg.Have(
				"the two weights total one: the common inverse factors out of a + b",
				"«pWeight» + «qWeight» = &1",
				By(unit, real_ring.RightDistrib))
			inSet := arg.Have(
				"so convexity puts their average of p and q in s",
				"«weightedMean» ∈ s",
				By(convexity, pInSet, qInSet, pWeightNonneg, qWeightNonneg, weightsSumOne, ConvexDef))

			// Read the other way, the same rescaling undoes itself: the
			// total multiplied back into a weight is the height it came
			// from.
			pRescaled := arg.Have(
				"the total undoes p's rescaling",
				"(a + b) * «pWeight» = a",
				By(unit, real_ring.MulAC, real_ring.MulRightId))
			qRescaled := arg.Have(
				"and q's",
				"(a + b) * «qWeight» = b",
				By(unit, real_ring.MulAC, real_ring.MulRightId))
			// Scaling the average by the total distributes over its two
			// terms and composes with each weight, which puts the two
			// heights back where they started.
			atTotalHeight := arg.Have(
				"so the average scaled to height a + b is the combination itself",
				"a • p + b • q = (a + b) • «weightedMean»",
				Simp(
					Fwd(vec_space.SmulAddLeft.Read(real_ring.CommRing)),
					Rev(vec_space.SmulMul.Read(real_ring.CommRing))),
				By(Normalized, pRescaled, qRescaled))

			arg.Take(arg.TermAs[Fun[Nat, Real]]("«weightedMean»"))
			arg.Show(
				"the average is a point of s, and the combination stands at height a + b above it",
				By(inSet, atTotalHeight))
		}),
})}

// VanishingWeights — nonnegative weights totalling zero leave nothing
// of the combination they carry.
//
// All three hypotheses are spent at once and on the weights alone:
// together they say that every weight is zero. What is left is a
// statement about the fold — each of its terms is a point scaled by
// zero, hence the zero vector, which is the element pointwise addition
// folds from, and a fold whose terms are all that element is that
// element. The fold law asks for no finiteness of its own.
var VanishingWeights = vanishingWeightsThm{family.Add(registry.ProofEntry{
	Name: "VanishingWeights",
	Key:  "prop_5438b32d45626351",
	Build: family.Theorem(
		Statement{
			Binders: "∀k:set(num). ∀u:(num → real). ∀x:(num → num → real).",
			Hypotheses: []string{
				"finite(k)",
				"∀i:num. i ∈ k ⇒ &0 ≤ u(i)",
				"Σ_{i∈k} u(i) = &0",
			},
			Conclusion: "Σ_{i∈k} u(i) • x(i) = vec_zero",
		},
		func(a *Argument, k *Expr[Set[Nat]], u *Arrow[Nat, Real],
			x *Arrow[Nat, Fun[Nat, Real]], finite, nonneg, vanishes Fact) {
			// The one thing the fold mechanism asks of the vectors, read
			// at the real ring.
			vectors := vec_space.MonoidalVecAdd.Read(real_ring.CommRing)

			zeros := a.Have(
				"nonnegative weights that total zero are each zero",
				"∀i:num. i ∈ k ⇒ u(i) = &0",
				By(finite, nonneg, vanishes, real_sum.NonnegEqZero))
			silent := a.Have(
				"so every point of the family enters scaled by zero, contributing the zero vector",
				"∀i:num. i ∈ k ⇒ u(i) • x(i) = vec_zero",
				By(zeros, vec_space.ZeroSmul.Read(real_ring.CommRing)))

			// The two readings of the zero vector meet here: it is what
			// every term of the combination is, and it is the element
			// pointwise addition folds from.
			a.Show(
				"and a fold whose every term is the element it starts from is that element",
				By(vectors, silent, monoidal.EqNeutral, vec_space.NeutralVecAdd.Read(real_ring.CommRing)))
		}),
})}
