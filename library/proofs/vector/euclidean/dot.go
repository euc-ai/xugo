// dot.go — the form at ℝ: the bridge to Σ, and what the order adds.
//
// `⟪u, v⟫_n` is `Σ_{i<n} u(i) * v(i)` by the two definitions, and the
// bridge states it once so that the Σ chapter's order theory reaches
// the form. What ℝ adds is
// positivity — every summand of `dot(u, u)` is a square — and its
// consequence on the active range: a vector null for the form has
// every active entry zero, so it is orthogonal to everything. On a
// dimension that is definiteness: an n-vector null against itself is
// the zero vector.

package euclidean

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/vector/dot"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// DotIsSum — the form at ℝ is the Σ of the pointwise products: the two
// definitions name the same fold.
var DotIsSum = dotIsSumThm{family.Add(registry.ProofEntry{
	Name: "DotIsSum",
	Key:  "prop_b278cf815891bc45",
	Build: family.Theorem("∀n:num. ∀u v:(num → real). ⟪u, v⟫_n = Σ_{i<n} u(i) * v(i)",
		func(a *Argument, n, u, v Term) {
			a.Do(Unfold(dot.DotDef), Unfold(real_sum.RealSumDef))
		}),
})}

// DotPosLe — the form is positive semidefinite: every summand of
// `dot(u, u)` is a square, and a sum of nonnegative terms is nonnegative.
var DotPosLe = dotPosLeThm{family.Add(registry.ProofEntry{
	Name: "DotPosLe",
	Key:  "prop_75310cd680e41fd0",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num. ∀u:(num → real).",
		Conclusion: "&0 ≤ ⟪u, u⟫_n",
	},
		func(a *Argument, n, u Term) {
			squares := a.Have(
				"every summand is a square — stated over the range, the shape the sum's positivity law reads",
				"∀i:num. i ∈ «activeRange» ⇒ &0 ≤ u(i) * u(i)",
				By(real_order_ring.SquareNonneg))
			asSum := a.Have(
				"the form is the sum of those squares",
				"⟪u, u⟫_n = Σ_{i<n} u(i) * u(i)",
				Cite(DotIsSum))
			a.Show(
				"and a sum of nonnegative terms is nonnegative",
				asSum.Rw(),
				By(squares, real_sum.Nonneg))
		}),
})}

// NullVectorOrthogonal — a vector null for the form is orthogonal to
// every vector. `dot(u, u)` is the sum of the squares u(i)·u(i) over the
// range, and those are nonnegative: when the sum vanishes every square
// does, so every entry does, and with it every product u(i)·v(i) — a
// sum of vanishing terms.
var NullVectorOrthogonal = nullVectorOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "NullVectorOrthogonal",
	Key:  "prop_c2c69d77c429607d",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u v:(num → real).",
		Hypotheses: []string{
			"⟪u, u⟫_n = &0",
		},
		Conclusion: "⟪u, v⟫_n = &0",
	},
		func(a *Argument, n, u, v Term) {
			// Both forms read as sums over the range; the hypothesis is
			// then that the sum of squares vanishes.
			a.Do(Simp(Fwd(DotIsSum)))
			sumOfSquares := a.Assume()
			squares := a.Have(
				"every summand of dot(u, u) is a square, hence nonnegative",
				"∀i:num. i ∈ «activeRange» ⇒ &0 ≤ u(i) * u(i)",
				By(real_order_ring.SquareNonneg))
			squaresVanish := a.Have(
				"a vanishing sum of nonnegative terms has every term zero",
				"∀i:num. i ∈ «activeRange» ⇒ u(i) * u(i) = &0",
				By(
					At(num_segment.FiniteBelowStrict, n),
					squares,
					sumOfSquares,
					Where(real_sum.NonnegEqZero, "f", a.Term("λi:num. u(i) * u(i)"))))
			entriesVanish := a.Have(
				"and a zero square has a zero base",
				"∀i:num. i ∈ «activeRange» ⇒ u(i) = &0",
				By(Normalized, squaresVanish, real_ring.MulEqZero))
			productsVanish := a.Have(
				"so every product u(i)·v(i) vanishes on the range",
				"∀i:num. i ∈ «activeRange» ⇒ u(i) * v(i) = &0",
				By(entriesVanish, real_ring.MulLeftZero))
			a.Show(
				"and a sum of vanishing terms vanishes",
				By(productsVanish, real_sum.EqZero))
		}),
})}

// DotEqZero — on a dimension the form is DEFINITE: the zero vector is
// the only null n-vector. What definiteness asks of ℝ is that a null
// vector be orthogonal to everything — the form's positivity, through
// NullVectorOrthogonal — and the generic law does the rest.
var DotEqZero = dotEqZeroThm{family.Add(registry.ProofEntry{
	Name: "DotEqZero",
	Key:  "prop_8e0290b8c467fe68",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀u:(num → real).",
		Hypotheses: []string{
			"vec⟨n⟩(u)",
		},
		Conclusion: "⟪u, u⟫_n = &0 ⇔ u = vec_zero",
	},
		func(a *Argument, n *Expr[Nat], u *Vec[Real, DimN], member Fact) {
			nullOrthogonal := a.Have(
				"a null vector is orthogonal to everything — the one thing definiteness asks of ℝ",
				"∀v w:(num → real). ⟪v, v⟫_n = &0 ⇒ ⟪v, w⟫_n = &0",
				By(NullVectorOrthogonal))
			a.Show(
				"and the generic law does the rest",
				By(nullOrthogonal, dot.Definite.Read(real_ring.CommRing).At(proof.Inhabit(u, member))))
		}),
})}
