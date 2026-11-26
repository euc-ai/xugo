// riemann_roch.go — the Riemann–Roch theorem for the invertible pairs of
// a curve: ℓ(M) − dim Hom(M, ω) = deg M + 1 − g, from χ(M) = deg M + 1 − g
// (curve_degree.RiemannRochEuler) and Serre duality, with every number
// finite by algebraic_curve.InvertibleFinite; and its form for the pair of
// a divisor.

package serre_duality

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	"github.com/euc-ai/xugo/library/proofs/scheme/curve_degree"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// RiemannRoch — the Riemann–Roch theorem: for an invertible pair M of a curve,
// H⁰(M) and H¹(M) are finite-dimensional over k, so is Hom(M, ω), and ℓ(M) −
// dim Hom(M, ω) = deg M + 1 − g. An invertible pair has finite cohomology
// (algebraic_curve.InvertibleFinite); Serre duality makes Hom(M, ω) finite of
// the dimension of H¹(M), so the left side is ℓ(M) − dim H¹(M) = χ(M), which is
// deg M + 1 − g (curve_degree.RiemannRochEuler).
var RiemannRoch = riemannRochThm{family.Add(registry.ProofEntry{
	Name: "RiemannRoch",
	Key:  "prop_752558fd4f7686e7",
	Reading: "The curve may be singular: g is the arithmetic genus dim H¹(O), and ω the dualizing " +
		"pair, which at a singular point is not the sheaf of differentials. Invertibility of M is what " +
		"makes every number here finite (InvertibleFinite) and Serre duality's dimension count apply.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀M:prod(set(A), set(A)).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdInvertible»(M)",
		},
		Conclusion: "«wdFinite»(M) ∧ " +
			"finite_dimensional(«wdScalars», «wdDualizingMaps»(M)) ∧ " +
			"int_of_num(lattice_pair_h0_dim(«wcOverlap», k, «wcField», M)) - " +
			"int_of_num(module_dim(«wdScalars», «wdDualizingMaps»(M))) = " +
			"«wdDegree»(M) + &1 - «wdGenus»",
		Abbrev: Abbrev{
			{Name: "wdFinite", Text: "lattice_pair_finite(«wcOverlap», k, «wcField»)"},
		},
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			M *Expr[_LatticePair],
			given Fact,
		) {
			duality := a.Conjuncts(
				GroupPremises(given, SerreDuality.Read(L).At(k, A0, A1, A01, t, M)),
				"H¹(M) is finite-dimensional over k",
				"so is Hom(M, ω)",
				"and Hom(M, ω) has the dimension of H¹(M)")
			count := a.Have(
				"ℓ(M) − dim Hom(M, ω) is χ(M), which is deg M + 1 − g",
				"int_of_num(lattice_pair_h0_dim(«wcOverlap», k, «wcField», M)) - "+
					"int_of_num(module_dim(«wdScalars», «wdDualizingMaps»(M))) = "+
					"«wdDegree»(M) + &1 - «wdGenus»",
				CalcEq(
					Leg(
						a.TermAs[Int](
							"int_of_num(lattice_pair_h0_dim(«wcOverlap», k, «wcField», M)) - int_of_num(«wdH1Dim»(M))"),
						"by Serre duality Hom(M, ω) has the dimension of H¹(M)",
						By(duality[2])),
					Leg(
						a.TermAs[Int]("«wdEuler»(M)"),
						"which is χ(M), by its definition",
						Unfold(lattice_pair.LatticePairEulerDef)),
					FinalLeg(
						"and χ(M) = deg M + 1 − g",
						By(curve_degree.RiemannRochEuler.Read(L).At(k, A0, A1, A01, t, M), given)),
				))
			a.Show(
				"M has finite cohomology, Hom(M, ω) is finite-dimensional, and the count holds",
				By(algebraic_curve.InvertibleFinite.Read(L).At(k, A0, A1, A01, t, M), given, duality[1], count))
		}),
})}

// RiemannRochDivisor — Riemann–Roch for a divisor:
// ℓ(O(D)) − dim Hom(O(D), ω) = deg D + 1 − g. The pair O(D) of a divisor is
// invertible (curve_degree.DivisorLatticeInvertible), so Riemann–Roch holds at
// it, and its degree is the divisor's (curve_degree.DivisorLatticeDegree).
var RiemannRochDivisor = riemannRochDivisorThm{family.Add(registry.ProofEntry{
	Name: "RiemannRochDivisor",
	Key:  "prop_40d53cf27d9bf72d",
	Reading: "The degree on the right is the divisor's, Σ D(P) over its support: each " +
		"regular point counts once (DivisorLatticeDegree). Both dimensions on the left are " +
		"finite, by RiemannRoch at O(D), whose first two conjuncts this form does not restate. " +
		"The divisor is a curve_divisor, supported on the regular rational points of a curve " +
		"over the line that may be singular; smooth_curve_riemann_roch.RiemannRochClosedDivisors " +
		"states Riemann–Roch for the closed divisors of a smooth curve over a finite field.",
	Build: family.Theorem(Statement{
		Binders: "∀L:field_on(A). ∀k A₀ A₁ A₀₁:set(A). ∀t:A. ∀D:(prod(set(A), set(A)) → int).",
		Hypotheses: []string{
			"«wcDatum»",
			"«wdDivisor»(D)",
		},
		Conclusion: "int_of_num(lattice_pair_h0_dim(«wcOverlap», k, «wcField», «wdDivisorPair»(D))) - " +
			"int_of_num(module_dim(«wdScalars», «wdDualizingMaps»(«wdDivisorPair»(D)))) = " +
			"curve_divisor_degree(D) + &1 - «wdGenus»",
	},
		func(
			a *Argument,
			L field.FieldFact[on.L],
			k, A0, A1, A01 *Expr[Set[A]],
			t *Expr[A],
			D *Arrow[_LatticePair, Int],
			given Fact,
		) {
			divisorPair := a.TermAs[_LatticePair]("«wdDivisorPair»(D)")
			a.Show(
				"O(D) is invertible, so Riemann–Roch holds at it, and deg O(D) = deg D",
				By(
					given,
					curve_degree.DivisorLatticeInvertible.Read(L).At(k, A0, A1, A01, t, D),
					RiemannRoch.Read(L).At(k, A0, A1, A01, t, divisorPair),
					curve_degree.DivisorLatticeDegree.Read(L).At(k, A0, A1, A01, t, D)))
		}),
})}
