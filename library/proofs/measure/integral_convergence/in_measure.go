// in_measure.go — convergence in measure read at the real values of the
// masses.

package integral_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

// ConvergesInMeasureDeviationMass — when V(n) converges in measure to Z,
// the real mass of the set where V(n) lies farther than δ from Z is
// eventually at most any ρ > 0: the definition bounds the mass by the finite
// value extended_of_real(ρ), so the mass is finite and its real value is at
// most ρ.
var ConvergesInMeasureDeviationMass = convergesInMeasureDeviationMassThm{family.Add(registry.ProofEntry{
	Name: "ConvergesInMeasureDeviationMass",
	Key:  "prop_c6a14cb40b3c08ba",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:(num → A → real). " +
			"∀Z:(A → real). " +
			"∀δ ρ:real.",
		Hypotheses: []string{"converges_in_measure(Ω, μ, V, Z)", "&0 < δ", "&0 < ρ"},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ extended_to_real(μ(«deviationEvent»(n))) ≤ ρ",
		Abbrev: Abbrev{
			{Name: "deviationEvent", Text: "λn:num. {x:A | x ∈ Ω ∧ δ < |V(n, x) - Z(x)|}"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], μ *Arrow[Set[A], ExtendedNonnegReal],
		V *Arrow2[Nat, A, Real], Z *Arrow[A, Real], δ, ρ *Expr[Real], assumptions Fact) {
		N, tail := a.ObtainAs[Nat](
			"convergence in measure bounds the extended mass",
			"∃N:num. ∀n:num. N ≤ n ⇒ μ(«deviationEvent»(n)) ≤ extended_of_real(ρ)",
			By(assumptions, ConvergesInMeasureDef.At(Ω, μ, V, Z)))
		a.Take(N)
		n := a.FixAs[Nat]()
		beyond := a.Assume()
		a.Show(
			"the finite upper bound passes to real mass",
			ByArith(
				beyond,
				tail.At(n),
				assumptions,
				extended_nonneg_real.ExtendedLeDef.At(
					a.TermAs[ExtendedNonnegReal]("μ(«deviationEvent»(n))"),
					a.TermAs[ExtendedNonnegReal]("extended_of_real(ρ)")),
				extended_nonneg_real.OfRealNotInfinity.At(ρ),
				extended_nonneg_real.ToRealOfReal.At(ρ)))
	}),
})}
