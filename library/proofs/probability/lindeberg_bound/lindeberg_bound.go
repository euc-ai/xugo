// lindeberg_bound.go — Lindeberg's bound along a row of martingale differences whose
// conditional variances sum to 1.

package lindeberg_bound

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/registry"
)

// MartingaleLindebergBound — Lindeberg's bound for a row of martingale differences whose
// conditional variances sum to 1: D(0) at the row's sum is integrable, and its expectation is
// within M₃·ε/6 + M₂·L + (M₃/3)·√(ε² + L) of the standard normal integral of D(0), L the
// Lindeberg sum at ε. It is MartingaleLindebergSmoothing at the clock 1: almost everywhere the
// row spends the whole clock, so the smoothing variable has scale 0 and the smoothed test is
// D(0) at the row's sum, while on the normal side the scale √1 is 1. D(0) grows at most
// quadratically (BoundedSecondDerivativeGrowth) and the row's sum is square-integrable
// (SquareIntegrableSum), which makes D(0) at it integrable.
var MartingaleLindebergBound = martingaleLindebergBoundThm{family.Add(registry.ProofEntry{
	Name: "MartingaleLindebergBound",
	Key:  "prop_b92b1ca879ad1b2b",
	Reading: "The row's conditional variances sum to exactly 1 almost everywhere. " +
		"For independent centred variables with the σ-algebras of the earlier ones as " +
		"filtration the v(k) are the variances, constants, and this is Lindeberg's bound.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀D:(num → real → real). " +
			"∀M₂ M₃ ε:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"martingale_difference_row(Ω, S, μ, F, n, ξ, v)",
			"measure_ae(Ω, S, μ, λx:A. real_sum({k:num | k < n}, λk:num. v(k, x)) = &1)",
			"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
			"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
			"&0 < ε",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. D(0)(real_sum({k:num | k < n}, λk:num. ξ(k, x)))) ∧ " +
			"|expectation(Ω, S, μ, λx:A. D(0)(real_sum({k:num | k < n}, λk:num. ξ(k, x)))) - " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), D(0))| ≤ " +
			"M₃ * ε / &6 + " +
			"M₂ * lindeberg_sum(Ω, S, μ, n, ξ, ε) + " +
			"M₃ / &3 * real_sqrt(real_pow(ε, 2) + lindeberg_sum(Ω, S, μ, n, ξ, ε))",
		Abbrev: Abbrev{
			{Name: "smoothed", Text: "λx:A. " +
				"    expectation(𝕌, " +
				"        borel_sets(real_topology), " +
				"        normal_distribution(&0, &1), " +
				"        λy:real. D(0)(Σ_{k<n} ξ(k, x) + real_sqrt(&1 - Σ_{k<n} v(k, x)) * y))"},
		},
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow[Nat, Set[Set[A]]],
			n *Expr[Nat],
			ξ, v *Arrow2[Nat, A, Real],
			D *Arrow2[Nat, Real, Real],
			M2, M3, ε *Expr[Real],
			probability, rows, varianceOne, tower, bounds, positive Fact,
		) {
			row := a.Conjuncts(
				a.Unfolded(rows, martingale.MartingaleDifferenceRowDef),
				"F is a filtration",
				"below n each increment is a martingale difference with conditional variance v")[1]
			one := a.TermAs[Real]("&1")
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			standard := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
			test := a.TermAs[Fun[Real, Real]]("D(0)")
			smoothed := a.TermAs[Fun[A, Real]]("«smoothed»")
			atSum := a.TermAs[Fun[A, Real]]("λx:A. D(0)(Σ_{k<n} ξ(k, x))")
			space := a.Have(
				"a probability is a measure on a σ-algebra",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
				By(
					probability,
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					measure_space.MeasureOn.At(Ω, S, μ)))
			unitScale := a.Have(
				"at the clock 1 the normal variable has scale √1 = 1",
				"(λy:real. D(0)(real_sqrt(&1) * y)) = D(0)",
				Funext(),
				ByArith(real_sqrt.SqrtUnique.At(one, one)))
			spent := a.Have(
				"where the conditional variances sum to 1 the smoothed test is D(0) at the row's sum",
				"∀x:A. x ∈ Ω ∧ Σ_{k<n} v(k, x) = &1 ⇒ «smoothed»(x) = D(0)(Σ_{k<n} ξ(k, x))",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					whole := b.Assume()
					left := b.Have(
						"nothing is left of the clock",
						"&1 - Σ_{k<n} v(k, x) = &0",
						ByArith(whole))
					scale := b.Have(
						"so the smoothing variable has scale 0",
						"real_sqrt(&1 - Σ_{k<n} v(k, x)) = &0",
						By(left, real_sqrt.SqrtZero))
					constant := b.Have(
						"and the test under the normal integral does not depend on y",
						"(λy:real. D(0)(Σ_{k<n} ξ(k, x) + real_sqrt(&1 - Σ_{k<n} v(k, x)) * y)) = "+
							"(λy:real. D(0)(Σ_{k<n} ξ(k, x)))",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[Real]("y")
							c.Show(
								"the scale is 0",
								ByArith(scale))
						}))
					b.Show(
						"a constant integrates to itself against the standard normal distribution",
						By(
							constant,
							probability_space.ExpectationConstant.At(
								line, borel, standard, b.TermAs[Real]("D(0)(Σ_{k<n} ξ(k, x))")),
							normal_distribution.NormalDistributionProbability.At(b.TermAs[Real]("&0"), one)))
				}))
			almostEverywhere := a.Have(
				"so almost everywhere the smoothed test is D(0) at the row's sum",
				"measure_ae_eq(Ω, S, μ, «smoothed», λx:A. D(0)(Σ_{k<n} ξ(k, x)))",
				By(
					spent,
					varianceOne,
					measure_space.AEEqualDef.At(Ω, S, μ, smoothed, atSum),
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. Σ_{k<n} v(k, x) = &1"),
						a.TermAs[Set[A]]("λx:A. «smoothed»(x) = D(0)(Σ_{k<n} ξ(k, x))"))))
			sameExpectation := a.Have(
				"and the two have one expectation",
				"expectation(Ω, S, μ, «smoothed») = expectation(Ω, S, μ, λx:A. D(0)(Σ_{k<n} ξ(k, x)))",
				By(
					space,
					almostEverywhere,
					measure_integral.IntegralAE.At(Ω, S, μ, smoothed, atSum),
					probability_space.ExpectationDef))
			atMostOne := a.Have(
				"a sum equal to 1 is at most 1",
				"∀x:A. x ∈ Ω ∧ Σ_{k<n} v(k, x) = &1 ⇒ Σ_{k<n} v(k, x) ≤ &1",
				ByArith())
			clock := a.Have(
				"the conditional variances sum to at most 1 almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. Σ_{k<n} v(k, x) ≤ &1)",
				By(atMostOne, varianceOne, measure_space.AEMono))
			smoothing := a.Have(
				"MartingaleLindebergSmoothing at the clock 1",
				"|expectation(Ω, S, μ, «smoothed») - "+
					"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. D(0)(real_sqrt(&1) * y))| ≤ "+
					"M₃ * ε / &6 * &1 + "+
					"M₂ * lindeberg_sum(Ω, S, μ, n, ξ, ε) + "+
					"M₃ / &3 * &1 * real_sqrt(real_pow(ε, 2) + lindeberg_sum(Ω, S, μ, n, ξ, ε))",
				By(
					probability,
					rows,
					clock,
					tower,
					bounds,
					positive,
					MartingaleLindebergSmoothing.At(Ω, S, μ, F, n, ξ, v, D, one, M2, M3, ε)))
			integrable := a.Have(
				"D(0) at the row's sum is integrable",
				"real_integrable(Ω, S, μ, λx:A. D(0)(Σ_{k<n} ξ(k, x)))",
				Derive(func(b *Argument) {
					K, growth := b.ObtainAs[Real](
						"D(0) grows at most quadratically",
						"∃K:real. &0 ≤ K ∧ (∀z:real. |D(0)(z)| ≤ K * (&1 + z * z) ∧ |D(1)(z)| ≤ K * (&1 + |z|))",
						By(
							tower,
							bounds,
							real_derivative.BoundedSecondDerivativeGrowth.At(
								test, b.TermAs[Fun[Real, Real]]("D(1)"), b.TermAs[Fun[Real, Real]]("D(2)"), M2)))
					terms := b.Have(
						"each ξ(k) is measurable and square-integrable, as "+
							"the integrands of its conditional expectations are",
						"∀k:num. k < n ⇒ real_measurable(Ω, S, ξ(k)) ∧ real_integrable(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]("k")
							below := c.Assume()
							c.Show(
								"the conditional mean and the conditional variance of ξ(k)",
								By(
									At(row, k),
									below,
									conditional_expectation.IsCondExpDef.At(
										Ω,
										S,
										μ,
										c.TermAs[Set[Set[A]]]("F(k)"),
										c.TermAs[Fun[A, Real]]("ξ(k)"),
										c.TermAs[Fun[A, Real]]("λx:A. &0")),
									conditional_expectation.IsCondExpDef.At(
										Ω,
										S,
										μ,
										c.TermAs[Set[Set[A]]]("F(k)"),
										c.TermAs[Fun[A, Real]]("λx:A. ξ(k, x) * ξ(k, x)"),
										c.TermAs[Fun[A, Real]]("v(k)")),
									measure_integral.RealIntegrableDef.At(Ω, S, μ, c.TermAs[Fun[A, Real]]("ξ(k)"))))
						}))
					rowSum := b.Have(
						"the row's sum is measurable and square-integrable",
						"real_measurable(Ω, S, λx:A. Σ_{k<n} ξ(k, x)) ∧ "+
							"real_integrable(Ω, S, μ, λx:A. (Σ_{k<n} ξ(k, x)) * Σ_{k<n} ξ(k, x))",
						By(terms, space, measure_integral.SquareIntegrableSum.At(Ω, S, μ, ξ, n)))
					derivative := b.Have(
						"D(1) is the derivative of D(0) on the line",
						"∀y:real. y ∈ 𝕌 ⇒ real_derivative_at(D(0), y, D(1)(y))",
						By(tower))
					testBorel := b.Have(
						"D(0) is differentiable, hence continuous and Borel",
						"real_measurable(𝕌, borel_sets(real_topology), D(0))",
						By(
							derivative,
							real_derivative.DerivativeContinuousOn.At(test, b.TermAs[Fun[Real, Real]]("D(1)"), line),
							borel_function.ContinuousBorelMeasurable.At(test)))
					majorant := b.Have(
						"K·(1 + s²) is integrable, s the row's sum",
						"real_integrable(Ω, S, μ, λx:A. K * (&1 + (Σ_{k<n} ξ(k, x)) * Σ_{k<n} ξ(k, x)))",
						By(
							rowSum,
							probability,
							space,
							probability_space.ExpectationConstant.At(Ω, S, μ, one),
							measure_integral.IntegrableAdd.At(
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("λx:A. &1"),
								b.TermAs[Fun[A, Real]]("λx:A. (Σ_{k<n} ξ(k, x)) * Σ_{k<n} ξ(k, x)")),
							measure_integral.IntegrableScale.At(
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("λx:A. &1 + (Σ_{k<n} ξ(k, x)) * Σ_{k<n} ξ(k, x)"),
								K)))
					b.Show(
						"D(0) at the row's sum is measurable and dominated by K·(1 + s²)",
						By(
							growth,
							rowSum,
							testBorel,
							majorant,
							borel_function.RealMeasurableCompose.At(
								Ω, S, b.TermAs[Fun[A, Real]]("λx:A. Σ_{k<n} ξ(k, x)"), test),
							measure_integral.IntegrableDominated.At(
								Ω,
								S,
								μ,
								atSum,
								b.TermAs[Fun[A, Real]]("λx:A. K * (&1 + (Σ_{k<n} ξ(k, x)) * Σ_{k<n} ξ(k, x))"))))
				}))
			a.Show(
				"the bound at the clock 1, the smoothed test replaced by D(0) at the row's sum",
				ByArith(unitScale, sameExpectation, smoothing, integrable))
		}),
})}
