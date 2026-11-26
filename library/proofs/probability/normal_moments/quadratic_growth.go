package normal_moments

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

// NormalQuadraticGrowthIntegrable uses the finite second moment to integrate
// a measurable function bounded in absolute value by a quadratic.
var NormalQuadraticGrowthIntegrable = normalQuadraticGrowthIntegrableThm{family.Add(registry.ProofEntry{
	Name: "NormalQuadraticGrowthIntegrable",
	Key:  "prop_eb98fc4300d6bc91",
	Build: family.Theorem(Statement{
		Binders: "∀m v K:real. ∀h:(real → real).",
		Hypotheses: []string{
			"&0 < v",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
			"∀y:real. |h(y)| ≤ K * (&1 + y * y)",
		},
		Conclusion: "real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), h)",
	}, func(a *Argument, m, v, K *Expr[Real], h *Arrow[Real, Real], positive, measurable, bound Fact) {
		line := a.TermAs[Set[Real]]("𝕌")
		borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
		law := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]](
			"normal_distribution(m, v)")
		one := a.TermAs[Real]("&1")
		constant := a.TermAs[Fun[Real, Real]]("λy:real. &1")
		square := a.TermAs[Fun[Real, Real]]("λy:real. y * y")
		quadratic := a.TermAs[Fun[Real, Real]]("λy:real. &1 + y * y")
		majorant := a.TermAs[Fun[Real, Real]]("λy:real. K * (&1 + y * y)")

		probability := a.Have(
			"the normal law is a probability measure",
			"probability_on(𝕌, borel_sets(real_topology), normal_distribution(m, v))",
			By(positive, normal_distribution.NormalDistributionProbability.At(m, v)))
		measure := a.Have(
			"the measure property of the normal law",
			"measure_on(𝕌, borel_sets(real_topology), normal_distribution(m, v))",
			By(probability, probability_space.ProbabilityOnDef.At(line, borel, law)))
		oneIntegrable := a.Have(
			"the constant one is integrable on a probability space",
			"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), λy:real. &1)",
			By(probability, probability_space.ExpectationConstant.At(line, borel, law, one)))
		squareIntegrable := a.Have(
			"the normal law has a finite second moment",
			"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), λy:real. y * y)",
			By(positive, NormalDistributionMoments.At(m, v)))
		quadraticIntegrable := a.Have(
			"one plus the square is integrable",
			"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(m, v), λy:real. &1 + y * y)",
			By(
				measure,
				oneIntegrable,
				squareIntegrable,
				measure_integral.IntegrableAdd.At(line, borel, law, constant, square)))
		majorantIntegrable := a.Have(
			"scaling preserves integrability of the majorant",
			"real_integrable(𝕌, "+
				"    borel_sets(real_topology), "+
				"    normal_distribution(m, v), "+
				"    λy:real. K * (&1 + y * y))",
			By(
				measure,
				quadraticIntegrable,
				measure_integral.IntegrableScale.At(line, borel, law, quadratic, K)))
		a.Show(
			"the integrable majorant bounds the absolute value of h",
			By(
				measurable,
				bound,
				majorantIntegrable,
				measure_integral.IntegrableDominated.At(line, borel, law, h, majorant)))
	}),
})}
