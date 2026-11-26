// distribution_function.go — distribution functions under weak convergence: at every point the
// limit gives no mass, the masses of the half-lines converge.

package weak_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// WeakConvergenceDistributionFunction — when probabilities ν(n) on the line converge weakly to ρ,
// the mass ν(n) gives a half-line {y ≤ t} tends to the mass ρ gives it, at every t to which ρ
// gives no mass. For a < b the ramp falling from height b − a at a to 0 at b lies between b − a
// times the indicators of {y ≤ a} and {y ≤ b}; that height gives it slope 1, so it is b − y
// clamped to [0, b − a] and nonexpansive at once, and the convergence of its integrals within
// (b − a)e, divided by b − a, holds each measure's mass at a below the other's at b plus e. ρ's
// distribution function is continuous at t: from the right as every distribution function is, and
// from the left because t is null.
var WeakConvergenceDistributionFunction = weakConvergenceDistributionFunctionThm{family.Add(registry.ProofEntry{
	Name: "WeakConvergenceDistributionFunction",
	Key:  "prop_ee063a9bca9f165e",
	Reading: "ρ({t}) = 0 is load-bearing: at an atom of the limit the masses of {y ≤ t} " +
		"need not converge. The masses are probabilities, so reading them as reals loses nothing.",
	Build: family.Sections(Statement{
		Binders: "∀ν:(num → set(real) → extended_nonneg_real). " +
			"∀ρ:(set(real) → extended_nonneg_real). " +
			"∀t:real.",
		Hypotheses: []string{
			"weakly_converges(real_topology, ν, ρ)",
			"ρ({t}) = extended_of_real(&0)",
		},
		Conclusion: "(λn:num. extended_to_real(ν(n, {y:real | y ≤ t}))) ⟶ " +
			"extended_to_real(ρ({y:real | y ≤ t}))",
		Abbrev: Abbrev{
			{Name: "ramp", Text: "λa:real. λb:real. λy:real. max(&0, min(b - a, b - y))"},
			{Name: "rampIntegral", Text: "λμ:(set(real) → extended_nonneg_real). λa:real. λb:real. " +
				"    «lineIntegral»(μ, λy:real. «ramp»(a, b, y))"},
			{Name: "distributionFunction", Text: "λμ:(set(real) → extended_nonneg_real). λs:real. " +
				"    extended_to_real(μ({y:real | y ≤ s}))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			rampValues := ctx.Lemma(Statement{
				Binders: "∀a b y:real.",
				Hypotheses: []string{
					"a ≤ b",
				},
				Conclusion: "COND(y ≤ a, b - a, &0) ≤ «ramp»(a, b, y) ∧ " +
					"«ramp»(a, b, y) ≤ COND(y ≤ b, b - a, &0) ∧ " +
					"|«ramp»(a, b, y)| ≤ b - a",
			},
				func(arg *Argument, a, b, y *Expr[Real], ordered Fact) {
					zero := arg.TermAs[Real]("&0")
					height := arg.TermAs[Real]("b - a")
					gap := arg.TermAs[Real]("b - y")
					arg.Show(
						"b − y clamped to [0, b − a] is b − a for y ≤ a, 0 for y ≥ b, and in [0, b − a] between",
						ByArith(
							ordered,
							real_sup_inf.ClampRange.At(zero, height, gap),
							real_sup_inf.ClampEnds.At(zero, height, gap)),
					)
				})

			rampContinuous := ctx.Lemma("∀a b:real. real_continuous_on(𝕌, λy:real. «ramp»(a, b, y))",
				func(arg *Argument, a, b *Expr[Real]) {
					ramp := arg.TermAs[Fun[Real, Real]]("λy:real. «ramp»(a, b, y)")
					nonexpansive := arg.Have(
						"the ramp clamps b − y to [0, b − a], so it moves no two points further apart",
						"∀x y:real. |«ramp»(a, b, x) - «ramp»(a, b, y)| ≤ |x - y|",
						Derive(func(c *Argument) {
							c.FixAs[Real]("x")
							c.FixAs[Real]("y")
							c.Show(
								"clamping is nonexpansive, and b − x and b − y are |x − y| apart",
								ByArith(real_sup_inf.ClampNonexpansive.At(
									c.TermAs[Real]("&0"),
									c.TermAs[Real]("b - a"),
									c.TermAs[Real]("b - x"),
									c.TermAs[Real]("b - y"))),
							)
						}),
					)
					arg.Show(
						"so the ramp is uniformly continuous, hence continuous",
						By(
							nonexpansive,
							real_continuous.NonexpansiveUniformlyContinuous.At(ramp),
							real_continuous.UniformlyContinuousContinuous.At(ramp, arg.TermAs[Set[Real]]("𝕌"))),
					)
				})

			rampMasses := ctx.Lemma(Statement{
				Binders: "∀μ:(set(real) → extended_nonneg_real). ∀a b:real.",
				Hypotheses: []string{
					"«lineProbability»(μ)",
					"a ≤ b",
				},
				Conclusion: "(b - a) * «distributionFunction»(μ, a) ≤ «rampIntegral»(μ, a, b) ∧ " +
					"«rampIntegral»(μ, a, b) ≤ (b - a) * «distributionFunction»(μ, b)",
			},
				func(
					arg *Argument,
					μ *Arrow[Set[Real], ExtendedNonnegReal],
					a, b *Expr[Real],
					probability, ordered Fact,
				) {
					line := arg.TermAs[Set[Real]]("𝕌")
					borelSets := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					ramp := arg.TermAs[Fun[Real, Real]]("λy:real. «ramp»(a, b, y)")
					height := arg.TermAs[Real]("b - a")
					lowerRay := arg.TermAs[Set[Real]]("{y:real | y ≤ a}")
					upperRay := arg.TermAs[Set[Real]]("{y:real | y ≤ b}")
					lowerIndicator := arg.TermAs[Fun[Real, Real]]("λx:real. COND(x ∈ {y:real | y ≤ a}, b - a, &0)")
					upperIndicator := arg.TermAs[Fun[Real, Real]]("λx:real. COND(x ∈ {y:real | y ≤ b}, b - a, &0)")
					integrable := arg.Have(
						"continuous, hence Borel measurable, and bounded by "+
							"b − a, the ramp is integrable against a probability",
						"«lineIntegrable»(μ, λy:real. «ramp»(a, b, y))",
						By(
							ordered,
							probability,
							At(rampContinuous, a, b),
							borel_function.ContinuousBorelMeasurable.At(ramp),
							rampValues,
							probability_space.BoundedIntegrable.At(line, borelSets, μ, ramp, height)),
					)
					above := arg.Have(
						"the ramp lies above b − a times the indicator of {y ≤ a}",
						"∀x:real. x ∈ 𝕌 ⇒ COND(x ∈ {y:real | y ≤ a}, b - a, &0) ≤ «ramp»(a, b, x)",
						By(ordered, rampValues),
					)
					below := arg.Have(
						"and below b − a times the indicator of {y ≤ b}",
						"∀x:real. x ∈ 𝕌 ⇒ «ramp»(a, b, x) ≤ COND(x ∈ {y:real | y ≤ b}, b - a, &0)",
						By(ordered, rampValues),
					)
					lower := arg.Have(
						"so its integral is at least b − a times the mass of {y ≤ a}",
						"(b - a) * «distributionFunction»(μ, a) ≤ «rampIntegral»(μ, a, b)",
						By(
							probability,
							integrable,
							above,
							borel_function.RaysBorel.At(a),
							probability_space.ExpectationIndicator.At(line, borelSets, μ, lowerRay, height),
							probability_space.ExpectationDef.At(line, borelSets, μ, lowerIndicator),
							measure_integral.IntegralMono.At(line, borelSets, μ, lowerIndicator, ramp)),
					)
					upper := arg.Have(
						"and at most b − a times the mass of {y ≤ b}",
						"«rampIntegral»(μ, a, b) ≤ (b - a) * «distributionFunction»(μ, b)",
						By(
							probability,
							integrable,
							below,
							borel_function.RaysBorel.At(b),
							probability_space.ExpectationIndicator.At(line, borelSets, μ, upperRay, height),
							probability_space.ExpectationDef.At(line, borelSets, μ, upperIndicator),
							measure_integral.IntegralMono.At(line, borelSets, μ, ramp, upperIndicator)),
					)
					arg.Show(
						"the ramp's integral lies between the two scaled masses",
						By(lower, upper),
					)
				})

			rampSandwich := ctx.Lemma(Statement{
				Binders: "∀ν:(num → set(real) → extended_nonneg_real). " +
					"∀ρ:(set(real) → extended_nonneg_real). " +
					"∀a b e:real.",
				Hypotheses: []string{
					"weakly_converges(real_topology, ν, ρ)",
					"a < b",
					"&0 < e",
				},
				Conclusion: "∃N:num. ∀n:num. " +
					"    N ≤ n ⇒ " +
					"    «distributionFunction»(ν(n), a) < «distributionFunction»(ρ, b) + e ∧ " +
					"    «distributionFunction»(ρ, a) < «distributionFunction»(ν(n), b) + e",
			},
				func(
					arg *Argument,
					ν *Arrow2[Nat, Set[Real], ExtendedNonnegReal],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					a, b, e *Expr[Real],
					weak, ordered, pos Fact,
				) {
					parts := arg.Conjuncts(
						arg.Unfolded(weak, WeaklyConvergesDef),
						"the ν(n) are probabilities on the Borel sets of the line",
						"so is ρ",
						"and the integrals of every bounded continuous test converge")
					atMost := arg.Have(
						"in particular a ≤ b, all the ramp's bounds need",
						"a ≤ b",
						ByArith(ordered),
					)
					ramp := arg.TermAs[Fun[Real, Real]]("λy:real. «ramp»(a, b, y)")
					continuous := arg.Have(
						"the ramp is a continuous map of the line",
						"continuous_map(real_topology, real_topology, λy:real. «ramp»(a, b, y))",
						By(At(rampContinuous, a, b), real_continuous.ContinuousOnUnivIffMap.At(ramp)),
					)
					bounded := arg.Have(
						"bounded by b − a",
						"∃B:real. ∀x:real. x ∈ ⋃real_topology ⇒ |«ramp»(a, b, x)| ≤ B",
						Witness(arg.TermAs[Real]("b - a")),
						By(atMost, rampValues),
					)
					converges := arg.Have(
						"so its integrals converge",
						"(λn:num. «rampIntegral»(ν(n), a, b)) ⟶ «rampIntegral»(ρ, a, b)",
						By(parts[2], continuous, bounded, real_topology.RealSpace),
					)
					tolerance := arg.Have(
						"(b − a)e is positive",
						"&0 < (b - a) * e",
						ByArith(ordered, pos),
					)
					N, tail := arg.ObtainAs[Nat](
						"from some index N on they are within (b − a)e of their limit",
						"∃N:num. ∀n:num. N ≤ n ⇒ |«rampIntegral»(ν(n), a, b) - «rampIntegral»(ρ, a, b)| < (b - a) * e",
						By(
							converges,
							tolerance,
							real_sequences.RealConvergesToDef.At(
								arg.TermAs[Fun[Nat, Real]]("λn:num. «rampIntegral»(ν(n), a, b)"),
								arg.TermAs[Real]("«rampIntegral»(ρ, a, b)"))),
					)
					probabilities := arg.Have(
						"the ν(n) and ρ are probabilities on the line",
						"(∀n:num. «lineProbability»(ν(n))) ∧ «lineProbability»(ρ)",
						By(parts[0], parts[1], real_topology.RealSpace),
					)
					arg.Show(
						"past N the ramp's integrals pin each measure's mass at a below the other's at b",
						Witness(N),
						Derive(func(c *Argument) {
							c.FixAs[Nat]("n")
							late := c.Assume()
							gap := c.Have(
								"the ramp's integrals under ν(n) and ρ are within (b − a)e",
								"|«rampIntegral»(ν(n), a, b) - «rampIntegral»(ρ, a, b)| < (b - a) * e",
								By(tail, late),
							)
							underNu := c.Have(
								"under ν(n) the ramp's integral lies between b − a times the masses at a and b",
								"(b - a) * «distributionFunction»(ν(n), a) ≤ «rampIntegral»(ν(n), a, b) ∧ "+
									"«rampIntegral»(ν(n), a, b) ≤ (b - a) * «distributionFunction»(ν(n), b)",
								By(
									probabilities,
									atMost,
									At(rampMasses, c.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("ν(n)"), a, b)),
							)
							underRho := c.Have(
								"and so it does under ρ",
								"(b - a) * «distributionFunction»(ρ, a) ≤ «rampIntegral»(ρ, a, b) ∧ "+
									"«rampIntegral»(ρ, a, b) ≤ (b - a) * «distributionFunction»(ρ, b)",
								By(probabilities, atMost, At(rampMasses, ρ, a, b)),
							)
							c.Show(
								"dividing by b − a, each mass at a is below the other's at b plus e",
								ByArith(ordered, gap, underRho, underNu),
							)
						}),
					)
				})

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					ν *Arrow2[Nat, Set[Real], ExtendedNonnegReal],
					ρ *Arrow[Set[Real], ExtendedNonnegReal],
					t *Expr[Real],
					weak, atomless Fact,
				) {
					probability := arg.Have(
						"the limit ρ is a probability on the line",
						"«lineProbability»(ρ)",
						By(
							weak,
							WeaklyConvergesDef.At(arg.TermAs[Set[Set[Real]]]("real_topology"), ν, ρ),
							real_topology.RealSpace),
					)
					eventually := arg.Have(
						"for every ε > 0, from some index on the masses of {y ≤ t} are within ε of their limit",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀n:num. " +
								"    N ≤ n ⇒ |«distributionFunction»(ν(n), t) - «distributionFunction»(ρ, t)| < ε",
						},
						Derive(func(c *Argument) {
							c.FixAs[Real]("ε")
							pos := c.Assume()
							half := c.Have(
								"ε/2 is positive",
								"&0 < ε / &2",
								ByArith(pos),
							)
							margin := c.TermAs[Real]("ε / &2")
							b, rightMass := c.ObtainAs[Real](
								"right of t, some b where ρ's mass is within ε/2 of its mass at t",
								"∃b:real. t < b ∧ «distributionFunction»(ρ, b) < «distributionFunction»(ρ, t) + ε / &2",
								By(probability, half, random_variable.DistributionFunctionRightContinuous.At(ρ, t, margin)),
							)
							a, leftMass := c.ObtainAs[Real](
								"left of t, some a where it is within ε/2 too, t being null",
								"∃a:real. a < t ∧ «distributionFunction»(ρ, t) < «distributionFunction»(ρ, a) + ε / &2",
								By(
									probability,
									atomless,
									half,
									random_variable.DistributionFunctionLeftContinuousAtNull.At(ρ, t, margin)),
							)
							_, upper := c.ObtainAs[Nat](
								"the ramp from t to b bounds ν(n)'s mass at t by ρ's at b, from some index on",
								"∃N:num. ∀n:num. "+
									"    N ≤ n ⇒ "+
									"    «distributionFunction»(ν(n), t) < «distributionFunction»(ρ, b) + ε / &2 ∧ "+
									"    «distributionFunction»(ρ, t) < «distributionFunction»(ν(n), b) + ε / &2",
								By(weak, rightMass, half, At(rampSandwich, ν, ρ, t, b, margin)),
							)
							_, lower := c.ObtainAs[Nat](
								"the ramp from a to t bounds it below by ρ's mass at a, from some index on",
								"∃M:num. ∀n:num. "+
									"    M ≤ n ⇒ "+
									"    «distributionFunction»(ν(n), a) < «distributionFunction»(ρ, t) + ε / &2 ∧ "+
									"    «distributionFunction»(ρ, a) < «distributionFunction»(ν(n), t) + ε / &2",
								By(weak, leftMass, half, At(rampSandwich, ν, ρ, a, t, margin)),
							)
							c.Show(
								"past both indices the mass at t is within ε of ρ's",
								Witness(c.TermAs[Nat]("N + M")),
								Derive(func(d *Argument) {
									n := d.FixAs[Nat]()
									late := d.Assume()
									d.Show(
										"the two sandwiches and the choices of a and b",
										ByArith(lower.At(n), upper.At(n), late, leftMass, rightMass),
									)
								}),
							)
						}),
					)
					arg.Show(
						"which is the convergence of the masses",
						By(
							eventually,
							real_sequences.RealConvergesToDef.At(
								arg.TermAs[Fun[Nat, Real]]("λn:num. «distributionFunction»(ν(n), t)"),
								arg.TermAs[Real]("«distributionFunction»(ρ, t)"))),
					)
				})
		}),
})}
