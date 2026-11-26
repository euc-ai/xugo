package normal_distribution

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/density_measure"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/weak_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_measure"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// StandardNormalDistributionFunctionLimit — measures converging weakly to the
// standard normal distribution have distribution functions converging to its
// distribution function at every point. Weak convergence carries the masses
// of {y | y ≤ t} across at every t the limit gives no mass, and the standard
// normal gives no point mass: a point is Lebesgue null, so the density cut to
// it vanishes almost everywhere and integrates to 0.
var StandardNormalDistributionFunctionLimit = standardNormalDistributionFunctionLimitThm{family.Add(registry.ProofEntry{
	Name: "StandardNormalDistributionFunctionLimit",
	Key:  "prop_ae9ed38d274f695c",
	Build: family.Sections(Statement{
		Binders: "∀ν:(num → set(real) → extended_nonneg_real). ∀t:real.",
		Hypotheses: []string{
			"weakly_converges(real_topology, ν, normal_distribution(&0, &1))",
		},
		Conclusion: "(λn:num. extended_to_real(ν(n, {y:real | y ≤ t}))) ⟶ " +
			"extended_to_real(normal_distribution(&0, &1, {y:real | y ≤ t}))",
		Abbrev: Abbrev{
			{Name: "lebesgueSets", Text: "{E:set(real) | lebesgue_measurable(E)}"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		noAtom := ctx.Lemma("∀t:real. normal_distribution(&0, &1, {t}) = &0",
			func(a *Argument, t *Expr[Real]) {
				line := a.TermAs[Set[Real]]("𝕌")
				lebesgue := a.TermAs[Set[Set[Real]]]("«lebesgueSets»")
				μ := a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("lebesgue_outer_measure")
				point := a.Have(
					"a point is the closed interval from it to itself",
					"{t} = ⟦t, t⟧",
					Simp(Fwd(set_basic.Extension)),
					a.ForEach(func(x *Expr[Real]) Action {
						return ByArith(real_topology.ClosedIntervalMembership.At(x, t, t), set_basic.InSing.At(x, t))
					}))
				null := a.Have(
					"so it is Lebesgue measurable, and Lebesgue null",
					"{t} ∈ «lebesgueSets» ∧ lebesgue_outer_measure({t}) = &0",
					By(
						Normalized,
						point,
						lebesgue_measure.MeasurableClosedInterval.At(t, t),
						lebesgue_measure.OuterMeasureSingleton.At(t)))
				cut := a.Have(
					"the density cut to {t} vanishes off that null set",
					"measure_ae_eq(𝕌, "+
						"    «lebesgueSets», "+
						"    lebesgue_outer_measure, "+
						"    λx:real. COND(x ∈ {t}, extended_of_real(normal_density(&0, &1, x)), &0), "+
						"    λx:real. &0)",
					Simp(
						Fwd(measure_space.AEEqualDef),
						Fwd(measure_space.AlmostEverywhereDef),
						Fwd(measure_space.NullSetDef)),
					BySets(null))
				a.Show(
					"so its integral, the mass of {t}, is 0",
					Simp(Fwd(NormalDistributionDef), Fwd(density_measure.DensityMeasureDef)),
					By(
						cut,
						lebesgue_measure.LebesgueMeasureOn,
						nonneg_integral.NonnegIntegralAE.At(
							line,
							lebesgue,
							μ,
							a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]](
								"λx:real. COND(x ∈ {t}, extended_of_real(normal_density(&0, &1, x)), &0)"),
							a.TermAs[Fun[Real, extended_nonneg_real.ExtendedNonnegReal]]("λx:real. &0")),
						nonneg_integral.NonnegIntegralZero.At(line, lebesgue, μ)))
			})
		return ctx.Theorem(headline,
			func(
				a *Argument,
				ν *Arrow2[Nat, Set[Real], extended_nonneg_real.ExtendedNonnegReal],
				t *Expr[Real],
				weak Fact,
			) {
				a.Show(
					"weak convergence carries the masses of {y | y ≤ t} across, the limit giving t no mass",
					By(
						weak,
						At(noAtom, t),
						weak_convergence.WeakConvergenceDistributionFunction.At(
							ν,
							a.TermAs[Fun[Set[Real], extended_nonneg_real.ExtendedNonnegReal]]("normal_distribution(&0, &1)"),
							t)))
			})
	}),
})}
