// pushforward.go — distributions: a measurable map carries a probability to its
// image, and an integral against the distribution is the integral of the composite.

package random_variable

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

// DistributionProbability — a measurable pushforward of a probability is
// a probability because the target carrier pulls back to the source carrier.
var DistributionProbability = distributionProbabilityThm{family.Add(registry.ProofEntry{
	Name: "DistributionProbability",
	Key:  "prop_7172041fae7756b1",
	Reading: "sigma_algebra_on(V, T) is a hypothesis of its own: " +
		"measurable_map does not require it, and probability_on(V, T, ·) does.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀X:(A → B).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"sigma_algebra_on(V, T)",
			"measurable_map(Ω, S, V, T, X)",
		},
		Conclusion: "probability_on(V, T, pushforward_measure(Ω, μ, X))",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			X *Arrow[A, B],
			probability, sigma, measurable Fact,
		) {
			mapLaws := a.Unfolded(measurable, measurable_space.MeasurableMapDef)
			carrierPreimage := a.Have(
				"the target carrier pulls back to the whole source carrier",
				"preimage_on(Ω, X, V) = Ω",
				BySets(mapLaws),
			)
			sourceLaws := a.Unfolded(probability, probability_space.ProbabilityOnDef)
			pushforward := a.TermAs[Fun[Set[B], ExtendedNonnegReal]]("pushforward_measure(Ω, μ, X)")
			measure := a.Have(
				"the pushforward is a measure on the target",
				"measure_on(V, T, pushforward_measure(Ω, μ, X))",
				By(sourceLaws, sigma, measurable, measure_space.PushforwardMeasure.At(Ω, S, μ, V, T, X)))
			mass := a.Have(
				"so the target carrier has pushforward mass one",
				"pushforward_measure(Ω, μ, X, V) = &1",
				By(Normalized, carrierPreimage, sourceLaws, measure_space.PushforwardMeasureDef.At(Ω, μ, X, V)))
			a.Show(
				"a measure of total mass one is a probability",
				By(measure, mass, probability_space.ProbabilityOnDef.At(V, T, pushforward)))
		}),
})}

// ExpectationPushforward — pulling back an observable preserves its
// integrability and its expectation: the change of variables for the
// nonnegative integral applies to its absolute, positive and negative parts.
var ExpectationPushforward = expectationPushforwardThm{family.Add(registry.ProofEntry{
	Name: "ExpectationPushforward",
	Key:  "prop_8d83927e161e4479",
	Reading: "The equality of expectations holds even when h is not integrable: an infinite " +
		"positive or negative part reads as 0 through extended_to_real, on both sides alike.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀X:(A → B). " +
			"∀h:(B → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"sigma_algebra_on(V, T)",
			"measurable_map(Ω, S, V, T, X)",
			"real_measurable(V, T, h)",
		},
		Conclusion: "(real_integrable(V, T, pushforward_measure(Ω, μ, X), h) ⇔ " +
			"    real_integrable(Ω, S, μ, h ∘ X)) ∧ " +
			"expectation(V, T, pushforward_measure(Ω, μ, X), h) = expectation(Ω, S, μ, h ∘ X)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]],
			T *Expr[Set[Set[B]]],
			X *Arrow[A, B],
			h *Arrow[B, Real],
			measure, targetSigma, xMeasurable, hMeasurable Fact,
		) {
			target := a.TermAs[Fun[Set[B], ExtendedNonnegReal]]("pushforward_measure(Ω, μ, X)")
			observable := a.TermAs[Fun[A, Real]]("λx:A. h(X(x))")
			composition := functions.ComposeApply.At(h, X)
			pushed := a.Have(
				"the pushforward is a measure on V giving each set the mass of its inverse image",
				"measure_on(V, T, pushforward_measure(Ω, μ, X)) ∧ "+
					"(∀E:set(B). E ∈ T ⇒ pushforward_measure(Ω, μ, X, E) = μ(preimage_on(Ω, X, E)))",
				By(
					measure,
					targetSigma,
					xMeasurable,
					measure_space.PushforwardMeasure.At(Ω, S, μ, V, T, X),
					measure_space.PushforwardMeasureDef))
			positive := a.Have(
				"the positive integrals agree",
				"nonneg_integral(V, T, pushforward_measure(Ω, μ, X), λy:B. extended_of_real(h(y))) = "+
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(h(X(x))))",
				By(
					measure,
					targetSigma,
					xMeasurable,
					hMeasurable,
					measurable_function.ExtendedMeasurableOfReal.At(V, T, h),
					pushed,
					nonneg_integral.NonnegIntegralPushforward.At(
						Ω, S, μ, V, T, target, X, a.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_of_real(h(y))"))))
			negative := a.Have(
				"the negative integrals agree",
				"nonneg_integral(V, T, pushforward_measure(Ω, μ, X), λy:B. extended_of_real(-h(y))) = "+
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-h(X(x))))",
				By(
					measure,
					targetSigma,
					xMeasurable,
					hMeasurable,
					measurable_function.RealMeasurableNeg.At(V, T, h),
					measurable_function.ExtendedMeasurableOfReal.At(V, T, a.TermAs[Fun[B, Real]]("λy:B. -h(y)")),
					pushed,
					nonneg_integral.NonnegIntegralPushforward.At(
						Ω, S, μ, V, T, target, X, a.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_of_real(-h(y))"))))
			absolute := a.Have(
				"the absolute integrals agree",
				"nonneg_integral(V, T, pushforward_measure(Ω, μ, X), λy:B. extended_of_real(|h(y)|)) = "+
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|h(X(x))|))",
				By(
					measure,
					targetSigma,
					xMeasurable,
					hMeasurable,
					measurable_function.RealMeasurableAbs.At(V, T, h),
					measurable_function.ExtendedMeasurableOfReal.At(V, T, a.TermAs[Fun[B, Real]]("λy:B. |h(y)|")),
					pushed,
					nonneg_integral.NonnegIntegralPushforward.At(
						Ω, S, μ, V, T, target, X, a.TermAs[Fun[B, ExtendedNonnegReal]]("λy:B. extended_of_real(|h(y)|)"))))
			measurable := a.Have(
				"the pullback of the real observable is measurable",
				"real_measurable(Ω, S, λx:A. h(X(x)))",
				By(
					Normalized,
					xMeasurable,
					hMeasurable,
					composition,
					measurable_function.RealMeasurableDef.At(V, T, h),
					measurable_function.RealMeasurableDef.At(Ω, S, observable),
					measurable_space.MeasurableCompose.At(Ω, S, V, T,
						a.TermAs[Set[Real]]("𝕌"), a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)"), X, h)))
			a.Show(
				"the pullback has the same integrability and the same expectation",
				Simp(Fwd(functions.ComposeApply)),
				SplitConj(
					Case(
						"the absolute integral decides integrability",
						By(
							hMeasurable,
							absolute,
							measurable,
							measure_integral.RealIntegrableDef.At(V, T, target, h),
							measure_integral.RealIntegrableDef.At(Ω, S, μ, observable))),
					Case(
						"the positive and negative parts decide the expectation",
						By(
							positive,
							negative,
							measure_integral.RealIntegralDef.At(V, T, target, h),
							measure_integral.RealIntegralDef.At(Ω, S, μ, observable),
							probability_space.ExpectationDef.At(V, T, target, h),
							probability_space.ExpectationDef.At(Ω, S, μ, observable)))))
		})
	}),
})}

// IdenticallyDistributedExpectation — identically distributed random variables give every
// Borel function of them the same integrability and the same expectation: each side is the
// integral of h against the variable's distribution, and the two distributions agree on the
// Borel sets.
var IdenticallyDistributedExpectation = identicallyDistributedExpectationThm{family.Add(registry.ProofEntry{
	Name: "IdenticallyDistributedExpectation",
	Key:  "prop_d47874f344b90aaf",
	Reading: "The equality of expectations holds whether or not h(X) is integrable, as " +
		"ExpectationPushforward's does. X and Y are asked to be measurable, which " +
		"identically_distributed does not ask: the change of variables reads each distribution " +
		"as a measure on the Borel sets. The composites are written λx. h(X(x)), not h ∘ X as " +
		"ExpectationPushforward writes them, the β-reduced form a citer's integrands take.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀X Y:(A → real). " +
			"∀h:(real → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"real_measurable(Ω, S, X)",
			"real_measurable(Ω, S, Y)",
			"identically_distributed(Ω, μ, X, Y)",
			"real_measurable(𝕌, borel_sets(real_topology), h)",
		},
		Conclusion: "(real_integrable(Ω, S, μ, λx:A. h(X(x))) ⇔ " +
			"    real_integrable(Ω, S, μ, λx:A. h(Y(x)))) ∧ " +
			"expectation(Ω, S, μ, λx:A. h(X(x))) = expectation(Ω, S, μ, λx:A. h(Y(x)))",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			X, Y *Arrow[A, Real],
			h *Arrow[Real, Real],
			measure, xMeasurable, yMeasurable, identical, hMeasurable Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			distributionX := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("pushforward_measure(Ω, μ, X)")
			distributionY := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("pushforward_measure(Ω, μ, Y)")
			agree := a.Unfolded(identical, IdenticallyDistributedDef)
			alike := a.Have(
				"distributions that agree on the Borel sets integrate h alike",
				"(real_integrable(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, X), h) ⇔ "+
					"    real_integrable(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, Y), h)) ∧ "+
					"expectation(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, X), h) = "+
					"expectation(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, Y), h)",
				By(
					agree,
					borel_function.LineBorelSigmaAlgebra,
					measure_integral.IntegralEqualMeasures.At(line, borel, distributionX, distributionY, h),
					probability_space.ExpectationDef))
			underX := a.Have(
				"by the change of variables, h ∘ X under μ is h under the distribution of X",
				"(real_integrable(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, X), h) ⇔ "+
					"    real_integrable(Ω, S, μ, h ∘ X)) ∧ "+
					"expectation(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, X), h) = "+
					"expectation(Ω, S, μ, h ∘ X)",
				By(
					measure,
					borel_function.LineBorelSigmaAlgebra,
					xMeasurable,
					hMeasurable,
					measurable_function.RealMeasurableDef.At(Ω, S, X),
					ExpectationPushforward.At(Ω, S, μ, line, borel, X, h)))
			underY := a.Have(
				"by the change of variables, h ∘ Y under μ is h under the distribution of Y",
				"(real_integrable(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, Y), h) ⇔ "+
					"    real_integrable(Ω, S, μ, h ∘ Y)) ∧ "+
					"expectation(𝕌, borel_sets(real_topology), pushforward_measure(Ω, μ, Y), h) = "+
					"expectation(Ω, S, μ, h ∘ Y)",
				By(
					measure,
					borel_function.LineBorelSigmaAlgebra,
					yMeasurable,
					hMeasurable,
					measurable_function.RealMeasurableDef.At(Ω, S, Y),
					ExpectationPushforward.At(Ω, S, μ, line, borel, Y, h)))
			a.Show(
				"h ∘ X and h ∘ Y are the observables x ↦ h(X(x)) and x ↦ h(Y(x)), which therefore agree",
				By(underX, alike, underY, functions.ComposeApply.At(h, X), functions.ComposeApply.At(h, Y)))
		}),
})}
