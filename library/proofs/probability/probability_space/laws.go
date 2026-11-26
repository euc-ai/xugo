package probability_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// ProbabilityBounds — the mass of an event is at most one, and the event
// and its complement split the total mass.
var ProbabilityBounds = probabilityBoundsThm{family.Add(registry.ProofEntry{
	Name: "ProbabilityBounds",
	Key:  "prop_17a1d1e7bdfc2328",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E:set(A).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"E ∈ S",
		},
		Conclusion: "μ(E) ≤ &1 ∧ μ(Ω ∖ E) + μ(E) = &1",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		h Fact,
	) {
		probability := a.Unfolded(h, ProbabilityOnDef)
		carrier := a.Have(
			"the carrier is measurable and contains the event",
			"E ⊆ Ω ∧ Ω ∈ S",
			BySets(probability, measure_space.MeasureOn.At(Ω, S, μ), sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		a.Show(
			"monotonicity bounds the event and additivity splits the carrier",
			By(
				Normalized,
				carrier,
				probability,
				measure_space.MeasureMono.At(Ω, S, μ, E, Ω),
				measure_space.MeasureAddDiff.At(Ω, S, μ, E, Ω),
				extended_nonneg_real.AddComm.At(
					a.TermAs[ExtendedNonnegReal]("μ(E)"),
					a.TermAs[ExtendedNonnegReal]("μ(Ω ∖ E)"))))
	}),
})}

// ProbabilityEventFinite — the mass of an event is finite, so it is the extended
// real of its real value: it is at most one, and one is finite.
var ProbabilityEventFinite = probabilityEventFiniteThm{family.Add(registry.ProofEntry{
	Name: "ProbabilityEventFinite",
	Key:  "prop_db76ed8e56611d56",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E:set(A).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"E ∈ S",
		},
		Conclusion: "μ(E) ≠ extended_infinity ∧ μ(E) = extended_of_real(extended_to_real(μ(E)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		probability, event Fact,
	) {
		a.Show(
			"a mass at most the finite one is finite, and a finite mass is its real value",
			By(
				probability,
				event,
				ProbabilityBounds.At(Ω, S, μ, E),
				extended_nonneg_real.ExtendedLeDef.At(
					μ.Apply(E), a.TermAs[ExtendedNonnegReal]("extended_of_real(&1)")),
				extended_nonneg_real.OfRealNotInfinity.At(a.TermAs[Real]("&1")),
				extended_nonneg_real.OfRealToReal.At(μ.Apply(E))))
	}),
})}

// ProbabilitySigmaFinite — a probability measure is σ-finite: its total mass
// one is finite, so it is a finite measure.
var ProbabilitySigmaFinite = probabilitySigmaFiniteThm{family.Add(registry.ProofEntry{
	Name: "ProbabilitySigmaFinite",
	Key:  "prop_6922adde79ae9516",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"probability_on(Ω, S, μ)"},
		Conclusion: "sigma_finite_on(Ω, S, μ)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		probability Fact,
	) {
		a.Show(
			"a measure of total mass one is a finite measure, and a finite measure is σ-finite",
			By(
				Normalized,
				probability,
				ProbabilityOnDef.At(Ω, S, μ),
				measure_space.FiniteMeasureDef.At(Ω, S, μ),
				extended_nonneg_real.OfRealNotInfinity.At(a.TermAs[Real]("&1")),
				measure_space.FiniteMeasureSigmaFinite.At(Ω, S, μ)))
	}),
})}

// ExpectationConstant — a constant is integrable on a probability space
// and has expectation equal to its value.
var ExpectationConstant = expectationConstantThm{family.Add(registry.ProofEntry{
	Name: "ExpectationConstant",
	Key:  "prop_66c67ed550ce5616",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀c:real.",
		Hypotheses: []string{"probability_on(Ω, S, μ)"},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. c) ∧ expectation(Ω, S, μ, λx:A. c) = c",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		c *Expr[Real],
		h Fact,
	) {
		probability := a.Unfolded(h, ProbabilityOnDef)
		carrier := a.Have(
			"the carrier is measurable in its sigma algebra",
			"sigma_algebra_on(Ω, S) ∧ Ω ∈ S",
			By(probability, measure_space.MeasureOn.At(Ω, S, μ), sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		constant := a.TermAs[Fun[A, Real]]("λx:A. c")
		integrable := a.Have(
			"the constant is its cut to the carrier there, and the carrier has finite mass",
			"real_integrable(Ω, S, μ, λx:A. c)",
			By(
				carrier,
				probability,
				extended_nonneg_real.OfRealNotInfinity.At(a.TermAs[Real]("&1")),
				measure_integral.IntegrableIndicator.At(Ω, S, μ, Ω, c),
				measure_integral.RealIntegrableEqOn.At(
					Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ Ω, c, &0)"), constant)))
		a.Show(
			"the expectation is the integral over the carrier, the constant times its unit mass",
			ByArith(
				integrable,
				probability,
				carrier,
				ExpectationDef.At(Ω, S, μ, constant),
				event_integral.EventIntegralCarrier.At(Ω, S, μ, constant),
				event_integral.EventIntegralConst.At(Ω, S, μ, Ω, c),
				extended_nonneg_real.ToRealOfReal.At(a.TermAs[Real]("&1"))))
	}),
})}

// ExpectationIndicator — c times the indicator of an event is integrable, with
// expectation c times the probability of the event: the event has finite mass.
var ExpectationIndicator = expectationIndicatorThm{family.Add(registry.ProofEntry{
	Name: "ExpectationIndicator",
	Key:  "prop_5cbb4573b88a307b",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E:set(A). ∀c:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"E ∈ S",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. COND(x ∈ E, c, &0)) ∧ " +
			"expectation(Ω, S, μ, λx:A. COND(x ∈ E, c, &0)) = c * extended_to_real(μ(E))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		c *Expr[Real],
		probability, event Fact,
	) {
		a.Show(
			"an event of finite mass has an integrable indicator, and its integral is the expectation",
			By(
				probability,
				event,
				ProbabilityOnDef.At(Ω, S, μ),
				ProbabilityEventFinite.At(Ω, S, μ, E),
				measure_integral.IntegrableIndicator.At(Ω, S, μ, E, c),
				measure_integral.IntegralIndicator.At(Ω, S, μ, E, c),
				ExpectationDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, c, &0)"))))
	}),
})}

// BoundedIntegrable — on a probability space a measurable function bounded on the
// sample space is integrable: the constant bound is an integrable majorant.
var BoundedIntegrable = boundedIntegrableThm{family.Add(registry.ProofEntry{
	Name: "BoundedIntegrable",
	Key:  "prop_fd51b426eb89d276",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(A → real). " +
			"∀B:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"real_measurable(Ω, S, f)",
			"∀x:A. x ∈ Ω ⇒ |f(x)| ≤ B",
		},
		Conclusion: "real_integrable(Ω, S, μ, f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		B *Expr[Real],
		probability, measurable, bounded Fact,
	) {
		a.Show(
			"the constant B is integrable on a probability space and dominates |f|",
			By(
				probability,
				measurable,
				bounded,
				ExpectationConstant.At(Ω, S, μ, B),
				measure_integral.IntegrableDominated.At(Ω, S, μ, f, a.TermAs[Fun[A, Real]]("λx:A. B"))))
	}),
})}

// SquareIntegrableIntegrable — on a probability space a measurable variable with
// integrable square is integrable: |Y| is at most 1 + Y², and the constant one is integrable.
var SquareIntegrableIntegrable = squareIntegrableIntegrableThm{family.Add(registry.ProofEntry{
	Name: "SquareIntegrableIntegrable",
	Key:  "prop_4b8559e6023c68fa",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Y:(A → real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"real_measurable(Ω, S, Y)",
			"real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, Y)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		Y *Arrow[A, Real],
		probability, measurable, square Fact,
	) {
		majorant := a.TermAs[Fun[A, Real]]("λx:A. &1 + Y(x) * Y(x)")
		majorantIntegrable := a.Have(
			"1 + Y² is integrable, the constant one being integrable on a probability space",
			"real_integrable(Ω, S, μ, λx:A. &1 + Y(x) * Y(x))",
			By(
				probability,
				square,
				ProbabilityOnDef.At(Ω, S, μ),
				ExpectationConstant.At(Ω, S, μ, a.TermAs[Real]("&1")),
				measure_integral.IntegrableAdd.At(
					Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. &1"), a.TermAs[Fun[A, Real]]("λx:A. Y(x) * Y(x)"))))
		a.Show(
			"and it dominates |Y|",
			By(
				measurable,
				majorantIntegrable,
				real_sgn_abs.AbsQuadraticBound,
				measure_integral.IntegrableDominated.At(Ω, S, μ, Y, majorant)))
	}),
})}

// VarianceAffine — an affine image aY + b of a square-integrable variable is
// square-integrable with a² times the variance of Y: its mean is a·E[Y] + b, so it
// deviates from its mean by a times the deviation of Y.
var VarianceAffine = varianceAffineThm{family.Add(registry.ProofEntry{
	Name: "VarianceAffine",
	Key:  "prop_7918052be83b0839",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀Y:(A → real). " +
			"∀a b:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"real_measurable(Ω, S, Y)",
			"real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. (a * Y(x) + b) * (a * Y(x) + b)) ∧ " +
			"variance(Ω, S, μ, λx:A. a * Y(x) + b) = a * a * variance(Ω, S, μ, Y)",
		Abbrev: Abbrev{
			{Name: "centred", Text: "λx:A. " +
				"    (Y(x) - expectation(Ω, S, μ, Y)) * (Y(x) - expectation(Ω, S, μ, Y))"},
			{Name: "expansion", Text: "λx:A. a * a * (Y(x) * Y(x)) + &2 * a * b * Y(x) + b * b"},
		},
	}, func(
		arg *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		Y *Arrow[A, Real],
		a, b *Expr[Real],
		probability, measurable, square Fact,
	) {
		integrable := arg.Have(
			"a probability measure is a measure, and Y, being square-integrable, is integrable",
			"measure_on(Ω, S, μ) ∧ real_integrable(Ω, S, μ, Y)",
			By(
				probability,
				measurable,
				square,
				ProbabilityOnDef.At(Ω, S, μ),
				SquareIntegrableIntegrable.At(Ω, S, μ, Y)))
		constant := arg.TermAs[Fun[A, Real]]("λx:A. b")
		affine := arg.TermAs[Fun[A, Real]]("λx:A. a * Y(x) + b")
		mean := arg.Have(
			"aY + b has mean a·E[Y] + b, the integral being linear",
			"expectation(Ω, S, μ, λx:A. a * Y(x) + b) = a * expectation(Ω, S, μ, Y) + b",
			ByArith(
				integrable,
				probability,
				ExpectationConstant.At(Ω, S, μ, b),
				measure_integral.IntegrableScale.At(Ω, S, μ, Y, a),
				measure_integral.IntegralAdd.At(Ω, S, μ, arg.TermAs[Fun[A, Real]]("λx:A. a * Y(x)"), constant),
				measure_integral.IntegralScale.At(Ω, S, μ, Y, a),
				ExpectationDef.At(Ω, S, μ, affine),
				ExpectationDef.At(Ω, S, μ, Y),
				ExpectationDef.At(Ω, S, μ, constant)))
		expand := arg.Have(
			"the square of aY + b expands",
			"∀x:A. «expansion»(x) = (a * Y(x) + b) * (a * Y(x) + b)",
			ByArith())
		quadratic := arg.TermAs[Fun[A, Real]]("λx:A. a * a * (Y(x) * Y(x))")
		expansionIntegrable := arg.Have(
			"a²Y² + 2abY + b² is integrable, a sum of multiples of Y² and Y and the constant b²",
			"real_integrable(Ω, S, μ, «expansion»)",
			By(
				integrable,
				probability,
				square,
				measure_integral.IntegrableScale.At(
					Ω, S, μ, arg.TermAs[Fun[A, Real]]("λx:A. Y(x) * Y(x)"), arg.TermAs[Real]("a * a")),
				measure_integral.IntegrableScale.At(Ω, S, μ, Y, arg.TermAs[Real]("&2 * a * b")),
				measure_integral.IntegrableAdd.At(
					Ω, S, μ, quadratic, arg.TermAs[Fun[A, Real]]("λx:A. &2 * a * b * Y(x)")),
				ExpectationConstant.At(Ω, S, μ, arg.TermAs[Real]("b * b")),
				measure_integral.IntegrableAdd.At(
					Ω,
					S,
					μ,
					arg.TermAs[Fun[A, Real]]("λx:A. a * a * (Y(x) * Y(x)) + &2 * a * b * Y(x)"),
					arg.TermAs[Fun[A, Real]]("λx:A. b * b"))))
		squareIntegrable := arg.Have(
			"so is (aY + b)², which equals it pointwise",
			"real_integrable(Ω, S, μ, λx:A. (a * Y(x) + b) * (a * Y(x) + b))",
			By(
				expand,
				expansionIntegrable,
				measure_integral.RealIntegrableEqOn.At(
					Ω,
					S,
					μ,
					arg.TermAs[Fun[A, Real]]("«expansion»"),
					arg.TermAs[Fun[A, Real]]("λx:A. (a * Y(x) + b) * (a * Y(x) + b)"))))
		deviation := arg.Have(
			"so aY + b deviates from its mean by a times the deviation of Y",
			"(λx:A. "+
				"    (a * Y(x) + b - expectation(Ω, S, μ, λx:A. a * Y(x) + b)) * "+
				"    (a * Y(x) + b - expectation(Ω, S, μ, λx:A. a * Y(x) + b))) = "+
				"(λx:A. a * a * «centred»(x))",
			Funext(),
			ByArith(mean))
		centred := arg.TermAs[Fun[A, Real]]("«centred»")
		arg.Show(
			"the variance of aY + b integrates a² times the squared deviation of Y, a² times its variance",
			By(
				Normalized,
				squareIntegrable,
				deviation,
				integrable,
				VarianceDef.At(Ω, S, μ, affine),
				VarianceDef.At(Ω, S, μ, Y),
				ExpectationDef.At(Ω, S, μ, arg.TermAs[Fun[A, Real]]("λx:A. a * a * «centred»(x)")),
				ExpectationDef.At(Ω, S, μ, centred),
				measure_integral.IntegralScale.At(Ω, S, μ, centred, arg.TermAs[Real]("a * a"))))
	}),
})}

// ProbabilityIntegralSqrtUpperBound compares the square of the integral of
// the square root with the integral of a function nonnegative almost everywhere.
var ProbabilityIntegralSqrtUpperBound = probabilityIntegralSqrtUpperBoundThm{family.Add(registry.ProofEntry{
	Name: "ProbabilityIntegralSqrtUpperBound",
	Key:  "prop_f2ec136f7648fc46",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀q:(A → real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"real_integrable(Ω, S, μ, q)",
			"real_measurable(Ω, S, λx:A. real_sqrt(q(x)))",
			"measure_ae(Ω, S, μ, λx:A. &0 ≤ q(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. real_sqrt(q(x))) ∧ " +
			"(real_pow(measure_integral(Ω, S, μ, λx:A. real_sqrt(q(x))), 2) ≤ measure_integral(Ω, S, μ, q) ∧ " +
			"    &0 ≤ measure_integral(Ω, S, μ, λx:A. real_sqrt(q(x))))",
		Abbrev: Abbrev{
			{Name: "root", Text: "λq:(A → real). λx:A. real_sqrt(q(x))"},
			{Name: "absRoot", Text: "λq:(A → real). λx:A. |real_sqrt(q(x))|"},
			{Name: "squareF", Text: "λr:(A → real). λx:A. r(x) * r(x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		secondMomentBound := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀r:(A → real).",
			Hypotheses: []string{
				"probability_on(Ω, S, μ)",
				"real_measurable(Ω, S, r)",
				"real_integrable(Ω, S, μ, «squareF»(r))",
			},
			Conclusion: "real_integrable(Ω, S, μ, r) ∧ " +
				"real_pow(measure_integral(Ω, S, μ, r), 2) ≤ measure_integral(Ω, S, μ, «squareF»(r))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], extended_nonneg_real.ExtendedNonnegReal],
			r *Arrow[A, Real], probability, measurable, squareIntegrable Fact) {
			measure := a.Have(
				"a probability measure is a measure",
				"measure_on(Ω, S, μ)",
				By(probability, ProbabilityOnDef.At(Ω, S, μ)))
			square := a.TermAs[Fun[A, Real]]("«squareF»(r)")
			integrable := a.Have(
				"r is integrable, its square being integrable",
				"real_integrable(Ω, S, μ, r)",
				By(probability, measurable, squareIntegrable, SquareIntegrableIntegrable.At(Ω, S, μ, r)))
			comparison := a.Have(
				"integrate the nonnegative square around any real center",
				"∀t:real. "+
					"    (&2 * t) * measure_integral(Ω, S, μ, r) ≤ t * t + measure_integral(Ω, S, μ, «squareF»(r))",
				Derive(func(b *Argument) {
					b.FixAs[Real]("t")
					twiceCenter := b.TermAs[Real]("&2 * t")
					centerSquare := b.TermAs[Real]("t * t")
					constant := b.TermAs[Fun[A, Real]]("λx:A. t * t")
					left := b.TermAs[Fun[A, Real]]("λx:A. &2 * t * r(x)")
					right := b.TermAs[Fun[A, Real]]("λx:A. t * t + «squareF»(r, x)")
					leftIntegrable := b.Have(
						"the left side is a constant multiple of r",
						"real_integrable(Ω, S, μ, λx:A. &2 * t * r(x))",
						By(measure, integrable, measure_integral.IntegrableScale.At(Ω, S, μ, r, twiceCenter)))
					constantIntegrable := b.Have(
						"the square of the center is integrable as a constant",
						"real_integrable(Ω, S, μ, λx:A. t * t)",
						By(probability, ExpectationConstant.At(Ω, S, μ, centerSquare)))
					rightIntegrable := b.Have(
						"the right side sums two integrable functions",
						"real_integrable(Ω, S, μ, λx:A. t * t + «squareF»(r, x))",
						By(
							measure,
							constantIntegrable,
							squareIntegrable,
							measure_integral.IntegrableAdd.At(Ω, S, μ, constant, square)))
					pointwise := b.Have(
						"expand the square of r(x) minus the center",
						"∀x:A. x ∈ Ω ⇒ &2 * t * r(x) ≤ t * t + «squareF»(r, x)",
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							c.Assume()
							c.Show(
								"the centered square is nonnegative",
								ByArith(real_order_ring.SquareNonneg.At(c.TermAs[Real]("r(x) - t"))))
						}))
					integralOrder := b.Have(
						"integrate the pointwise inequality",
						"measure_integral(Ω, S, μ, λx:A. &2 * t * r(x)) ≤ "+
							"measure_integral(Ω, S, μ, λx:A. t * t + «squareF»(r, x))",
						By(
							leftIntegrable,
							rightIntegrable,
							pointwise,
							measure_integral.IntegralMono.At(Ω, S, μ, left, right)))
					leftIntegral := b.Have(
						"pull the constant multiple outside the integral",
						"measure_integral(Ω, S, μ, λx:A. &2 * t * r(x)) = &2 * t * measure_integral(Ω, S, μ, r)",
						By(measure, measure_integral.IntegralScale.At(Ω, S, μ, r, twiceCenter)))
					constantIntegral := b.Have(
						"integrating the constant against a probability law gives the constant",
						"measure_integral(Ω, S, μ, λx:A. t * t) = t * t",
						By(
							probability,
							ExpectationConstant.At(Ω, S, μ, centerSquare),
							ExpectationDef.At(Ω, S, μ, constant)))
					rightIntegral := b.Have(
						"the right integral is the centered constant plus the second moment",
						"measure_integral(Ω, S, μ, λx:A. t * t + «squareF»(r, x)) = "+
							"t * t + measure_integral(Ω, S, μ, «squareF»(r))",
						By(
							measure,
							constantIntegrable,
							squareIntegrable,
							constantIntegral,
							measure_integral.IntegralAdd.At(Ω, S, μ, constant, square)))
					b.Show(
						"substitute the two integral identities",
						ByArith(integralOrder, leftIntegral, rightIntegral))
				}))
			mean := a.TermAs[Real]("measure_integral(Ω, S, μ, r)")
			meanSquare := a.Have(
				"center at the integral of r",
				"real_pow(measure_integral(Ω, S, μ, r), 2) ≤ measure_integral(Ω, S, μ, «squareF»(r))",
				ByArith(comparison.At(mean), real_pow.PowTwo.At(mean)))
			a.Show(
				"r is integrable and its mean square is bounded",
				By(integrable, meanSquare))
		})

		return ctx.Theorem(
			headline,
			func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], extended_nonneg_real.ExtendedNonnegReal],
				q *Arrow[A, Real], probability, integrable, measurableRoot, nonnegative Fact) {
				root := a.TermAs[Fun[A, Real]]("«root»(q)")
				rootSquare := a.TermAs[Fun[A, Real]]("«squareF»(«root»(q))")
				absoluteRoot := a.TermAs[Fun[A, Real]]("«absRoot»(q)")
				nonnegativeInput := a.TermAs[Set[A]]("λx:A. &0 ≤ q(x)")
				pointwiseSquare := a.TermAs[Set[A]]("λx:A. «squareF»(«root»(q), x) = q(x)")
				pointwiseAbsolute := a.TermAs[Set[A]]("λx:A. «absRoot»(q, x) = «root»(q, x)")
				measure := a.Have(
					"the probability law is a measure",
					"measure_on(Ω, S, μ)",
					By(probability, ProbabilityOnDef.At(Ω, S, μ)))
				sigma := a.Have(
					"the events form a sigma algebra",
					"sigma_algebra_on(Ω, S)",
					By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
				measurableInput := a.Have(
					"integrability includes measurability of q",
					"real_measurable(Ω, S, q)",
					By(integrable, measure_integral.RealIntegrableDef.At(Ω, S, μ, q)))
				squareMeasurable := a.Have(
					"the square of the root is measurable",
					"real_measurable(Ω, S, «squareF»(«root»(q)))",
					By(sigma, measurableRoot, measurable_function.RealMeasurableMul.At(Ω, S, root, root)))
				squareIdentity := a.Have(
					"the square of the root restores q wherever q is nonnegative",
					"∀x:A. x ∈ Ω ∧ &0 ≤ q(x) ⇒ «squareF»(«root»(q), x) = q(x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						guard := b.Assume()
						b.Show(
							"square the root of the nonnegative value",
							By(
								Normalized,
								guard,
								real_sqrt.SqrtPowTwo.At(q.Apply(x)),
								real_pow.PowTwo.At(b.TermAs[Real]("«root»(q, x)"))))
					}))
				squareAgreement := a.Have(
					"the squared root equals q almost everywhere",
					"measure_ae_eq(Ω, S, μ, «squareF»(«root»(q)), q)",
					By(
						nonnegative,
						squareIdentity,
						measure_space.AEMono.At(Ω, S, μ, nonnegativeInput, pointwiseSquare),
						measure_space.AEEqualDef.At(Ω, S, μ, rootSquare, q)))
				squareIntegrable := a.Have(
					"the squared root is integrable by agreement with q",
					"real_integrable(Ω, S, μ, «squareF»(«root»(q)))",
					By(
						measure,
						squareMeasurable,
						measurableInput,
						integrable,
						squareAgreement,
						measure_integral.IntegrableAE.At(Ω, S, μ, rootSquare, q)))
				squareIntegral := a.Have(
					"the second moment of the root is the integral of q",
					"measure_integral(Ω, S, μ, «squareF»(«root»(q))) = measure_integral(Ω, S, μ, q)",
					By(measure, squareAgreement, measure_integral.IntegralAE.At(Ω, S, μ, rootSquare, q)))
				rootBound := a.Have(
					"the root is integrable and its squared integral is bounded by its second moment",
					"real_integrable(Ω, S, μ, «root»(q)) ∧ "+
						"real_pow(measure_integral(Ω, S, μ, «root»(q)), 2) ≤ "+
						"measure_integral(Ω, S, μ, «squareF»(«root»(q)))",
					By(probability, measurableRoot, squareIntegrable, At(secondMomentBound, Ω, S, μ, root)))
				absIdentity := a.Have(
					"the root is nonnegative wherever q is nonnegative",
					"∀x:A. x ∈ Ω ∧ &0 ≤ q(x) ⇒ «absRoot»(q, x) = «root»(q, x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						guard := b.Assume()
						b.Show(
							"the absolute value fixes a nonnegative root",
							By(
								guard,
								real_sqrt.SqrtNonneg.At(q.Apply(x)),
								real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("«root»(q, x)"))))
					}))
				absAgreement := a.Have(
					"the absolute root agrees with the root almost everywhere",
					"measure_ae_eq(Ω, S, μ, «absRoot»(q), «root»(q))",
					By(
						nonnegative,
						absIdentity,
						measure_space.AEMono.At(Ω, S, μ, nonnegativeInput, pointwiseAbsolute),
						measure_space.AEEqualDef.At(Ω, S, μ, absoluteRoot, root)))
				absIntegral := a.Have(
					"the absolute root and the root have the same integral",
					"measure_integral(Ω, S, μ, «absRoot»(q)) = measure_integral(Ω, S, μ, «root»(q))",
					By(measure, absAgreement, measure_integral.IntegralAE.At(Ω, S, μ, absoluteRoot, root)))
				absNonnegative := a.Have(
					"the absolute root is pointwise nonnegative",
					"∀x:A. x ∈ Ω ⇒ &0 ≤ «absRoot»(q, x)",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.Assume()
						b.Show(
							"an absolute value is nonnegative",
							By(real_sgn_abs.AbsNonneg.At(b.TermAs[Real]("«root»(q, x)"))))
					}))
				nonnegativeMean := a.Have(
					"the root has nonnegative integral",
					"&0 ≤ measure_integral(Ω, S, μ, «root»(q))",
					By(absNonnegative, absIntegral, measure_integral.IntegralNonneg.At(Ω, S, μ, absoluteRoot)))
				a.Show(
					"replace the second moment of the root by the integral of q",
					By(rootBound, squareIntegral, nonnegativeMean))
			})
	}),
})}

// ExpectationDifferenceOnEvent — a common error bound on the good set and a
// uniform bound on an exceptional event control the difference of expectations.
var ExpectationDifferenceOnEvent = expectationDifferenceOnEventThm{family.Add(registry.ProofEntry{
	Name: "ExpectationDifferenceOnEvent",
	Key:  "prop_a52be6eae8f91d8c",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀f g:(A → real). " +
			"∀B C:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"E ∈ S",
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
			"&0 ≤ C",
			"∀x:A. x ∈ Ω ⇒ |f(x) - g(x)| ≤ B",
			"∀x:A. x ∈ Ω ∧ x ∉ E ⇒ |f(x) - g(x)| ≤ C",
		},
		Conclusion: "|expectation(Ω, S, μ, f) - expectation(Ω, S, μ, g)| ≤ C + B * extended_to_real(μ(E))",
		Abbrev: Abbrev{
			{Name: "expectationMajorant", Text: "λx:A. C + COND(x ∈ E, B, &0)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		f, g *Arrow[A, Real],
		B, C *Expr[Real],
		assumptions Fact,
	) {
		constantC := a.TermAs[Fun[A, Real]]("λx:A. C")
		constantB := a.TermAs[Fun[A, Real]]("λx:A. B")
		penalty := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, B, &0)")
		majorant := a.TermAs[Fun[A, Real]]("«expectationMajorant»")
		measure := a.Have(
			"the probability is a measure with a sigma algebra",
			"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
			By(assumptions, ProbabilityOnDef.At(Ω, S, μ), measure_space.MeasureOn.At(Ω, S, μ)))
		parts := a.Have(
			"the constant and the exceptional penalty are integrable",
			"real_integrable(Ω, S, μ, λx:A. C) ∧ real_integrable(Ω, S, μ, λx:A. COND(x ∈ E, B, &0))",
			By(
				measure,
				assumptions,
				ExpectationConstant.At(Ω, S, μ, C),
				ExpectationConstant.At(Ω, S, μ, B),
				event_integral.IntegrableOnEvent.At(Ω, S, μ, E, constantB)))
		integrable := a.Have(
			"their sum is integrable",
			"real_integrable(Ω, S, μ, «expectationMajorant»)",
			By(measure, parts, measure_integral.IntegrableAdd.At(Ω, S, μ, constantC, penalty)))
		cost := a.Have(
			"the exceptional penalty integrates to the bound times its probability",
			"measure_integral(Ω, S, μ, «expectationMajorant») = C + B * extended_to_real(μ(E))",
			ByArith(
				measure,
				assumptions,
				parts,
				measure_integral.IntegralAdd.At(Ω, S, μ, constantC, penalty),
				ExpectationConstant.At(Ω, S, μ, C),
				ExpectationDef.At(Ω, S, μ, constantC),
				event_integral.EventIntegralConst.At(Ω, S, μ, E, B),
				event_integral.EventIntegralDef.At(Ω, S, μ, E, constantB)))
		pointwise := a.Have(
			"the majorant dominates the error everywhere",
			"∀x:A. x ∈ Ω ⇒ |f(x) - g(x)| ≤ «expectationMajorant»(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]()
				inSpace := b.Assume()
				b.Cases(b.Term("x ∈ E"))
				b.When(
					"on the exceptional event",
					func(d *Argument, inE Fact) {
						d.Show(
							"the penalty supplies the uniform bound",
							ByArith(inE, inSpace, assumptions))
					})
				b.Otherwise(
					"off the exceptional event",
					func(d *Argument, outside Fact) {
						d.Show(
							"the constant controls the error",
							ByArith(outside, inSpace, assumptions))
					})
			}))
		dominated := a.Have(
			"the integral of the majorant bounds the difference of integrals",
			"|measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g)| ≤ "+
				"measure_integral(Ω, S, μ, «expectationMajorant»)",
			By(
				pointwise,
				measure,
				assumptions,
				integrable,
				measure_integral.IntegralAbsSubLe.At(Ω, S, μ, f, g, majorant)))
		a.Show(
			"expectations are the integrals being compared",
			ByArith(Normalized, cost, dominated, ExpectationDef.At(Ω, S, μ, f), ExpectationDef.At(Ω, S, μ, g)))
	}),
})}
