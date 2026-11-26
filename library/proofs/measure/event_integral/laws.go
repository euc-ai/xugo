// laws.go — the laws of the integral over an event.

package event_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegrableOnEvent — cutting an integrable function to a measurable event
// preserves integrability: the cut stays measurable, and
// its absolute value has integral bounded by that of the original function.
var IntegrableOnEvent = integrableOnEventThm{family.Add(registry.ProofEntry{
	Name: "IntegrableOnEvent",
	Key:  "prop_ed73072a185ba7a",
	Reading: "S need only be a sigma algebra and μ is any set function: the " +
		"bound is monotonicity of a supremum. E ∈ S is load-bearing, since the " +
		"cut of a nonzero constant to a subset of Ω outside S is not measurable.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"E ∈ S",
			"real_integrable(Ω, S, μ, f)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. COND(x ∈ E, f(x), &0))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		f *Arrow[A, Real],
		sigma, event, integrable Fact,
	) {
		cut := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, f(x), &0)")
		measurable := a.Have(
			"the cut to the measurable event stays measurable",
			"real_measurable(Ω, S, λx:A. COND(x ∈ E, f(x), &0))",
			By(
				event,
				sigma,
				integrable,
				measure_integral.RealIntegrableDef.At(Ω, S, μ, f),
				measurable_function.RealMeasurableOnEvent.At(Ω, S, E, f)))
		below := a.Have(
			"cutting to E cannot increase the embedded absolute value",
			"∀x:A. extended_of_real(|COND(x ∈ E, f(x), &0)|) ≤ extended_of_real(|f(x)|)",
			ByArith(extended_nonneg_real.OfRealLe, real_sgn_abs.AbsNonneg))
		a.Show(
			"the integral of the absolute value of the cut is bounded by the finite integral of |f|",
			By(
				below,
				measurable,
				integrable,
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|COND(x ∈ E, f(x), &0)|)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)")),
				extended_nonneg_real.ExtendedLeDef,
				measure_integral.RealIntegrableDef.At(Ω, S, μ, f),
				measure_integral.RealIntegrableDef.At(Ω, S, μ, cut)))
	}),
})}

// EventIntegralCarrier — integration over the whole carrier is the
// original integral: cutting to the carrier preserves both embedded
// integrands at every point the nonnegative integrals read.
var EventIntegralCarrier = eventIntegralCarrierThm{family.Add(registry.ProofEntry{
	Name:    "EventIntegralCarrier",
	Key:     "prop_db2d4d6bedc2b0ba",
	Reading: "No structure is asked of Ω, S or μ, and no integrability.",
	Build: family.Theorem("∀Ω:set(A). "+
		"∀S:set(set(A)). "+
		"∀μ:(set(A) → extended_nonneg_real). "+
		"∀f:(A → real). "+
		"    event_integral(Ω, S, μ, Ω, f) = measure_integral(Ω, S, μ, f)",
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow[A, Real],
		) {
			a.Do(Unfold(EventIntegralDef), Unfold(measure_integral.RealIntegralDef))
			a.Show(
				"both embedded integrands agree on Ω, so both nonnegative integrals agree",
				By(
					nonneg_integral.NonnegIntegralEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(COND(x ∈ Ω, f(x), &0))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))")),
					nonneg_integral.NonnegIntegralEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-COND(x ∈ Ω, f(x), &0))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"))))
		}),
})}

// EventIntegralEqOn — functions agreeing on the part of an event inside
// the carrier have equal event integrals: their cuts agree on the carrier,
// so both nonnegative integrals defining the signed integral agree.
var EventIntegralEqOn = eventIntegralEqOnThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralEqOn",
	Key:  "prop_8c02cf254bebef92",
	Reading: "No structure is asked of Ω, S or μ, and E need not " +
		"be an event of S. The integrands are compared on Ω ∩ E only.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀f g:(A → real).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ∧ x ∈ E ⇒ f(x) = g(x)"},
		Conclusion: "event_integral(Ω, S, μ, E, f) = event_integral(Ω, S, μ, E, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		E *Expr[Set[A]],
		f, g *Arrow[A, Real],
		agree Fact,
	) {
		a.Do(Unfold(EventIntegralDef), Unfold(measure_integral.RealIntegralDef))
		a.Show(
			"the cuts and their negatives agree on Ω, so their nonnegative integrals agree",
			By(
				agree,
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(COND(x ∈ E, f(x), &0))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(COND(x ∈ E, g(x), &0))")),
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-COND(x ∈ E, f(x), &0))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-COND(x ∈ E, g(x), &0))"))))
	}),
})}

// EventIntegralAE — almost-everywhere equality of the integrands implies
// equality of their integrals over any event, since their cuts agree almost everywhere.
var EventIntegralAE = eventIntegralAEThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralAE",
	Key:  "prop_67c8d117330f9aa3",
	Reading: "E need not be an event of S and no measurability is asked of f or g: a " +
		"subset of a null set is null. The measure axioms are load-bearing: a set function " +
		"that is not monotone can give a set of positive mass inside one of mass zero, and " +
		"the indicator of that set is then 0 almost everywhere with a positive integral.",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A). ∀f g:(A → real).",
		Hypotheses: []string{"measure_ae_eq(Ω, S, μ, f, g)"},
		Conclusion: "event_integral(Ω, S, μ, E, f) = event_integral(Ω, S, μ, E, g)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		f, g *Arrow[A, Real],
		equal Fact,
	) {
		agree := a.Unfolded(equal, measure_space.AEEqualDef)
		pointwise := a.Have(
			"where f and g agree, cutting both to E preserves their equality",
			"∀x:A. x ∈ Ω ∧ f(x) = g(x) ⇒ «cutOff»(E, f, x) = «cutOff»(E, g, x)",
			BySets())
		cutsAgree := a.Have(
			"the cuts to E agree almost everywhere",
			"measure_ae_eq(Ω, S, μ, «cutOff»(E, f), «cutOff»(E, g))",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				agree,
				pointwise,
				measure_space.AEMono.At(
					Ω, S, μ,
					a.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
					a.TermAs[Set[A]]("λx:A. «cutOff»(E, f, x) = «cutOff»(E, g, x)"))))
		cutF := a.TermAs[Fun[A, Real]]("«cutOff»(E, f)")
		cutG := a.TermAs[Fun[A, Real]]("«cutOff»(E, g)")
		a.Show(
			"almost-everywhere equality gives equal integrals of the cuts",
			By(
				measure,
				cutsAgree,
				measure_integral.IntegralAE.At(Ω, S, μ, cutF, cutG),
				EventIntegralDef.At(Ω, S, μ, E, f),
				EventIntegralDef.At(Ω, S, μ, E, g)))
	}),
})}

// EventIntegralAdd — integration over an event adds integrable functions:
// cutting distributes over addition, and both cuts remain integrable.
var EventIntegralAdd = eventIntegralAddThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralAdd",
	Key:  "prop_7d267429f4d948dc",
	Reading: "Both integrabilities are load-bearing. For counting measure on ℕ " +
		"and E = Ω, take f the constant 1 and g equal to 1 at 0 and to −1 elsewhere: " +
		"f + g integrates to 2, while the infinite parts of f and g are read as zero " +
		"and their integrals are 0 and 1. E ∈ S is what makes the cuts integrable.",
	Build: measure_space.MeasureOn.Law(Statement{
		Binders: "∀E:set(A). ∀f g:(A → real).",
		Hypotheses: []string{
			"E ∈ S",
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "event_integral(Ω, S, μ, E, λx:A. f(x) + g(x)) = " +
			"event_integral(Ω, S, μ, E, f) + event_integral(Ω, S, μ, E, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		event Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		a.Do(Unfold(EventIntegralDef))
		cut := a.Have(
			"cutting distributes over addition, since zero plus zero is zero",
			"«cutOff»(E, λx:A. f(x) + g(x)) = (λx:A. «cutOff»(E, f, x) + «cutOff»(E, g, x))",
			By(real_ring.AddRightId))
		a.Show(
			"the integral adds the two integrable cuts",
			cut.Rw(),
			By(
				event,
				sigma,
				measure,
				integrableF,
				integrableG,
				IntegrableOnEvent.At(Ω, S, μ, E, f),
				IntegrableOnEvent.At(Ω, S, μ, E, g),
				measure_integral.IntegralAdd.At(
					Ω, S, μ, a.TermAs[Fun[A, Real]]("«cutOff»(E, f)"), a.TermAs[Fun[A, Real]]("«cutOff»(E, g)"))))
	}),
})}

// EventIntegralSub — integration over an event subtracts integrable functions:
// cutting distributes over subtraction, and both cuts remain integrable.
var EventIntegralSub = eventIntegralSubThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralSub",
	Key:  "prop_fc39e5208fb50bdc",
	Reading: "As for the sum, both integrabilities are " +
		"load-bearing, and E ∈ S is what makes the cuts integrable.",
	Build: measure_space.MeasureOn.Law(Statement{
		Binders: "∀E:set(A). ∀f g:(A → real).",
		Hypotheses: []string{
			"E ∈ S",
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "event_integral(Ω, S, μ, E, λx:A. f(x) - g(x)) = " +
			"event_integral(Ω, S, μ, E, f) - event_integral(Ω, S, μ, E, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		event Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		a.Do(Unfold(EventIntegralDef))
		cut := a.Have(
			"cutting distributes over subtraction, since zero minus zero is zero",
			"«cutOff»(E, λx:A. f(x) - g(x)) = (λx:A. «cutOff»(E, f, x) - «cutOff»(E, g, x))",
			By(real_ring.SubRefl))
		a.Show(
			"the integral subtracts the two integrable cuts",
			cut.Rw(),
			By(
				event,
				sigma,
				measure,
				integrableF,
				integrableG,
				IntegrableOnEvent.At(Ω, S, μ, E, f),
				IntegrableOnEvent.At(Ω, S, μ, E, g),
				measure_integral.IntegralSub.At(
					Ω, S, μ, a.TermAs[Fun[A, Real]]("«cutOff»(E, f)"), a.TermAs[Fun[A, Real]]("«cutOff»(E, g)"))))
	}),
})}

// EventIntegralScale — a real factor moves through the integral over an
// event: cutting a scalar multiple to the event is scaling the cut.
var EventIntegralScale = eventIntegralScaleThm{family.Add(registry.ProofEntry{
	Name:    "EventIntegralScale",
	Key:     "prop_6ba56e97d5baeba8",
	Reading: "Like the law of the integral it reads, it asks neither integrability nor E ∈ S.",
	Build: measure_space.MeasureOn.Law(Statement{
		Binders:    "∀E:set(A). ∀f:(A → real). ∀c:real.",
		Conclusion: "event_integral(Ω, S, μ, E, λx:A. c * f(x)) = c * event_integral(Ω, S, μ, E, f)",
	}, func(a *Argument, measure Fact, E *Expr[Set[A]], f *Arrow[A, Real], c *Expr[Real]) {
		a.Do(Unfold(EventIntegralDef))
		cut := a.Have(
			"cutting commutes with scalar multiplication, since c times zero is zero",
			"(λx:A. COND(x ∈ E, c * f(x), &0)) = (λx:A. c * COND(x ∈ E, f(x), &0))",
			By(real_ring.MulRightZero))
		a.Show(
			"the scalar moves through the integral of the cut",
			cut.Rw(),
			By(measure, measure_integral.IntegralScale))
	}),
})}

// EventIntegralUnion — integration is additive over two disjoint events:
// the cut to their union is the sum of the cuts to each, and both cuts are
// integrable.
var EventIntegralUnion = eventIntegralUnionThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralUnion",
	Key:  "prop_75503e894d9f2825",
	Reading: "Disjointness is read at every point: on an overlap the two cuts add to twice f. " +
		"Integrability is load-bearing: for counting measure on ℕ, f the constant 1, E = {0} and D " +
		"its complement, the left side is read as 0 and the right is 1. So is measurability of the " +
		"events: on S = {∅, Ω} with μ(Ω) = 1 the two halves of a two-point Ω each integrate 1 to 0.",
	Build: measure_space.MeasureOn.Law(Statement{
		Binders: "∀E D:set(A). ∀f:(A → real).",
		Hypotheses: []string{
			"E ∈ S",
			"D ∈ S",
			"E ∩ D = ∅",
			"real_integrable(Ω, S, μ, f)",
		},
		Conclusion: "event_integral(Ω, S, μ, E ∪ D, f) = " +
			"event_integral(Ω, S, μ, E, f) + event_integral(Ω, S, μ, D, f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		eventE Fact,
		D *Expr[Set[A]],
		eventD, disjoint Fact,
		f *Arrow[A, Real],
		integrable Fact,
	) {
		cutE := a.TermAs[Fun[A, Real]]("«cutOff»(E, f)")
		cutD := a.TermAs[Fun[A, Real]]("«cutOff»(D, f)")
		union := a.Have(
			"at most one cut is nonzero, so the union cut is their sum",
			"«cutOff»(E ∪ D, f) = (λx:A. «cutOff»(E, f, x) + «cutOff»(D, f, x))",
			BySets(disjoint, real_ring.AddRightId, real_construction.AddLeftId))
		cuts := a.Have(
			"cutting to either measurable event preserves integrability",
			"real_integrable(Ω, S, μ, «cutOff»(E, f)) ∧ real_integrable(Ω, S, μ, «cutOff»(D, f))",
			By(
				measure,
				eventE,
				eventD,
				integrable,
				measure_space.MeasureOn.At(Ω, S, μ),
				IntegrableOnEvent.At(Ω, S, μ, E, f),
				IntegrableOnEvent.At(Ω, S, μ, D, f)))
		a.Show(
			"integration adds the two integrable cuts",
			Simp(Fwd(EventIntegralDef), Fwd(union)),
			By(measure, cuts, measure_integral.IntegralAdd.At(Ω, S, μ, cutE, cutD)))
	}),
})}

// EventIntegralMono — event integration preserves order on the part of the
// event inside the carrier: each cut has finite positive and negative parts,
// their positive parts compare forwards and their negative parts backwards,
// and subtraction gives the comparison of their signed integrals.
var EventIntegralMono = eventIntegralMonoThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralMono",
	Key:  "prop_5f2710b7977d0fdc",
	Reading: "No structure is asked of Ω, S or μ, and E is any set. The integrands " +
		"are compared only on Ω ∩ E. Integrability of f and g makes the four signed-part " +
		"integrals of their cuts finite; measurability of the cuts is not needed.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀E:set(A). " +
			"∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
			"∀x:A. x ∈ Ω ∩ E ⇒ f(x) ≤ g(x)",
		},
		Conclusion: "event_integral(Ω, S, μ, E, f) ≤ event_integral(Ω, S, μ, E, g)",
		Abbrev: Abbrev{
			{Name: "positiveCut", Text: "λf:(A → real). " +
				"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(«cutOff»(E, f, x)))"},
			{Name: "negativeCut", Text: "λf:(A → real). " +
				"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-«cutOff»(E, f, x)))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteCutParts := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀E:set(A). " +
				"∀f:(A → real).",
			Hypotheses: []string{"real_integrable(Ω, S, μ, f)"},
			Conclusion: "«positiveCut»(f) ≠ extended_infinity ∧ «negativeCut»(f) ≠ extended_infinity",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			E *Expr[Set[A]],
			f *Arrow[A, Real],
			integrable Fact,
		) {
			below := a.Have(
				"cutting cannot increase either embedded signed part",
				"∀x:A. "+
					"    extended_of_real(«cutOff»(E, f, x)) ≤ extended_of_real(f(x)) ∧ "+
					"    extended_of_real(-«cutOff»(E, f, x)) ≤ extended_of_real(-f(x))",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Cases(b.TermAs[Bool]("x ∈ E"))
					b.When(
						"on the event both parts are unchanged",
						func(c *Argument, inside Fact) {
							c.Show(
								"each part equals the corresponding original part",
								By(inside, extended_nonneg_real.LeRefl))
						})
					b.Otherwise(
						"off the event both parts vanish",
						func(c *Argument, outside Fact) {
							c.Show(
								"zero lies below each original part",
								ByArith(outside, extended_nonneg_real.ZeroLe))
						})
				}))
			a.Show(
				"their integrals lie below the finite integrals of the original parts",
				By(
					below,
					integrable,
					measure_integral.IntegrablePartsFinite.At(Ω, S, μ, f),
					nonneg_integral.NonnegIntegralMono.At(Ω, S, μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«cutOff»(E, f, x))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))")),
					nonneg_integral.NonnegIntegralMono.At(Ω, S, μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-«cutOff»(E, f, x))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))")),
					extended_nonneg_real.ExtendedLeDef))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			E *Expr[Set[A]],
			f, g *Arrow[A, Real],
			integrableF, integrableG, below Fact,
		) {
			parts := a.Have(
				"on Ω the positive cuts compare forwards and the negative cuts backwards",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "extended_of_real(«cutOff»(E, f, x)) ≤ extended_of_real(«cutOff»(E, g, x)) ∧ " +
						"extended_of_real(-«cutOff»(E, g, x)) ≤ extended_of_real(-«cutOff»(E, f, x))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					inΩ := b.Assume()
					cutsBelow := b.Have(
						"the cuts keep the given order on Ω",
						"«cutOff»(E, f, x) ≤ «cutOff»(E, g, x)",
						BySets(inΩ, below.At(x), real_order_ring.LessEqRefl))
					negativesBelow := b.Have(
						"negation reverses that order",
						"-«cutOff»(E, g, x) ≤ -«cutOff»(E, f, x)",
						ByArith(cutsBelow))
					b.Show(
						"the nonnegative embedding preserves both inequalities",
						By(
							negativesBelow,
							cutsBelow,
							extended_nonneg_real.OfRealMono.At(
								b.TermAs[Real]("«cutOff»(E, f, x)"), b.TermAs[Real]("«cutOff»(E, g, x)")),
							extended_nonneg_real.OfRealMono.At(
								b.TermAs[Real]("-«cutOff»(E, g, x)"), b.TermAs[Real]("-«cutOff»(E, f, x)"))))
				}))
			values := a.Have(
				"the four finite part integrals have the same order as their integrands",
				"extended_to_real(«positiveCut»(f)) ≤ extended_to_real(«positiveCut»(g)) ∧ "+
					"extended_to_real(«negativeCut»(g)) ≤ extended_to_real(«negativeCut»(f))",
				By(
					parts,
					integrableF,
					integrableG,
					At(finiteCutParts, Ω, S, μ, E, f),
					At(finiteCutParts, Ω, S, μ, E, g),
					nonneg_integral.NonnegIntegralMono.At(Ω, S, μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«cutOff»(E, f, x))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«cutOff»(E, g, x))")),
					nonneg_integral.NonnegIntegralMono.At(Ω, S, μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-«cutOff»(E, g, x))"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-«cutOff»(E, f, x))")),
					extended_nonneg_real.ExtendedLeDef))
			a.Show(
				"subtracting the negative part from the positive part compares the event integrals",
				ByArith(
					values,
					EventIntegralDef.At(Ω, S, μ, E, f),
					EventIntegralDef.At(Ω, S, μ, E, g),
					measure_integral.RealIntegralDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«cutOff»(E, f)")),
					measure_integral.RealIntegralDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«cutOff»(E, g)"))))
		})
	}),
})}

// EventIntegralMonoAE — event integration preserves almost-everywhere order:
// the part of E where f lies below g has the same event integrals as E, since
// cutting to it keeps each integrand almost everywhere, and on that part the
// order holds at every point.
var EventIntegralMonoAE = eventIntegralMonoAEThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralMonoAE",
	Key:  "prop_70d678cc6025d5b8",
	Reading: "E need not be an event of S and no measurability " +
		"is asked of f or g: a subset of a null set is null.",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀E:set(A). ∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
			"measure_ae(Ω, S, μ, λx:A. f(x) ≤ g(x))",
		},
		Conclusion: "event_integral(Ω, S, μ, E, f) ≤ event_integral(Ω, S, μ, E, g)",
		Abbrev: Abbrev{
			{Name: "ordered", Text: "{x:A | f(x) ≤ g(x)}"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		f, g *Arrow[A, Real],
		integrableF, integrableG, order Fact,
	) {
		ordered := a.TermAs[Set[A]]("«ordered»")
		sameIntegral := a.Have(
			"cutting E to where f lies below g changes no event integral",
			"∀h:(A → real). event_integral(Ω, S, μ, E ∩ «ordered», h) = event_integral(Ω, S, μ, E, h)",
			Derive(func(b *Argument) {
				h := b.FixAs[Fun[A, Real]]("h")
				pointwise := b.Have(
					"where f lies below g, the cut to that set keeps h",
					"∀x:A. x ∈ Ω ∧ f(x) ≤ g(x) ⇒ h(x) = «cutOff»(«ordered», h, x)",
					BySets())
				kept := b.Have(
					"so h agrees with that cut almost everywhere",
					"measure_ae_eq(Ω, S, μ, h, «cutOff»(«ordered», h))",
					Simp(Fwd(measure_space.AEEqualDef)),
					By(
						order,
						pointwise,
						measure_space.AEMono.At(
							Ω, S, μ,
							b.TermAs[Set[A]]("λx:A. f(x) ≤ g(x)"),
							b.TermAs[Set[A]]("λx:A. h(x) = «cutOff»(«ordered», h, x)"))))
				b.Show(
					"over E the cut integrates as h does, and its integral "+
						"over E is that of h over the part of E where f lies below g",
					By(
						measure,
						kept,
						EventIntegralAE.At(Ω, S, μ, E, h, b.TermAs[Fun[A, Real]]("«cutOff»(«ordered», h)")),
						EventIntegralRestrict.At(Ω, S, μ, E, ordered, h)))
			}))
		orderOnPart := a.Have(
			"on that part of E the order holds at every point",
			"∀x:A. x ∈ Ω ∩ (E ∩ «ordered») ⇒ f(x) ≤ g(x)",
			BySets())
		a.Show(
			"compare the event integrals over the part of E where f lies below g",
			By(
				integrableF,
				integrableG,
				orderOnPart,
				sameIntegral.At(f),
				sameIntegral.At(g),
				EventIntegralMono.At(Ω, S, μ, a.TermAs[Set[A]]("E ∩ «ordered»"), f, g)))
	}),
})}

// EventIntegralRestrict — cutting an integrand to a set intersects the
// event of integration with that set: the two resulting cuts are the
// same function at every point.
var EventIntegralRestrict = eventIntegralRestrictThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralRestrict",
	Key:  "prop_e0d4f29d3bf37bf4",
	Reading: "It is an identity of integrands, with no structure asked of Ω, S or μ " +
		"and E, D any sets. At E = Ω it reads the integral of a cut as an event integral.",
	Build: family.Theorem("∀Ω:set(A). "+
		"∀S:set(set(A)). "+
		"∀μ:(set(A) → extended_nonneg_real). "+
		"∀E D:set(A). "+
		"∀f:(A → real). "+
		"    event_integral(Ω, S, μ, E, λx:A. COND(x ∈ D, f(x), &0)) = event_integral(Ω, S, μ, E ∩ D, f)",
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			E, D *Expr[Set[A]],
			f *Arrow[A, Real],
		) {
			a.Do(Unfold(EventIntegralDef))
			cuts := a.Have(
				"successive cuts keep f exactly on the intersection",
				"(λx:A. COND(x ∈ E, COND(x ∈ D, f(x), &0), &0)) = (λx:A. COND(x ∈ E ∩ D, f(x), &0))",
				BySets())
			a.Show(
				"the same integrand has the same integral",
				cuts.Rw(),
				Basic())
		}),
})}

// EventIntegralConst — a constant c integrates over a measurable event to c
// times the measure of the event: the event integral is the integral of the
// cut of c to the event.
var EventIntegralConst = eventIntegralConstThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralConst",
	Key:  "prop_31cb3fce1653c012",
	Reading: "An event of infinite measure gives 0 on both sides for every c: " +
		"extended_to_real reads extended_infinity as &0, and the infinite integral of " +
		"a nonzero constant is read as zero. With μ(E) finite it is the usual c·μ(E). " +
		"E ∈ S is load-bearing: on S = {∅, Ω} the cut of 1 to a proper nonempty subset " +
		"has no simple minorant but 0 and integrates to 0, whatever μ gives the subset.",
	Build: measure_space.MeasureOn.Law(Statement{
		Binders:    "∀E:set(A). ∀c:real.",
		Hypotheses: []string{"E ∈ S"},
		Conclusion: "event_integral(Ω, S, μ, E, λx:A. c) = c * extended_to_real(μ(E))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		event Fact,
		c *Expr[Real],
	) {
		a.Show(
			"the event integral is the integral of the cut of c to E",
			By(
				measure,
				event,
				EventIntegralDef.At(Ω, S, μ, E, a.TermAs[Fun[A, Real]]("λx:A. c")),
				measure_integral.IntegralIndicator.At(Ω, S, μ, E, c)))
	}),
})}

// EventIntegralDominatedConvergence — dominated almost-everywhere convergence
// passes to the integral over each measurable event. Cutting to the event
// preserves measurability, convergence and the bound, so dominated convergence
// applies to the cut functions.
var EventIntegralDominatedConvergence = eventIntegralDominatedConvergenceThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralDominatedConvergence",
	Key:  "prop_5d58568c76d3ed71",
	Build: family.Sections(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀E:set(A). ∀f:(num → A → real). ∀g h:(A → real).",
		Hypotheses: []string{
			"E ∈ S",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"real_measurable(Ω, S, g)",
			"real_integrable(Ω, S, μ, h)",
			"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. f(n, x), g(x)))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |f(n, x)| ≤ h(x))",
		},
		Conclusion: "real_converges_to(λn:num. event_integral(Ω, S, μ, E, f(n)), " +
			"    event_integral(Ω, S, μ, E, g))",
	}), func(ctx *Script, headline string) *GoalStackNode {
		cutConvergence := ctx.Lemma(Statement{
			Binders:    "∀E:set(A). ∀f:(num → A → real). ∀g:(A → real). ∀x:A.",
			Hypotheses: []string{"real_converges_to(λn:num. f(n, x), g(x))"},
			Conclusion: "real_converges_to(λn:num. «cutOff»(E, f(n), x), «cutOff»(E, g, x))",
		}, func(
			a *Argument,
			E *Expr[Set[A]],
			f *Arrow2[Nat, A, Real],
			g *Arrow[A, Real],
			x *Expr[A],
			pointwise Fact,
		) {
			a.Cases(a.TermAs[Bool]("x ∈ E"))
			a.When(
				"on E the cut functions keep their values",
				func(b *Argument, inside Fact) {
					b.Show(
						"the given convergence applies",
						By(inside, pointwise))
				})
			a.Otherwise(
				"off E the sequence and its limit are zero",
				func(b *Argument, outside Fact) {
					b.Show(
						"a constant sequence converges to its value",
						By(outside, real_sequences.LimitConst.At(b.TermAs[Real]("&0"))))
				})
		})
		return ctx.Theorem(headline, func(a *Argument,
			Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			E *Expr[Set[A]], f *Arrow2[Nat, A, Real], g, h *Arrow[A, Real],
			measure, event, measurable, gMeasurable, integrable, converges, dominated Fact,
		) {
			cutsMeasurable := a.Conjuncts(
				a.Have(
					"the sequence and its limit remain measurable when cut to E",
					"(∀n:num. real_measurable(Ω, S, «cutOff»(E, f(n)))) ∧ real_measurable(Ω, S, «cutOff»(E, g))",
					By(
						measurable,
						event,
						measure,
						measure_space.MeasureOn.At(Ω, S, μ),
						gMeasurable,
						measurable_function.RealMeasurableOnEvent.AsFact().At(Ω, S, E))),
				"each cut function is measurable",
				"the cut limit is measurable")
			cutConvergesAE := a.Have(
				"the cut functions therefore converge almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. «cutOff»(E, f(n), x), «cutOff»(E, g, x)))",
				By(
					At(cutConvergence, E, f, g),
					converges,
					measure_space.AEMono.At(Ω, S, μ,
						a.TermAs[Set[A]]("λx:A. real_converges_to(λn:num. f(n, x), g(x))"),
						a.TermAs[Set[A]]("λx:A. real_converges_to(λn:num. «cutOff»(E, f(n), x), «cutOff»(E, g, x))"))))
			cutBound := a.Have(
				"a bound for an absolute value is nonnegative and also bounds the cut",
				"∀n:num. ∀x:A. |f(n, x)| ≤ h(x) ⇒ |«cutOff»(E, f(n), x)| ≤ h(x)",
				ByArith(real_sgn_abs.AbsNonneg))
			cutsDominated := a.Have(
				"the same integrable function dominates each cut almost everywhere",
				"∀n:num. measure_ae(Ω, S, μ, λx:A. |«cutOff»(E, f(n), x)| ≤ h(x))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"almost-everywhere monotonicity transfers the bound",
						By(
							cutBound.At(n),
							dominated.At(n),
							measure_space.AEMono.At(Ω, S, μ,
								b.TermAs[Set[A]]("λx:A. |f(n, x)| ≤ h(x)"),
								b.TermAs[Set[A]]("λx:A. |«cutOff»(E, f(n), x)| ≤ h(x)"))))
				}))
			a.Show(
				"dominated convergence for the cuts is convergence of the event integrals",
				Unfold(EventIntegralDef),
				By(
					cutsMeasurable[0],
					cutsDominated,
					measure,
					cutsMeasurable[1],
					cutConvergesAE,
					integrable,
					integral_convergence.DominatedConvergenceAE.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun2[Nat, A, Real]]("λn:num. «cutOff»(E, f(n))"),
						a.TermAs[Fun[A, Real]]("«cutOff»(E, g)"),
						h)))
		})
	}),
})}

// EventIntegralTailLimit — the integral of an integrable function g over the
// set where the absolute value of a measurable f exceeds an unbounded level
// tends to 0. Cut to the measurable part of that set inside Ω, g is bounded by
// |g|, and at each point the cut is 0 once the level passes |f(x)|, so
// dominated convergence over Ω carries the integrals to the integral of 0.
var EventIntegralTailLimit = eventIntegralTailLimitThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralTailLimit",
	Key:  "prop_b84eb3058cbdc173",
	Build: family.Sections(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → real). ∀c:(num → real).",
		Hypotheses: []string{
			"real_measurable(Ω, S, f)",
			"real_integrable(Ω, S, μ, g)",
			"∀B:real. ∃N:num. ∀n:num. N ≤ n ⇒ B ≤ c(n)",
		},
		Conclusion: "(λn:num. event_integral(Ω, S, μ, {x:A | c(n) < |f(x)|}, g)) ⟶ &0",
		Abbrev: Abbrev{
			{Name: "tail", Text: "λn:num. {x:A | x ∈ Ω ∧ c(n) < |f(x)|}"},
		},
	}), func(ctx *Script, headline string) *GoalStackNode {
		vanishing := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀f g:(A → real). ∀c:(num → real). ∀x:A.",
			Hypotheses: []string{"∀B:real. ∃N:num. ∀n:num. N ≤ n ⇒ B ≤ c(n)"},
			Conclusion: "(λn:num. «cutOff»({y:A | y ∈ Ω ∧ c(n) < |f(y)|}, g, x)) ⟶ &0",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			f, g *Arrow[A, Real],
			c *Arrow[Nat, Real],
			x *Expr[A],
			unbounded Fact,
		) {
			N, eventually := a.UnpackAs[Nat](unbounded.At(a.TermAs[Real]("|f(x)|")))
			vanishes := a.Have(
				"from N on the level is at least |f(x)|, so every cut there is 0",
				"∀n:num. N ≤ n ⇒ «cutOff»({y:A | y ∈ Ω ∧ c(n) < |f(y)|}, g, x) = &0",
				ByArith(eventually))
			zero := a.TermAs[Real]("&0")
			a.Show(
				"so the cuts agree from N on with the constant sequence 0, which tends to 0",
				By(
					vanishes,
					real_sequences.LimitConst.At(zero),
					real_sequences.LimitEventuallyEqual.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. &0"),
						a.TermAs[Fun[Nat, Real]]("λn:num. «cutOff»({y:A | y ∈ Ω ∧ c(n) < |f(y)|}, g, x)"),
						zero,
						N)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			measure Fact,
			f, g *Arrow[A, Real],
			c *Arrow[Nat, Real],
			measurable, integrable, unbounded Fact,
		) {
			sigma := a.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			carrier := a.Have(
				"so the carrier is an event",
				"Ω ∈ S",
				By(sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
			tails := a.Have(
				"each tail is an upper ray of the measurable |f|, so an event",
				"∀n:num. «tail»(n) ∈ S",
				By(
					sigma,
					measurable,
					measurable_function.RealMeasurableAbs.At(Ω, S, f),
					measurable_function.RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|"))))
			cutsMeasurable := a.Have(
				"g cut to each tail is measurable",
				"∀n:num. real_measurable(Ω, S, «cutOff»(«tail»(n), g))",
				By(
					tails,
					sigma,
					integrable,
					measure_integral.RealIntegrableDef.At(Ω, S, μ, g),
					measurable_function.RealMeasurableOnEvent.AsFact().At(Ω, S)))
			convergesAE := a.Have(
				"the cuts tend to 0 at every point, so almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. (λn:num. «cutOff»(«tail»(n), g, x)) ⟶ &0)",
				By(
					measure,
					unbounded,
					At(vanishing, Ω, f, g, c),
					measure_space.AEOfEverywhere.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. (λn:num. «cutOff»(«tail»(n), g, x)) ⟶ &0"))))
			dominated := a.Have(
				"|g| bounds every cut at every point, so almost everywhere",
				"∀n:num. measure_ae(Ω, S, μ, λx:A. |«cutOff»(«tail»(n), g, x)| ≤ |g(x)|)",
				ByArith(measure, measure_space.AEOfEverywhere))
			limit := a.Have(
				"dominated convergence over Ω takes the integrals of the cuts to that of 0",
				"(λn:num. event_integral(Ω, S, μ, Ω, «cutOff»(«tail»(n), g))) ⟶ "+
					"event_integral(Ω, S, μ, Ω, λx:A. &0)",
				By(
					measure,
					carrier,
					cutsMeasurable,
					convergesAE,
					dominated,
					integrable,
					sigma,
					measurable_function.RealMeasurableConst.At(Ω, S, a.TermAs[Real]("&0")),
					measure_integral.IntegrableAbs.At(Ω, S, μ, g),
					EventIntegralDominatedConvergence.At(
						Ω,
						S,
						μ,
						Ω,
						a.TermAs[Fun2[Nat, A, Real]]("λn:num. «cutOff»(«tail»(n), g)"),
						a.TermAs[Fun[A, Real]]("λx:A. &0"),
						a.TermAs[Fun[A, Real]]("λx:A. |g(x)|"))))
			agree := a.Have(
				"on Ω, cutting to a tail is cutting to where |f| exceeds the level",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ «cutOff»(«tail»(n), g, x) = «cutOff»({y:A | c(n) < |f(y)|}, g, x)",
				BySets())
			same := a.Have(
				"so the integral over Ω of each cut is the integral of g over that set",
				"∀n:num. "+
					"    event_integral(Ω, S, μ, Ω, «cutOff»(«tail»(n), g)) = "+
					"    event_integral(Ω, S, μ, {x:A | c(n) < |f(x)|}, g)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					exceeds := b.TermAs[Set[A]]("{y:A | c(n) < |f(y)|}")
					cut := b.TermAs[Fun[A, Real]]("«cutOff»({y:A | c(n) < |f(y)|}, g)")
					b.Show(
						"the cuts agree on Ω, and over Ω the cut to a set integrates as g over it",
						By(
							agree.At(n),
							EventIntegralEqOn.At(Ω, S, μ, Ω, b.TermAs[Fun[A, Real]]("«cutOff»(«tail»(n), g)"), cut),
							EventIntegralCarrier.At(Ω, S, μ, cut),
							EventIntegralDef.At(Ω, S, μ, exceeds, g)))
				}))
			zero := a.Have(
				"0 integrates to 0 over the carrier",
				"event_integral(Ω, S, μ, Ω, λx:A. &0) = &0",
				ByArith(measure, carrier, EventIntegralConst.At(Ω, S, μ, Ω, a.TermAs[Real]("&0"))))
			a.Show(
				"the integrals over the tails are those of the cuts, which tend to 0",
				By(limit, same, zero))
		})
	}),
})}

// EventIntegralL1Limit — convergence in L¹ over the whole carrier carries the
// integrals over every measurable event along. Cutting two functions to an
// event does not increase their distance at any point, so the distances of the
// cuts lie between 0 and those of the functions and tend to 0, and the
// integrals of the cuts converge to that of the cut limit.
var EventIntegralL1Limit = eventIntegralL1LimitThm{family.Add(registry.ProofEntry{
	Name: "EventIntegralL1Limit",
	Key:  "prop_6ef2cb4472af06aa",
	Reading: "The distance is that of the functions over the whole carrier, not over E: " +
		"convergence in L¹ on Ω gives convergence of the integrals over every measurable event. " +
		"Integrability of the f(n) and of g is load-bearing: for counting measure on ℕ, the " +
		"function equal to 1 at 0 and to −1 elsewhere stands at a distance read as 0 from the " +
		"zero function, and its integral is read as 1. E ∈ S is what makes the cuts integrable.",
	Build: family.Sections(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀E:set(A). ∀f:(num → A → real). ∀g:(A → real).",
		Hypotheses: []string{
			"E ∈ S",
			"∀n:num. real_integrable(Ω, S, μ, f(n))",
			"real_integrable(Ω, S, μ, g)",
			"real_converges_to(λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|), &0)",
		},
		Conclusion: "real_converges_to(λn:num. event_integral(Ω, S, μ, E, f(n)), " +
			"    event_integral(Ω, S, μ, E, g))",
		Abbrev: Abbrev{
			{Name: "cutDistance", Text: "λn:num. " +
				"    measure_integral(Ω, S, μ, λx:A. |«cutOff»(E, f(n), x) - «cutOff»(E, g, x)|)"},
		},
	}), func(ctx *Script, headline string) *GoalStackNode {
		pointwise := ctx.Lemma(
			"∀E:set(A). ∀f:(num → A → real). ∀g:(A → real). ∀n:num. ∀x:A. "+
				"    |«cutOff»(E, f(n), x) - «cutOff»(E, g, x)| ≤ |f(n, x) - g(x)|",
			func(
				a *Argument,
				E *Expr[Set[A]],
				f *Arrow2[Nat, A, Real],
				g *Arrow[A, Real],
				n *Expr[Nat],
				x *Expr[A],
			) {
				a.Cases(a.TermAs[Bool]("x ∈ E"))
				a.When(
					"on E the cuts are the functions",
					func(b *Argument, inside Fact) {
						b.Show(
							"so the two distances agree",
							ByArith(inside))
					})
				a.Otherwise(
					"off E both cuts are 0",
					func(b *Argument, outside Fact) {
						b.Show(
							"so the distance of the cuts is 0, which no distance is below",
							ByArith(outside))
					})
			})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			E *Expr[Set[A]],
			f *Arrow2[Nat, A, Real],
			g *Arrow[A, Real],
			measure, event, integrable, integrableG, converges Fact,
		) {
			cuts := a.Conjuncts(
				a.Have(
					"the cuts of the f(n) and of g to E are integrable",
					"(∀n:num. real_integrable(Ω, S, μ, «cutOff»(E, f(n)))) ∧ real_integrable(Ω, S, μ, «cutOff»(E, g))",
					By(
						measure,
						measure_space.MeasureOn.At(Ω, S, μ),
						event,
						integrable,
						integrableG,
						IntegrableOnEvent)),
				"each cut function is integrable",
				"the cut limit is integrable")
			distances := a.Have(
				"so are the distances of the cuts, as are those of the functions",
				"∀n:num. "+
					"    real_integrable(Ω, S, μ, λx:A. |«cutOff»(E, f(n), x) - «cutOff»(E, g, x)|) ∧ "+
					"    real_integrable(Ω, S, μ, λx:A. |f(n, x) - g(x)|)",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						measure,
						measure_space.MeasureOn.At(Ω, S, μ),
						cuts[0].At(n),
						cuts[1],
						integrable.At(n),
						integrableG,
						measure_integral.IntegrableSub,
						measure_integral.IntegrableAbs)
				}))
			squeezed := a.Have(
				"each distance of the cuts lies between 0 and the distance of the functions",
				"∀n:num. "+
					"    &0 ≤ «cutDistance»(n) ∧ «cutDistance»(n) ≤ measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|)",
				a.ForEach(func(n *Expr[Nat]) Action {
					return By(
						distances.At(n),
						At(pointwise, E, f, g),
						measure_integral.IntegralNonneg,
						real_sgn_abs.AbsNonneg,
						measure_integral.IntegralMono)
				}))
			zero := a.TermAs[Real]("&0")
			firstIndex := a.TermAs[Nat]("0")
			toZero := a.Have(
				"so, squeezed from index 0 on, the distances of the cuts tend to 0",
				"real_converges_to(«cutDistance», &0)",
				By(
					squeezed,
					converges,
					real_sequences.LimitConst.At(zero),
					real_sequences.LimitSqueeze.At(
						a.TermAs[Fun[Nat, Real]]("λn:num. &0"),
						a.TermAs[Fun[Nat, Real]]("«cutDistance»"),
						a.TermAs[Fun[Nat, Real]]("λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|)"),
						zero,
						firstIndex)))
			a.Show(
				"the integrals of the cuts converge to that of the cut limit",
				Unfold(EventIntegralDef),
				By(
					measure,
					cuts[0],
					cuts[1],
					toZero,
					integral_convergence.IntegralL1Limit.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun2[Nat, A, Real]]("λn:num. «cutOff»(E, f(n))"),
						a.TermAs[Fun[A, Real]]("«cutOff»(E, g)"))))
		})
	}),
})}
