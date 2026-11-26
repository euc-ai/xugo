// laws.go — the laws of conditional expectation read from its definition
// alone: a G-measurable integrable function is its own conditional
// expectation, linear combinations of related pairs are related, related
// functions have the same integral, and conditional expectations preserve
// almost-everywhere order and are unique almost everywhere.

package conditional_expectation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// CondExpIdentity — an integrable function measurable for G is its own conditional expectation.
var CondExpIdentity = condExpIdentityThm{family.Add(registry.ProofEntry{
	Name: "CondExpIdentity",
	Key:  "prop_c3bdc7968fa4d312",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_integrable(Ω, S, μ, X)",
			"real_measurable(Ω, G, X)",
		},
		Conclusion: "is_cond_exp(Ω, S, μ, G, X, X)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		X *Arrow[A, Real],
		h Fact,
	) {
		a.Show(
			"the hypotheses give the relation conditions, and each event integral equals itself",
			By(h, IsCondExpDef.At(Ω, S, μ, G, X, X)))
	}),
})}

// CondExpLinear — conditional expectations respect linear combinations, by event-integral linearity.
var CondExpLinear = condExpLinearThm{family.Add(registry.ProofEntry{
	Name: "CondExpLinear",
	Key:  "prop_a0f8e02a942e2927",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y U V:(A → real). " +
			"∀a b:real.",
		Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "is_cond_exp(Ω, S, μ, G, U, V)"},
		Conclusion: "is_cond_exp(Ω, S, μ, G, λx:A. a * X(x) + b * U(x), λx:A. a * Y(x) + b * V(x))",
	}, func(
		arg *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		X, Y, U, V *Arrow[A, Real],
		a, b *Expr[Real],
		h Fact,
	) {
		relations := arg.Conjuncts(
			h,
			"X has conditional expectation Y",
			"U has conditional expectation V")
		xy := arg.Conjuncts(
			arg.Unfolded(relations[0], IsCondExpDef),
			"the ambient measure",
			"the conditioning sigma algebra",
			"conditioning events are ambient events",
			"X is integrable",
			"Y is integrable",
			"Y is measurable for G",
			"X and Y agree on event integrals")
		uv := arg.Unfolded(relations[1], IsCondExpDef)
		measure, sigma, included := xy[0], xy[1], xy[2]
		integrableX, integrableY, measurableY, eventsXY := xy[3], xy[4], xy[5], xy[6]
		aX := arg.TermAs[Fun[A, Real]]("λx:A. a * X(x)")
		aY := arg.TermAs[Fun[A, Real]]("λx:A. a * Y(x)")
		bU := arg.TermAs[Fun[A, Real]]("λx:A. b * U(x)")
		bV := arg.TermAs[Fun[A, Real]]("λx:A. b * V(x)")
		input := arg.TermAs[Fun[A, Real]]("λx:A. a * X(x) + b * U(x)")
		output := arg.TermAs[Fun[A, Real]]("λx:A. a * Y(x) + b * V(x)")
		scaled := arg.Have(
			"the four scaled functions are integrable",
			"real_integrable(Ω, S, μ, λx:A. a * X(x)) ∧ "+
				"real_integrable(Ω, S, μ, λx:A. a * Y(x)) ∧ "+
				"real_integrable(Ω, S, μ, λx:A. b * U(x)) ∧ "+
				"real_integrable(Ω, S, μ, λx:A. b * V(x))",
			By(
				uv,
				integrableX,
				integrableY,
				measure_integral.IntegrableScale.At(Ω, S, μ, X, a),
				measure_integral.IntegrableScale.At(Ω, S, μ, Y, a),
				measure_integral.IntegrableScale.At(Ω, S, μ, U, b),
				measure_integral.IntegrableScale.At(Ω, S, μ, V, b)))
		measurable := arg.Have(
			"the output combination is measurable for G",
			"real_measurable(Ω, G, λx:A. a * Y(x) + b * V(x))",
			By(
				uv,
				measurableY,
				measurable_function.RealMeasurableScale.At(Ω, G, Y, a),
				measurable_function.RealMeasurableScale.At(Ω, G, V, b),
				measurable_function.RealMeasurableAdd.At(Ω, G, aY, bV)))
		events := arg.Have(
			"the combinations agree on every conditioning event",
			Statement{
				Binders:    "∀E:set(A).",
				Hypotheses: []string{"E ∈ G"},
				Conclusion: "event_integral(Ω, S, μ, E, λx:A. a * X(x) + b * U(x)) = " +
					"event_integral(Ω, S, μ, E, λx:A. a * Y(x) + b * V(x))",
			},
			Derive(func(d *Argument) {
				E := d.FixAs[Set[A]]("E")
				inG := d.Assume()
				inS := d.Have(
					"the conditioning event is ambient measurable",
					"E ∈ S",
					BySets(inG, included))
				d.Show(
					"linearity carries the two event identities to the combinations",
					CalcEq(
						Leg(
							d.TermAs[Real]("a * event_integral(Ω, S, μ, E, X) + b * event_integral(Ω, S, μ, E, U)"),
							"expand the input event integral",
							By(
								inS,
								scaled,
								measure,
								event_integral.EventIntegralAdd.At(Ω, S, μ, E, aX, bU),
								event_integral.EventIntegralScale.At(Ω, S, μ, E, X, a),
								event_integral.EventIntegralScale.At(Ω, S, μ, E, U, b))),
						Leg(
							d.TermAs[Real]("a * event_integral(Ω, S, μ, E, Y) + b * event_integral(Ω, S, μ, E, V)"),
							"use the two defining event identities",
							By(eventsXY.At(E), inG, uv)),
						FinalLeg(
							"reassemble the output event integral",
							By(
								inS,
								scaled,
								measure,
								event_integral.EventIntegralAdd.At(Ω, S, μ, E, aY, bV),
								event_integral.EventIntegralScale.At(Ω, S, μ, E, Y, a),
								event_integral.EventIntegralScale.At(Ω, S, μ, E, V, b)))))
			}))
		arg.Show(
			"integrability, G-measurability, and the event identities give the relation",
			By(
				events,
				sigma,
				included,
				scaled,
				measure,
				measurable,
				measure_integral.IntegrableAdd.At(Ω, S, μ, aX, bU),
				measure_integral.IntegrableAdd.At(Ω, S, μ, aY, bV),
				IsCondExpDef.At(Ω, S, μ, G, input, output)))
	}),
})}

// CondExpIntegral — conditional expectation preserves the integral, by the event identity on the carrier.
var CondExpIntegral = condExpIntegralThm{family.Add(registry.ProofEntry{
	Name: "CondExpIntegral",
	Key:  "prop_d2b721429393c731",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y:(A → real).",
		Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)"},
		Conclusion: "measure_integral(Ω, S, μ, X) = measure_integral(Ω, S, μ, Y)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		X, Y *Arrow[A, Real],
		h Fact,
	) {
		a.Show(
			"the event identity on the whole carrier gives equality of the integrals",
			By(
				h,
				IsCondExpDef.At(Ω, S, μ, G, X, Y),
				sigma_algebra.SigmaAlgebraOnDef.At(Ω, G),
				event_integral.EventIntegralCarrier.At(Ω, S, μ, X),
				event_integral.EventIntegralCarrier.At(Ω, S, μ, Y)))
	}),
})}

// CondExpMono — almost-everywhere order is preserved by conditional
// expectation. On the conditioning event where Y exceeds V, comparison
// of the input integrals bounds the integral of Y − V above by zero.
// Its cut to that event is nonnegative, so it vanishes almost everywhere.
var CondExpMono = condExpMonoThm{family.Add(registry.ProofEntry{
	Name: "CondExpMono",
	Key:  "prop_1940e0def727787c",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y U V:(A → real).",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"is_cond_exp(Ω, S, μ, G, U, V)",
			"measure_ae(Ω, S, μ, λx:A. X(x) ≤ U(x))",
		},
		Conclusion: "measure_ae(Ω, S, μ, λx:A. Y(x) ≤ V(x))",
		Abbrev: Abbrev{
			{Name: "difference", Text: "λx:A. Y(x) - V(x)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		X, Y, U, V *Arrow[A, Real],
		first, second, order Fact,
	) {
		ys := a.Conjuncts(
			a.Unfolded(first, IsCondExpDef),
			"the ambient measure",
			"the conditioning sigma algebra",
			"conditioning events are ambient events",
			"X is integrable",
			"Y is integrable",
			"Y is measurable for G",
			"Y has the event integrals of X")
		vs := a.Unfolded(second, IsCondExpDef)
		measure, sigma, included := ys[0], ys[1], ys[2]
		integrableX, integrableY, measurableY, eventsY := ys[3], ys[4], ys[5], ys[6]
		difference := a.TermAs[Fun[A, Real]]("«difference»")
		measurable := a.Have(
			"Y − V is measurable for G, as Y plus the negative of V",
			"real_measurable(Ω, G, «difference»)",
			Simp(Fwd(real_ring.RealSubDef)),
			By(
				sigma,
				measurableY,
				vs,
				measurable_function.RealMeasurableNeg.At(Ω, G, V),
				measurable_function.RealMeasurableAdd.At(Ω, G, Y, a.TermAs[Fun[A, Real]]("λx:A. -V(x)"))))
		E, eDef := a.LetAs[Set[A]]("E", "{x:A | x ∈ Ω ∧ &0 < Y(x) - V(x)}")
		inG := a.Have(
			"the set where Y exceeds V is a conditioning event",
			"E ∈ G",
			Simp(Fwd(eDef)),
			By(sigma, measurable, measurable_function.RealMeasurableIffRay.At(Ω, G, difference)))
		inS := a.Have(
			"so E is an ambient event",
			"E ∈ S",
			BySets(inG, included))
		members := a.Have(
			"E holds the points of Ω where Y exceeds V",
			"∀x:A. x ∈ E ⇔ x ∈ Ω ∧ &0 < Y(x) - V(x)",
			BySets(eDef))
		inputOrder := a.Have(
			"X lies below U almost everywhere, so their integrals over E compare",
			"event_integral(Ω, S, μ, E, X) ≤ event_integral(Ω, S, μ, E, U)",
			By(measure, integrableX, vs, order, event_integral.EventIntegralMonoAE.At(Ω, S, μ, E, X, U)))
		outputOrder := a.Have(
			"the defining event identities on E give the same order for Y and V",
			"event_integral(Ω, S, μ, E, Y) ≤ event_integral(Ω, S, μ, E, V)",
			By(inG, inputOrder, eventsY.At(E), vs))
		eventNonpos := a.Have(
			"the integral of Y − V over E is therefore nonpositive",
			"event_integral(Ω, S, μ, E, «difference») ≤ &0",
			ByArith(
				inS,
				measure,
				integrableY,
				vs,
				outputOrder,
				event_integral.EventIntegralSub.At(Ω, S, μ, E, Y, V)))
		h, hDef := a.LetAs[Fun[A, Real]]("h", "λx:A. COND(x ∈ E, Y(x) - V(x), &0)")
		positivePart := a.Have(
			"on Ω the cut h is the positive part of Y − V",
			"∀x:A. x ∈ Ω ⇒ h(x) = max(Y(x) - V(x), &0)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Cases(b.Term("x ∈ E"))
				b.When(
					"on E, h is Y − V",
					func(c *Argument, inE Fact) {
						c.Show(
							"which is positive there",
							Simp(Fwd(hDef)),
							ByArith(inE, members.At(x)))
					})
				b.Otherwise(
					"off E, h is 0",
					func(c *Argument, outside Fact) {
						c.Show(
							"and Y − V is not positive at a point of Ω outside E",
							Simp(Fwd(hDef)),
							ByArith(inΩ, outside, members.At(x)))
					})
			}))
		nonneg := a.Have(
			"so h is nonnegative on Ω",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ h(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"a positive part is nonnegative",
					ByArith(inΩ, positivePart.At(x)))
			}))
		integrable := a.Have(
			"h is integrable, the cut of the integrable Y − V to the ambient event E",
			"real_integrable(Ω, S, μ, h)",
			By(
				hDef,
				inS,
				measure,
				integrableY,
				vs,
				measure_space.MeasureOn.At(Ω, S, μ),
				measure_integral.IntegrableSub.At(Ω, S, μ, Y, V),
				event_integral.IntegrableOnEvent.At(Ω, S, μ, E, difference)))
		realIntegralZero := a.Have(
			"the integral of the nonnegative cut h is nonnegative and equals the nonpositive event integral",
			"measure_integral(Ω, S, μ, h) = &0",
			ByArith(
				nonneg,
				hDef,
				eventNonpos,
				measure_integral.IntegralNonneg.At(Ω, S, μ, h),
				event_integral.EventIntegralDef.At(Ω, S, μ, E, difference)))
		integralZero := a.Have(
			"embedding the integral of h gives zero in the extended nonnegative reals",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(h(x))) = &0",
			By(realIntegralZero, integrable, nonneg, measure_integral.IntegralNonnegEmbedding.At(Ω, S, μ, h)))
		vanishes := a.Have(
			"a nonnegative measurable function with integral 0 vanishes almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. extended_of_real(h(x)) = &0)",
			By(
				integralZero,
				measure,
				integrable,
				measure_space.MeasureOn.At(Ω, S, μ),
				measure_integral.RealIntegrableDef.At(Ω, S, μ, h),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, h),
				nonneg_integral.IntegralZeroIffAE.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(h(x))"))))
		pointwise := a.Have(
			"where h vanishes, Y lies below V",
			"∀x:A. x ∈ Ω ∧ extended_of_real(h(x)) = &0 ⇒ Y(x) ≤ V(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				vanishing := b.Assume()
				b.Show(
					"the embedding is one-to-one on the nonnegative reals, so the positive part of Y − V is 0 at x",
					ByArith(
						vanishing,
						positivePart.At(x),
						extended_nonneg_real.OfRealInjective.At(b.TermAs[Real]("h(x)"), b.TermAs[Real]("&0"))))
			}))
		a.Show(
			"so Y lies below V almost everywhere",
			By(vanishes, pointwise, measure_space.AEMono))
	}),
})}

// CondExpUnique — two conditional expectations of one function agree almost
// everywhere: the two-sided corollary of CondExpMono. X lies below itself
// almost everywhere, so each of Y and Z lies below the other.
var CondExpUnique = condExpUniqueThm{family.Add(registry.ProofEntry{
	Name: "CondExpUnique",
	Key:  "prop_1d558aff5408e10c",
	Reading: "No finiteness is read: {Y > Z} is a G-event because both are " +
		"genuinely G-measurable, and both are integrable inside is_cond_exp.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y Z:(A → real).",
		Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "is_cond_exp(Ω, S, μ, G, X, Z)"},
		Conclusion: "measure_ae_eq(Ω, S, μ, Y, Z)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		X, Y, Z *Arrow[A, Real],
		first, second Fact,
	) {
		reflexive := a.Have(
			"X lies below itself almost everywhere, μ being a measure as is_cond_exp asks",
			"measure_ae(Ω, S, μ, λx:A. X(x) ≤ X(x))",
			By(
				first,
				IsCondExpDef.At(Ω, S, μ, G, X, Y),
				real_order_ring.LessEqRefl,
				measure_space.AEOfEverywhere.At(Ω, S, μ, a.TermAs[Set[A]]("λx:A. X(x) ≤ X(x)"))))
		joint := a.Have(
			"monotonicity puts each of Y and Z below the other "+
				"almost everywhere, and both bounds hold together",
			"measure_ae(Ω, S, μ, λx:A. Y(x) ≤ Z(x) ∧ Z(x) ≤ Y(x))",
			By(
				first,
				second,
				reflexive,
				CondExpMono.At(Ω, S, μ, G, X, Y, X, Z),
				CondExpMono.At(Ω, S, μ, G, X, Z, X, Y),
				IsCondExpDef.At(Ω, S, μ, G, X, Y),
				measure_space.AEConjunction))
		a.Show(
			"where both bounds hold, Y and Z agree",
			ByArith(
				joint,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, Bool]]("λx:A. Y(x) ≤ Z(x) ∧ Z(x) ≤ Y(x)"),
					a.TermAs[Fun[A, Bool]]("λx:A. Y(x) = Z(x)")),
				measure_space.AEEqualDef.At(Ω, S, μ, Y, Z)))
	}),
})}
