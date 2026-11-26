// optional_sampling.go — bounded optional sampling: sampling a martingale at
// two ordered bounded stopping times gives a conditional expectation over the
// earlier stopped sigma algebra. Each stopped increment cancels over an
// earlier stopped event, and the increments telescope to the terminal values.
// Sampled against the zero time it keeps the expectation of a martingale stopped
// and observed at a finite time, and so of one stopped at a time almost
// everywhere bounded.

package optional_stopping

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/stopping_time"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// OptionalSamplingBounded — sampling a martingale at two ordered bounded stopping
// times gives a conditional expectation over the earlier stopped sigma algebra.
// The difference of the stopped increments is the original increment on {U≤n<T};
// its integral over an earlier stopped event vanishes, and induction reaches the bound.
var OptionalSamplingBounded = optionalSamplingBoundedThm{family.Add(registry.ProofEntry{
	Name: "OptionalSamplingBounded",
	Key:  "prop_64dd5997ab21d0a1",
	Reading: "The bounds and order hold at every point of the carrier. This avoids assuming " +
		"completeness of the filtration when using the stopped sigma algebra. No finiteness of μ is read.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀U T:(A → option(num)). " +
			"∀N:num.",
		Hypotheses: []string{
			"martingale_on(Ω, S, μ, F, M)",
			"stopping_time_on(Ω, F, U)",
			"stopping_time_on(Ω, F, T)",
			"∀x:A. x ∈ Ω ⇒ stopping_time_le(U(x), T(x)) ∧ stopping_time_le(T(x), some(N))",
		},
		Conclusion: "is_cond_exp(Ω, " +
			"    S, " +
			"    μ, " +
			"    stopped_sigma(Ω, S, F, U), " +
			"    stopped_value(M, T), " +
			"    stopped_value(M, U))",
	}, func(ctx *Script, headline string) *GoalStackNode {
		zeroIndex := ctx.Lemma("∀t:option(num). stopping_time_min_nat(t, 0) = 0", func(a *Argument) {
			zeroBound := a.Have(
				"zero is the only natural number below zero",
				"∀k:num. k ≤ 0 ⇔ k = 0",
				ByArith())
			a.Show(
				"truncation at zero always selects zero",
				By(zeroBound, stopping_time.TimeMinNatDef))
		})
		stoppedZero := ctx.Lemma("∀M:(num → A → real). ∀T:(A → option(num)). "+
			"    stopped_process(M, T, 0) = M(0)", func(a *Argument) {
			a.Show(
				"every stopped process starts at the original initial value",
				By(stopping_time.StoppedProcessDef, zeroIndex))
		})
		stoppedRecurrence := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀M:(num → A → real). ∀T:(A → option(num)). ∀n:num. ∀x:A.",
			Hypotheses: []string{"x ∈ Ω"},
			Conclusion: "stopped_process(M, T, n + 1, x) = " +
				"COND(x ∈ «running», M(n + 1, x) - M(n, x), &0) + stopped_process(M, T, n, x)",
			Abbrev: Abbrev{{Name: "running", Text: "Ω ∖ {y:A | y ∈ Ω ∧ stopping_time_le(T(y), some(n))}"}},
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			n *Expr[Nat],
			x *Expr[A],
			inΩ Fact,
		) {
			a.Show(
				"the next stopped value adds the increment on the event of still running",
				BySets(
					inΩ,
					stopping_time.StoppedIncrement.At(M, T, n, x),
					real_ring.EqSubRightAdd.At(a.TermAs[Real]("stopped_process(M, T, n + 1, x)"),
						a.TermAs[Real]("stopped_process(M, T, n, x)"),
						a.TermAs[Real]("COND(x ∈ «running», M(n + 1, x) - M(n, x), &0)"))))
		})
		stoppedIntegrable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀M:(num → A → real). " +
				"∀T:(A → option(num)). " +
				"∀n:num.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"∀k:num. real_integrable(Ω, S, μ, M(k))",
				"∀k:num. {x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(k))} ∈ S",
			},
			Conclusion: "real_integrable(Ω, S, μ, stopped_process(M, T, n))",
			Abbrev: Abbrev{
				{Name: "running", Text: "Ω ∖ {y:A | y ∈ Ω ∧ stopping_time_le(T(y), some(n))}"},
				{Name: "cutIncrement", Text: "λx:A. COND(x ∈ «running», M(n + 1, x) - M(n, x), &0)"},
			},
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			n *Expr[Nat],
			h Fact,
		) {
			sigma := a.Have(
				"a measure is defined on a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(h, measure_space.MeasureOn.At(Ω, S, μ)))
			a.Induct(n)
			a.Base(
				"the initial stopped value is integrable",
				Simp(Fwd(stoppedZero)),
				By(h))
			a.Step(
				"the next stopped increment preserves integrability",
				func(b *Argument, ih Fact) {
					running := b.Have(
						"the event of still running is measurable",
						"«running» ∈ S",
						By(h, sigma, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
					increment := b.Have(
						"a difference of process values is integrable",
						"real_integrable(Ω, S, μ, λx:A. M(n + 1, x) - M(n, x))",
						By(
							h,
							measure_integral.IntegrableSub.At(
								Ω, S, μ, b.TermAs[Fun[A, Real]]("M(n + 1)"), b.TermAs[Fun[A, Real]]("M(n)"))))
					cut := b.Have(
						"restricting the increment to the running event preserves integrability",
						"real_integrable(Ω, S, μ, «cutIncrement»)",
						By(
							running,
							sigma,
							increment,
							event_integral.IntegrableOnEvent.At(
								Ω, S, μ, b.TermAs[Set[A]]("«running»"), b.TermAs[Fun[A, Real]]("λx:A. M(n + 1, x) - M(n, x)"))))
					sum := b.Have(
						"adding the restricted increment preserves integrability",
						"real_integrable(Ω, S, μ, λx:A. «cutIncrement»(x) + stopped_process(M, T, n, x))",
						By(
							h,
							ih,
							cut,
							measure_integral.IntegrableAdd.At(
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("«cutIncrement»"),
								b.TermAs[Fun[A, Real]]("stopped_process(M, T, n)"))))
					next := b.Have(
						"the successor cutoff is n plus one",
						"suc(n) = n + 1",
						ByArith())
					b.Show(
						"the stopped recurrence identifies the integrable sum on the carrier",
						By(
							next,
							sum,
							At(stoppedRecurrence, Ω, M, T, n),
							measure_integral.RealIntegrableEqOn.At(Ω, S, μ,
								b.TermAs[Fun[A, Real]]("λx:A. «cutIncrement»(x) + stopped_process(M, T, n, x)"),
								b.TermAs[Fun[A, Real]]("stopped_process(M, T, suc(n))"))))
				})
		})
		conditionalDifference := ctx.Lemma(Statement{
			Binders:    "∀u t:option(num). ∀n:num. ∀d:real.",
			Hypotheses: []string{"stopping_time_le(u, t)"},
			Conclusion: "COND(stopping_time_le(t, some(n)), &0, d) - " +
				"COND(stopping_time_le(u, some(n)), &0, d) = " +
				"COND(stopping_time_le(u, some(n)) ∧ ¬stopping_time_le(t, some(n)), d, &0)",
		}, func(a *Argument, u, t *Expr[Option[Nat]], n *Expr[Nat], d *Expr[Real], ordered Fact) {
			a.Show(
				"the two stopped increments differ exactly between the stopping times",
				By(
					ordered,
					stopping_time.TimeLeTrans.At(u, t, a.TermAs[Option[Nat]]("some(n)")),
					real_ring.SubRefl,
					real_ring.SubRightZero))
		})
		incrementDifference := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀M:(num → A → real). ∀U T:(A → option(num)). ∀n:num. ∀x:A.",
			Hypotheses: []string{"x ∈ Ω", "stopping_time_le(U(x), T(x))"},
			Conclusion: "(stopped_process(M, T, n + 1, x) - stopped_process(M, T, n, x)) - " +
				"(stopped_process(M, U, n + 1, x) - stopped_process(M, U, n, x)) = " +
				"COND(x ∈ «between», M(n + 1, x) - M(n, x), &0)",
			Abbrev: Abbrev{
				{Name: "between", Text: "{y:A | y ∈ Ω ∧ stopping_time_le(U(y), some(n))} ∖ " +
					"{y:A | y ∈ Ω ∧ stopping_time_le(T(y), some(n))}"},
			},
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			M *Arrow2[Nat, A, Real],
			U, T *Arrow[A, Option[Nat]],
			n *Expr[Nat],
			x *Expr[A],
			h Fact,
		) {
			a.Show(
				"subtracting stopped increments restricts the original increment to U≤n<T",
				BySets(
					h,
					stopping_time.StoppedIncrement.At(M, T, n, x),
					stopping_time.StoppedIncrement.At(M, U, n, x),
					At(conditionalDifference, U.Apply(x), T.Apply(x), n, a.TermAs[Real]("M(n + 1, x) - M(n, x)"))))
		})
		conditionalIncrement := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S G:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀f g:(A → real). " +
				"∀E:set(A).",
			Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, f, g)", "E ∈ G"},
			Conclusion: "event_integral(Ω, S, μ, E, λx:A. f(x) - g(x)) = &0",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S, G *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			f, g *Arrow[A, Real],
			E *Expr[Set[A]],
			h Fact,
		) {
			data := a.Unfolded(h, conditional_expectation.IsCondExpDef)
			inS := a.Have(
				"the conditioning event belongs to the ambient sigma algebra",
				"E ∈ S",
				BySets(data))
			a.Show(
				"the defining event integrals cancel",
				By(inS, data, event_integral.EventIntegralSub.At(Ω, S, μ, E, f, g), real_ring.SubRefl))
		})
		eventDifferenceZero := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀F:(num → set(set(A))). " +
				"∀M:(num → A → real). " +
				"∀U T:(A → option(num)). " +
				"∀E:set(A). " +
				"∀n:num.",
			Hypotheses: []string{
				"martingale_on(Ω, S, μ, F, M)",
				"stopping_time_on(Ω, F, T)",
				"∀x:A. x ∈ Ω ⇒ stopping_time_le(U(x), T(x))",
				"E ∈ stopped_sigma(Ω, S, F, U)",
			},
			Conclusion: "event_integral(Ω, S, μ, E, «incrementDifference») = &0",
			Abbrev: Abbrev{
				{Name: "earlier", Text: "{x:A | x ∈ Ω ∧ stopping_time_le(U(x), some(n))}"},
				{Name: "later", Text: "{x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(n))}"},
				{Name: "between", Text: "«earlier» ∖ «later»"},
				{Name: "incrementDifference", Text: "λx:A. " +
					"    (stopped_process(M, T, n + 1, x) - stopped_process(M, T, n, x)) - " +
					"    (stopped_process(M, U, n + 1, x) - stopped_process(M, U, n, x))"},
			},
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			U, T *Arrow[A, Option[Nat]],
			E *Expr[Set[A]],
			n *Expr[Nat],
			h Fact,
		) {
			parts := a.Conjuncts(
				h,
				"martingale",
				"later stopping time",
				"ordered times",
				"earlier stopped event")
			step := a.Have(
				"at time n the next value has the present value as conditional expectation",
				"sigma_algebra_on(Ω, F(n)) ∧ is_cond_exp(Ω, S, μ, F(n), M(n + 1), M(n))",
				By(parts[0], martingale.MartingaleDef.At(Ω, S, μ, F, M), filtration.FiltrationDef.At(Ω, S, F)))
			events := a.Have(
				"both cut events belong to the time n sigma algebra",
				"E ∩ «earlier» ∈ F(n) ∧ «later» ∈ F(n)",
				BySets(
					parts[3],
					parts[1],
					stopping_time.StoppedSigmaDef.At(Ω, S, F, U),
					stopping_time.StoppingTimeDef.At(Ω, F, T)))
			between := a.Have(
				"the part of E between the stopping times is known at time n",
				"E ∩ «between» ∈ F(n)",
				Derive(func(b *Argument) {
					same := b.Have(
						"intersecting E with the interval is a difference of known events",
						"E ∩ «between» = (E ∩ «earlier») ∖ «later»",
						BySets())
					b.Show(
						"the time n sigma algebra is closed under difference",
						same.Rw(),
						By(events, step, sigma_algebra.SigmaFiniteOperations.At(Ω, a.TermAs[Set[Set[A]]]("F(n)"))))
				}))
			cutZero := a.Have(
				"the restricted increment has zero integral over E",
				"event_integral(Ω, S, μ, E, λx:A. COND(x ∈ «between», M(n + 1, x) - M(n, x), &0)) = &0",
				By(
					between,
					step,
					At(
						conditionalIncrement,
						Ω,
						S,
						a.TermAs[Set[Set[A]]]("F(n)"),
						μ,
						a.TermAs[Fun[A, Real]]("M(n + 1)"),
						a.TermAs[Fun[A, Real]]("M(n)"),
						a.TermAs[Set[A]]("E ∩ «between»")),
					event_integral.EventIntegralRestrict.At(
						Ω, S, μ, E, a.TermAs[Set[A]]("«between»"), a.TermAs[Fun[A, Real]]("λx:A. M(n + 1, x) - M(n, x)"))))
			a.Show(
				"the stopped increment difference has the same event integral",
				By(
					parts[2],
					cutZero,
					At(incrementDifference, Ω, M, U, T, n),
					event_integral.EventIntegralEqOn.At(Ω, S, μ, E, a.TermAs[Fun[A, Real]]("«incrementDifference»"),
						a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ «between», M(n + 1, x) - M(n, x), &0)"))))
		})
		telescoping := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀P Q:(num → A → real). " +
				"∀E:set(A). " +
				"∀n:num.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)", "E ∈ S",
				"∀k:num. real_integrable(Ω, S, μ, P(k)) ∧ real_integrable(Ω, S, μ, Q(k))",
				"event_integral(Ω, S, μ, E, P(0)) = event_integral(Ω, S, μ, E, Q(0))",
				"∀k:num. event_integral(Ω, S, μ, E, λx:A. (P(k + 1, x) - P(k, x)) - (Q(k + 1, x) - Q(k, x))) = &0",
			},
			Conclusion: "event_integral(Ω, S, μ, E, P(n)) = event_integral(Ω, S, μ, E, Q(n))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			P, Q *Arrow2[Nat, A, Real],
			E *Expr[Set[A]],
			n *Expr[Nat],
			h Fact,
		) {
			a.Induct(n)
			a.Base(
				"the initial event integrals agree",
				By(h))
			a.Step(
				"equal increment integrals preserve equality at the next cutoff",
				func(b *Argument, ih Fact) {
					increments := b.Have(
						"both increments are integrable",
						"real_integrable(Ω, S, μ, λx:A. P(n + 1, x) - P(n, x)) ∧ "+
							"real_integrable(Ω, S, μ, λx:A. Q(n + 1, x) - Q(n, x))",
						By(
							h,
							measure_integral.IntegrableSub.At(
								Ω, S, μ, b.TermAs[Fun[A, Real]]("P(n + 1)"), b.TermAs[Fun[A, Real]]("P(n)")),
							measure_integral.IntegrableSub.At(
								Ω, S, μ, b.TermAs[Fun[A, Real]]("Q(n + 1)"), b.TermAs[Fun[A, Real]]("Q(n)"))))
					equal := b.Have(
						"the two increment integrals agree",
						"event_integral(Ω, S, μ, E, λx:A. P(n + 1, x) - P(n, x)) = "+
							"event_integral(Ω, S, μ, E, λx:A. Q(n + 1, x) - Q(n, x))",
						By(
							h,
							increments,
							event_integral.EventIntegralSub.At(
								Ω,
								S,
								μ,
								E,
								b.TermAs[Fun[A, Real]]("λx:A. P(n + 1, x) - P(n, x)"),
								b.TermAs[Fun[A, Real]]("λx:A. Q(n + 1, x) - Q(n, x)")),
							real_ring.SubEqZero))
					next := b.Have(
						"the successor cutoff is n plus one",
						"suc(n) = n + 1",
						ByArith())
					b.Show(
						"subtracting the equal present integrals leaves equal next integrals",
						By(
							next,
							ih,
							equal,
							h,
							event_integral.EventIntegralSub.At(
								Ω, S, μ, E, b.TermAs[Fun[A, Real]]("P(n + 1)"), b.TermAs[Fun[A, Real]]("P(n)")),
							event_integral.EventIntegralSub.At(
								Ω, S, μ, E, b.TermAs[Fun[A, Real]]("Q(n + 1)"), b.TermAs[Fun[A, Real]]("Q(n)")),
							real_ring.EqSubRightAdd))
				})
		})
		stoppedProcessIntegrable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀F:(num → set(set(A))). " +
				"∀M:(num → A → real). " +
				"∀T:(A → option(num)). " +
				"∀n:num.",
			Hypotheses: []string{"martingale_on(Ω, S, μ, F, M)", "stopping_time_on(Ω, F, T)"},
			Conclusion: "real_integrable(Ω, S, μ, stopped_process(M, T, n))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			n *Expr[Nat],
			h Fact,
		) {
			data := a.Have(
				"the martingale is integrable on its measure space, with its filtration",
				"measure_on(Ω, S, μ) ∧ filtration_on(Ω, S, F) ∧ (∀k:num. real_integrable(Ω, S, μ, M(k)))",
				By(h, martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M)))
			events := a.Have(
				"stopping events are measurable in the ambient sigma algebra",
				"∀k:num. {x:A | x ∈ Ω ∧ stopping_time_le(T(x), some(k))} ∈ S",
				BySets(data, h, filtration.FiltrationDef.At(Ω, S, F), stopping_time.StoppingTimeDef.At(Ω, F, T)))
			a.Show(
				"every finite stopped value is integrable",
				By(events, data, At(stoppedIntegrable, Ω, S, μ, M, T, n)))
		})
		stoppedEvents := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀F:(num → set(set(A))). " +
				"∀M:(num → A → real). " +
				"∀U T:(A → option(num)). " +
				"∀E:set(A). " +
				"∀n:num.",
			Hypotheses: []string{
				"martingale_on(Ω, S, μ, F, M)",
				"stopping_time_on(Ω, F, U)",
				"stopping_time_on(Ω, F, T)",
				"∀x:A. x ∈ Ω ⇒ stopping_time_le(U(x), T(x))",
				"E ∈ stopped_sigma(Ω, S, F, U)",
			},
			Conclusion: "event_integral(Ω, S, μ, E, stopped_process(M, T, n)) = " +
				"event_integral(Ω, S, μ, E, stopped_process(M, U, n))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			U, T *Arrow[A, Option[Nat]],
			E *Expr[Set[A]],
			n *Expr[Nat],
			h Fact,
		) {
			space := a.Have(
				"the stopped event is measurable on the measure space",
				"measure_on(Ω, S, μ) ∧ E ∈ S",
				BySets(
					h,
					martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M),
					stopping_time.StoppedSigmaDef.At(Ω, S, F, U)))
			integrable := a.Have(
				"both stopped processes are integrable at each cutoff",
				"∀k:num. "+
					"    real_integrable(Ω, S, μ, stopped_process(M, T, k)) ∧ "+
					"    real_integrable(Ω, S, μ, stopped_process(M, U, k))",
				By(
					h,
					At(stoppedProcessIntegrable, Ω, S, μ, F, M, T),
					At(stoppedProcessIntegrable, Ω, S, μ, F, M, U)))
			initial := a.Have(
				"the stopped processes have the same initial event integral",
				"event_integral(Ω, S, μ, E, stopped_process(M, T, 0)) = "+
					"event_integral(Ω, S, μ, E, stopped_process(M, U, 0))",
				By(stoppedZero))
			increments := a.Have(
				"every difference of stopped increments has zero event integral",
				"∀k:num. "+
					"    event_integral(Ω, "+
					"        S, "+
					"        μ, "+
					"        E, "+
					"        λx:A. "+
					"            (stopped_process(M, T, k + 1, x) - stopped_process(M, T, k, x)) - "+
					"            (stopped_process(M, U, k + 1, x) - stopped_process(M, U, k, x))) = "+
					"    &0",
				By(h, At(eventDifferenceZero, Ω, S, μ, F, M, U, T, E)))
			a.Show(
				"induction carries the common event integral to every finite cutoff",
				By(
					increments,
					integrable,
					initial,
					space,
					At(
						telescoping,
						Ω,
						S,
						μ,
						a.TermAs[Fun2[Nat, A, Real]]("stopped_process(M, T)"),
						a.TermAs[Fun2[Nat, A, Real]]("stopped_process(M, U)"),
						E,
						n)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			U, T *Arrow[A, Option[Nat]],
			N *Expr[Nat],
			h Fact,
		) {
			data := a.Have(
				"the martingale supplies the measure, filtration and integrable adapted values",
				"measure_on(Ω, S, μ) ∧ "+
					"filtration_on(Ω, S, F) ∧ "+
					"adapted_process(Ω, F, M) ∧ "+
					"(∀k:num. real_integrable(Ω, S, μ, M(k)))",
				By(h, martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M)))
			stoppedSigma := a.Have(
				"the earlier stopped value is measurable in its stopped sigma algebra",
				"sigma_algebra_on(Ω, stopped_sigma(Ω, S, F, U)) ∧ "+
					"stopped_sigma(Ω, S, F, U) ⊆ S ∧ "+
					"real_measurable(Ω, stopped_sigma(Ω, S, F, U), stopped_value(M, U))",
				By(
					data,
					h,
					filtration.FiltrationDef.At(Ω, S, F),
					stopping_time.StoppedSigmaAlgebra.At(Ω, S, F, U),
					stopping_time.StoppedValueMeasurable.At(Ω, S, F, U, M)))
			terminal := a.Have(
				"at the common bound both stopped processes equal their stopped values",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "stopped_process(M, T, N, x) = stopped_value(M, T, x) ∧ " +
						"stopped_process(M, U, N, x) = stopped_value(M, U, x)",
				},
				By(
					h,
					stopping_time.TimeLeTrans,
					stopping_time.StoppedProcessAtBound.Inst[A]().At(M, T, N),
					stopping_time.StoppedProcessAtBound.Inst[A]().At(M, U, N)))
			integrable := a.Have(
				"both terminal stopped values are integrable",
				"real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ real_integrable(Ω, S, μ, stopped_value(M, U))",
				By(
					terminal,
					h,
					At(stoppedProcessIntegrable, Ω, S, μ, F, M, T, N),
					At(stoppedProcessIntegrable, Ω, S, μ, F, M, U, N),
					measure_integral.RealIntegrableEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Real]]("stopped_process(M, T, N)"),
						a.TermAs[Fun[A, Real]]("stopped_value(M, T)")),
					measure_integral.RealIntegrableEqOn.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, Real]]("stopped_process(M, U, N)"),
						a.TermAs[Fun[A, Real]]("stopped_value(M, U)"))))
			eventIntegrals := a.Have(
				"the terminal values have equal integrals over every earlier stopped event",
				Statement{
					Binders:    "∀E:set(A).",
					Hypotheses: []string{"E ∈ stopped_sigma(Ω, S, F, U)"},
					Conclusion: "event_integral(Ω, S, μ, E, stopped_value(M, T)) = " +
						"event_integral(Ω, S, μ, E, stopped_value(M, U))",
				},
				Derive(func(b *Argument) {
					E := b.FixAs[Set[A]]("E")
					event := b.Assume()
					b.Show(
						"the finite cutoff equality transfers to both terminal values on the carrier",
						By(
							terminal,
							event,
							h,
							At(stoppedEvents, Ω, S, μ, F, M, U, T, E, N),
							event_integral.EventIntegralEqOn.At(
								Ω,
								S,
								μ,
								E,
								b.TermAs[Fun[A, Real]]("stopped_process(M, T, N)"),
								b.TermAs[Fun[A, Real]]("stopped_value(M, T)")),
							event_integral.EventIntegralEqOn.At(
								Ω,
								S,
								μ,
								E,
								b.TermAs[Fun[A, Real]]("stopped_process(M, U, N)"),
								b.TermAs[Fun[A, Real]]("stopped_value(M, U)"))))
				}))
			a.Show(
				"these are the defining clauses of the conditional expectation",
				By(
					eventIntegrals,
					stoppedSigma,
					data,
					integrable,
					conditional_expectation.IsCondExpDef.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[Set[A]]]("stopped_sigma(Ω, S, F, U)"),
						a.TermAs[Fun[A, Real]]("stopped_value(M, T)"),
						a.TermAs[Fun[A, Real]]("stopped_value(M, U)"))))
		})
	}),
})}

// OptionalStoppingTruncated — a martingale stopped at a stopping time and observed
// at a finite time n is integrable and keeps its expectation. Truncated at n the
// stopping time is bounded, and bounded sampling against the zero time makes the
// initial value a conditional expectation of the truncated one.
var OptionalStoppingTruncated = optionalStoppingTruncatedThm{family.Add(registry.ProofEntry{
	Name: "OptionalStoppingTruncated",
	Key:  "prop_a06e2e2b146dd92",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)). " +
			"∀n:num.",
		Hypotheses: []string{"martingale_on(Ω, S, μ, F, M)", "stopping_time_on(Ω, F, T)"},
		Conclusion: "real_integrable(Ω, S, μ, stopped_process(M, T, n)) ∧ " +
			"expectation(Ω, S, μ, stopped_process(M, T, n)) = expectation(Ω, S, μ, M(0))",
		Abbrev: Abbrev{
			{Name: "truncation", Text: "λx:A. some(stopping_time_min_nat(T(x), n))"},
			{Name: "zeroTime", Text: "λx:A. some(0)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		F *Arrow2[Nat, Set[A], Bool],
		M *Arrow2[Nat, A, Real],
		T *Arrow[A, Option[Nat]],
		n *Expr[Nat],
		h Fact,
	) {
		stopping := a.Have(
			"zero and the truncation are stopping times, and the truncation is bounded by n",
			"stopping_time_on(Ω, F, «truncation») ∧ "+
				"stopping_time_on(Ω, F, «zeroTime») ∧ "+
				"(∀x:A. stopping_time_min_nat(T(x), n) ≤ n)",
			By(
				h,
				martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M),
				filtration.FiltrationDef.At(Ω, S, F),
				stopping_time.StoppingTruncation.At(Ω, F, T, n),
				stopping_time.StoppingConstants.At(Ω, F, a.TermAs[Nat]("0"))))
		ordered := a.Have(
			"the two sample times lie between zero and n",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "stopping_time_le(«zeroTime»(x), «truncation»(x)) ∧ " +
					"stopping_time_le(«truncation»(x), some(n))",
			},
			By(stopping, stopping_time.TimeLeClauses, nat_order.ZeroLessEq))
		zeroTime := a.TermAs[Fun[A, Option[Nat]]]("«zeroTime»")
		truncation := a.TermAs[Fun[A, Option[Nat]]]("«truncation»")
		sampled := a.Have(
			"bounded optional sampling compares the truncation with time zero",
			"is_cond_exp(Ω, "+
				"    S, "+
				"    μ, "+
				"    stopped_sigma(Ω, S, F, «zeroTime»), "+
				"    stopped_value(M, «truncation»), "+
				"    stopped_value(M, «zeroTime»))",
			By(ordered, stopping, h, OptionalSamplingBounded.At(Ω, S, μ, F, M, zeroTime, truncation, n)))
		values := a.Have(
			"the bounded samples are the truncated process and its initial value",
			"stopped_value(M, «truncation») = stopped_process(M, T, n) ∧ stopped_value(M, «zeroTime») = M(0)",
			By(stopping_time.StoppedValueAtTruncation.At(M, T, n), stopping_time.StoppedValueSome))
		earlier := a.TermAs[Set[Set[A]]]("stopped_sigma(Ω, S, F, «zeroTime»)")
		later := a.TermAs[Fun[A, Real]]("stopped_value(M, «truncation»)")
		initial := a.TermAs[Fun[A, Real]]("stopped_value(M, «zeroTime»)")
		a.Show(
			"the conditioned value is integrable, and its conditional expectation keeps its integral",
			By(
				values,
				sampled,
				conditional_expectation.IsCondExpDef.At(Ω, S, μ, earlier, later, initial),
				conditional_expectation.CondExpIntegral.At(Ω, S, μ, earlier, later, initial),
				probability_space.ExpectationDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("stopped_process(M, T, n)")),
				probability_space.ExpectationDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("M(0)"))))
	}),
})}

// OptionalStoppingBoundedAE — a martingale stopped at a time that is almost
// everywhere at most N keeps its expectation. The process stopped at N is
// integrable with the initial expectation, and it shows the stopped value
// wherever the time has occurred by N, so almost everywhere; both are
// measurable, so integrability and the integral pass across the agreement.
var OptionalStoppingBoundedAE = optionalStoppingBoundedAEThm{family.Add(registry.ProofEntry{
	Name: "OptionalStoppingBoundedAE",
	Reading: "The points where T is infinite lie in the exceptional " +
		"set, because stopping_time_le(none, some(N)) is false, so the " +
		"almost everywhere bound also makes T finite almost everywhere.",
	Key: "prop_5b932ed3bc1088e0",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)). " +
			"∀N:num.",
		Hypotheses: []string{
			"martingale_on(Ω, S, μ, F, M)",
			"stopping_time_on(Ω, F, T)",
			"measure_ae(Ω, S, μ, λx:A. stopping_time_le(T(x), some(N)))",
		},
		Conclusion: "real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ " +
			"expectation(Ω, S, μ, stopped_value(M, T)) = expectation(Ω, S, μ, M(0))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		F *Arrow2[Nat, Set[A], Bool],
		M *Arrow2[Nat, A, Real],
		T *Arrow[A, Option[Nat]],
		N *Expr[Nat],
		h Fact,
	) {
		atBound := a.TermAs[Fun[A, Real]]("stopped_process(M, T, N)")
		stoppedValue := a.TermAs[Fun[A, Real]]("stopped_value(M, T)")
		data := a.Have(
			"the martingale supplies the measure, filtration and adaptedness",
			"measure_on(Ω, S, μ) ∧ filtration_on(Ω, S, F) ∧ adapted_process(Ω, F, M)",
			By(h, martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M)))
		measurable := a.Have(
			"the stopped value and the process stopped at N are measurable",
			"real_measurable(Ω, S, stopped_value(M, T)) ∧ real_measurable(Ω, S, stopped_process(M, T, N))",
			By(data, h, stopping_time.StoppedAmbientMeasurable.At(Ω, S, F, T, M)))
		agree := a.Have(
			"the process stopped at N shows the stopped value almost everywhere",
			"measure_ae_eq(Ω, S, μ, stopped_process(M, T, N), stopped_value(M, T))",
			By(
				h,
				measure_space.AEEqualDef.At(Ω, S, μ, atBound, stoppedValue),
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. stopping_time_le(T(x), some(N))"),
					a.TermAs[Set[A]]("λx:A. stopped_process(M, T, N, x) = stopped_value(M, T, x)")),
				stopping_time.StoppedProcessAtBound.Inst[A]().At(M, T, N)))
		a.Show(
			"integrability and the expectation pass from the process stopped at N to the stopped value",
			By(
				data,
				h,
				measurable,
				agree,
				OptionalStoppingTruncated.At(Ω, S, μ, F, M, T, N),
				measure_integral.IntegrableAE.At(Ω, S, μ, atBound, stoppedValue),
				probability_space.ExpectationDef.At(Ω, S, μ, atBound),
				probability_space.ExpectationDef.At(Ω, S, μ, stoppedValue)))
	}),
})}
