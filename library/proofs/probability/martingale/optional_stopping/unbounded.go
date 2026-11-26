// unbounded.go — optional stopping at an unbounded stopping time. Dominated
// stopping reads the integrals of the truncations off OptionalStoppingTruncated
// and passes to the limit; a finite expected time and bounded increments give
// the dominating envelope |M(0)| + |C|·τ, τ the finite part of T.

package optional_stopping

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/stopping_time"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// OptionalStoppingDominated — an almost surely finite stopping time preserves
// the expectation of a martingale whose stopped process has an integrable bound.
// OptionalStoppingTruncated fixes the integral of each truncation; eventual equality
// identifies its almost everywhere limit, and dominated convergence passes the integral to it.
var OptionalStoppingDominated = optionalStoppingDominatedThm{family.Add(registry.ProofEntry{
	Name: "OptionalStoppingDominated",
	Key:  "prop_a06c7591d893f1a6",
	Reading: "Only the stopped process is dominated. The initial value may be any integrable random " +
		"variable, and the value assigned at T=infinity is irrelevant under almost sure finiteness.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)). " +
			"∀Y:(A → real).",
		Hypotheses: []string{
			"martingale_on(Ω, S, μ, F, M)",
			"stopping_time_on(Ω, F, T)",
			"measure_ae(Ω, S, μ, λx:A. T(x) ≠ none)",
			"real_integrable(Ω, S, μ, Y)",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |stopped_process(M, T, n, x)| ≤ Y(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ " +
			"expectation(Ω, S, μ, stopped_value(M, T)) = expectation(Ω, S, μ, M(0))",
		Abbrev: Abbrev{
			{Name: "integrals", Text: "λn:num. measure_integral(Ω, S, μ, stopped_process(M, T, n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		tailValue := ctx.Lemma(Statement{
			Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀x:A. ∀k n:num.",
			Hypotheses: []string{"T(x) = some(k)", "k ≤ n"},
			Conclusion: "stopped_process(M, T, n, x) = M(k, x)",
		}, func(
			a *Argument,
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			x *Expr[A],
			k, n *Expr[Nat],
			h Fact,
		) {
			a.Show(
				"truncation beyond the finite stopping index retains that value",
				By(
					h,
					stopping_time.StoppedProcessDef.At(M, T, n, x),
					stopping_time.TimeMinNatDef.At(T.Apply(x), n),
					option.SomeInjective))
		})
		finiteIndexLimit := ctx.Lemma(Statement{
			Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀x:A. ∀k:num.",
			Hypotheses: []string{"T(x) = some(k)"},
			Conclusion: "(λn:num. stopped_process(M, T, n, x)) ⟶ stopped_value(M, T, x)",
		}, func(
			a *Argument,
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			x *Expr[A],
			k *Expr[Nat],
			finite Fact,
		) {
			a.Do(Unfold(real_sequences.RealConvergesToDef))
			a.FixAs[Real]("ε")
			positive := a.Assume()
			a.Take(k)
			n := a.FixAs[Nat]("n")
			past := a.Assume()
			a.Show(
				"past k the difference vanishes and is below every positive epsilon",
				By(
					past,
					finite,
					positive,
					stopping_time.StoppedValueSome.At(M, T, x, k),
					At(tailValue, M, T, x, k, n),
					real_ring.SubRefl,
					real_sgn_abs.AbsOfZero))
		})
		finiteLimit := ctx.Lemma(Statement{
			Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀x:A.",
			Hypotheses: []string{"T(x) ≠ none"},
			Conclusion: "(λn:num. stopped_process(M, T, n, x)) ⟶ stopped_value(M, T, x)",
		}, func(a *Argument, M *Arrow2[Nat, A, Real], T *Arrow[A, Option[Nat]], x *Expr[A], finite Fact) {
			k, atIndex := a.ObtainAs[Nat](
				"a finite optional time has a natural index",
				"∃k:num. T(x) = some(k)",
				By(Normalized, finite, option.Cases.At(T.Apply(x))))
			a.Show(
				"the finite-index convergence applies",
				By(atIndex, At(finiteIndexLimit, M, T, x, k)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			Y *Arrow[A, Real],
			h Fact,
		) {
			data := a.Have(
				"the martingale supplies the measure, filtration and adaptedness",
				"measure_on(Ω, S, μ) ∧ filtration_on(Ω, S, F) ∧ adapted_process(Ω, F, M)",
				By(h, martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M)))
			measurable := a.Have(
				"the terminal value and each truncation are measurable",
				"real_measurable(Ω, S, stopped_value(M, T)) ∧ "+
					"(∀n:num. real_measurable(Ω, S, stopped_process(M, T, n)))",
				By(h, data, stopping_time.StoppedAmbientMeasurable.At(Ω, S, F, T, M)))
			convergence := a.Have(
				"finite stopping gives almost everywhere convergence of the truncations",
				"measure_ae(Ω, S, μ, λx:A. (λn:num. stopped_process(M, T, n, x)) ⟶ stopped_value(M, T, x))",
				By(
					h,
					At(finiteLimit, M, T),
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. T(x) ≠ none"),
						a.TermAs[Set[A]]("λx:A. (λn:num. stopped_process(M, T, n, x)) ⟶ stopped_value(M, T, x)"))))
			dominated := a.Have(
				"dominated convergence gives integrability and convergence of the integrals",
				"real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ "+
					"«integrals» ⟶ measure_integral(Ω, S, μ, stopped_value(M, T))",
				By(
					h,
					data,
					measurable,
					convergence,
					integral_convergence.DominatedConvergenceAE.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun2[Nat, A, Real]]("stopped_process(M, T)"),
						a.TermAs[Fun[A, Real]]("stopped_value(M, T)"),
						Y)))
			constant := a.Have(
				"every truncated integral is the initial integral",
				"«integrals» = (λn:num. measure_integral(Ω, S, μ, M(0)))",
				By(h, OptionalStoppingTruncated.Inst[A]().At(Ω, S, μ, F, M, T), probability_space.ExpectationDef))
			a.Show(
				"uniqueness of the limit identifies the terminal and initial expectations",
				By(
					constant,
					dominated,
					real_sequences.LimitConst.At(a.TermAs[Real]("measure_integral(Ω, S, μ, M(0))")),
					real_sequences.LimitUnique.At(
						a.TermAs[Fun[Nat, Real]]("«integrals»"),
						a.TermAs[Real]("measure_integral(Ω, S, μ, stopped_value(M, T))"),
						a.TermAs[Real]("measure_integral(Ω, S, μ, M(0))")),
					probability_space.ExpectationDef))
		})
	}),
})}

// OptionalStoppingIntegrableTime — finite expected stopping time and a uniform
// almost everywhere bound on martingale increments preserve expectation.
// The finite part of the stopping time is integrable; linear growth bounds every
// stopped value by the initial absolute value plus |C| times that finite part.
var OptionalStoppingIntegrableTime = optionalStoppingIntegrableTimeThm{family.Add(registry.ProofEntry{
	Name: "OptionalStoppingIntegrableTime",
	Key:  "prop_58e3bea9b0ce6268",
	Reading: "Expected time is the extended nonnegative integral, with infinity " +
		"mapped to infinity. Almost sure finiteness alone would not suffice.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M:(num → A → real). " +
			"∀T:(A → option(num)). " +
			"∀C:real.",
		Hypotheses: []string{
			"martingale_on(Ω, S, μ, F, M)",
			"stopping_time_on(Ω, F, T)",
			"nonneg_integral(Ω, S, μ, λx:A. stopping_time_extended(T(x))) ≠ extended_infinity",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |M(n + 1, x) - M(n, x)| ≤ C)",
		},
		Conclusion: "real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ " +
			"expectation(Ω, S, μ, stopped_value(M, T)) = expectation(Ω, S, μ, M(0))",
		Abbrev: Abbrev{
			{Name: "τ", Text: "stopped_value(λn:num. λy:A. &n, T)"},
			{Name: "envelope", Text: "λx:A. |M(0, x)| + |C| * «τ»(x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		finiteTimeValues := ctx.Lemma(Statement{
			Binders:    "∀T:(A → option(num)). ∀x:A. ∀k:num.",
			Hypotheses: []string{"T(x) = some(k)"},
			Conclusion: "«τ»(x) = &k ∧ stopping_time_extended(T(x)) = extended_of_real(&k)",
		}, func(a *Argument, T *Arrow[A, Option[Nat]], x *Expr[A], k *Expr[Nat], finite Fact) {
			a.Show(
				"both representations of a finite stopping time give its index",
				By(
					finite,
					stopping_time.StoppedValueSome.At(a.TermAs[Fun2[Nat, A, Real]]("λn:num. λy:A. &n"), T, x, k),
					stopping_time.TimeToExtendedDef.At(T.Apply(x)),
					option.NoneNotSome,
					option.SomeInjective))
		})
		infiniteTimeValues := ctx.Lemma(Statement{
			Binders:    "∀T:(A → option(num)). ∀x:A.",
			Hypotheses: []string{"T(x) = none"},
			Conclusion: "«τ»(x) = &0 ∧ stopping_time_extended(T(x)) = extended_infinity",
		}, func(a *Argument) {
			a.Show(
				"at infinity the real finite part is zero and the extended time is infinite",
				By(stopping_time.StoppedValueDef, stopping_time.TimeToExtendedDef))
		})
		timeBounds := ctx.Lemma("∀T:(A → option(num)). ∀x:A. "+
			"    &0 ≤ «τ»(x) ∧ extended_of_real(|«τ»(x)|) ≤ stopping_time_extended(T(x))",
			func(a *Argument, T *Arrow[A, Option[Nat]], x *Expr[A]) {
				a.Cases(a.TermAs[Bool]("T(x) = none"))
				a.When(
					"at infinity the extended time bounds the zero finite part",
					func(b *Argument, infinite Fact) {
						b.Show(
							"zero is nonnegative and every extended value lies below infinity",
							By(
								infinite,
								At(infiniteTimeValues, T, x),
								real_sgn_abs.AbsNonneg,
								real_sgn_abs.AbsOfZero,
								extended_nonneg_real.LeInfinity))
					})
				a.Otherwise(
					"a finite time is represented by a nonnegative natural index",
					func(b *Argument, finite Fact) {
						k, atIndex := b.ObtainAs[Nat](
							"choose the finite stopping index",
							"∃k:num. T(x) = some(k)",
							By(finite, option.Cases.At(T.Apply(x))))
						b.Show(
							"the natural index has the same real and extended values",
							By(
								Normalized,
								atIndex,
								At(finiteTimeValues, T, x, k),
								real_sgn_abs.AbsOfNum.At(k),
								real_sgn_abs.AbsNonneg.At(b.TermAs[Real]("&k")),
								extended_nonneg_real.LeRefl))
					})
			})
		timeMeasurable := ctx.Lemma(Statement{
			Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀T:(A → option(num)).",
			Hypotheses: []string{"sigma_algebra_on(Ω, S)", "stopping_time_on(Ω, λn:num. S, T)"},
			Conclusion: "real_measurable(Ω, S, «τ») ∧ " +
				"extended_measurable(Ω, S, λx:A. stopping_time_extended(T(x)))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], T *Arrow[A, Option[Nat]], h Fact) {
			F := a.TermAs[Fun[Nat, Set[Set[A]]]]("λn:num. S")
			clock := a.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. &n")
			data := a.Have(
				"the deterministic clock is adapted to the constant filtration",
				"filtration_on(Ω, S, λn:num. S) ∧ adapted_process(Ω, λn:num. S, λn:num. λx:A. &n)",
				BySets(
					h,
					filtration.FiltrationDef.At(Ω, S, F),
					filtration.AdaptedDef.At(Ω, F, clock),
					At(measurable_function.RealMeasurableConst, Ω, S)))
			a.Show(
				"both forms of the stopping time are measurable on S",
				By(
					h,
					data,
					stopping_time.StoppedAmbientMeasurable.At(Ω, S, F, T, clock),
					stopping_time.StoppingTimeExtendedMeasurable.At(Ω, S, T)))
		})
		timeIntegrable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀T:(A → option(num)).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"stopping_time_on(Ω, λn:num. S, T)",
				"nonneg_integral(Ω, S, μ, λx:A. stopping_time_extended(T(x))) ≠ extended_infinity",
			},
			Conclusion: "real_integrable(Ω, S, μ, «τ») ∧ measure_ae(Ω, S, μ, λx:A. T(x) ≠ none)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			T *Arrow[A, Option[Nat]],
			h Fact,
		) {
			measurable := a.Have(
				"the real finite part and extended time are measurable",
				"real_measurable(Ω, S, «τ») ∧ extended_measurable(Ω, S, λx:A. stopping_time_extended(T(x)))",
				By(h, measure_space.MeasureOn.At(Ω, S, μ), At(timeMeasurable, Ω, S, T)))
			bound := a.Have(
				"the absolute finite part has no larger integral than the extended time",
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|«τ»(x)|)) ≤ "+
					"nonneg_integral(Ω, S, μ, λx:A. stopping_time_extended(T(x)))",
				By(
					At(timeBounds, T),
					nonneg_integral.NonnegIntegralMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|«τ»(x)|)"),
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. stopping_time_extended(T(x))"))))
			extendedFinite := a.Have(
				"a finite integral makes the extended stopping time finite almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. stopping_time_extended(T(x)) ≠ extended_infinity)",
				By(
					h,
					measurable,
					nonneg_integral.FiniteIntegralAEFinite.At(
						Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. stopping_time_extended(T(x))"))))
			finite := a.Have(
				"the stopping time is finite almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. T(x) ≠ none)",
				By(
					extendedFinite,
					At(infiniteTimeValues, T),
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. stopping_time_extended(T(x)) ≠ extended_infinity"),
						a.TermAs[Set[A]]("λx:A. T(x) ≠ none"))))
			a.Show(
				"the measurable finite part has a finite absolute integral",
				By(
					bound,
					h,
					measurable,
					finite,
					extended_nonneg_real.ExtendedLeDef.At(
						a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|«τ»(x)|))"),
						a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, λx:A. stopping_time_extended(T(x)))")),
					measure_integral.RealIntegrableDef.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«τ»"))))
		})
		growth := ctx.Lemma(Statement{
			Binders:    "∀a:(num → real). ∀D:real. ∀n:num.",
			Hypotheses: []string{"∀k:num. |a(k + 1) - a(k)| ≤ D"},
			Conclusion: "|a(n)| ≤ |a(0)| + D * &n",
		}, func(b *Argument, a *Arrow[Nat, Real], D *Expr[Real], n *Expr[Nat], increments Fact) {
			b.Induct(n)
			b.Base(
				"at zero the growth bound is equality",
				ByArith())
			b.Step(
				"one more bounded increment advances the growth bound",
				func(b *Argument, ih Fact) {
					triangle := b.Have(
						"the next absolute value is bounded by the present value and increment",
						"|a(n + 1)| ≤ |a(n)| + |a(n + 1) - a(n)|",
						ByArith(real_sgn_abs.AbsTriangle.At(a.Apply(n), b.TermAs[Real]("a(n + 1) - a(n)"))))
					b.Show(
						"the increment bound and natural-number cast give the next growth estimate",
						ByArith(
							increments.At(n),
							nat_arith.Add1.At(n),
							ih,
							triangle,
							real_construction.OfNumAdd.At(n, b.TermAs[Nat]("1"))))
				})
		})
		truncatedIndex := ctx.Lemma(Statement{
			Binders:    "∀t:option(num). ∀k n:num.",
			Hypotheses: []string{"t = some(k)"},
			Conclusion: "stopping_time_min_nat(t, n) ≤ k",
		}, func(a *Argument, t *Expr[Option[Nat]], k, n *Expr[Nat], finite Fact) {
			a.Cases(a.TermAs[Bool]("k ≤ n"))
			a.When(
				"the finite stopping index lies within the cutoff",
				func(b *Argument, within Fact) {
					value := b.Have(
						"truncation retains the stopping index",
						"stopping_time_min_nat(t, n) = k",
						By(within, finite, stopping_time.TimeMinNatDef.At(t, n), option.SomeInjective))
					b.Show(
						"the retained index does not exceed itself",
						ByArith(value))
				})
			a.Otherwise(
				"the cutoff precedes the finite stopping index",
				func(b *Argument, beyond Fact) {
					value := b.Have(
						"truncation selects the earlier cutoff",
						"stopping_time_min_nat(t, n) = n",
						By(beyond, finite, stopping_time.TimeMinNatDef.At(t, n), option.SomeInjective))
					b.Show(
						"the selected cutoff is below the stopping index",
						ByArith(beyond, value))
				})
		})
		pointwiseDomination := ctx.Lemma(Statement{
			Binders:    "∀M:(num → A → real). ∀T:(A → option(num)). ∀C:real. ∀x:A. ∀n:num.",
			Hypotheses: []string{"T(x) ≠ none", "∀k:num. |M(k + 1, x) - M(k, x)| ≤ C"},
			Conclusion: "|stopped_process(M, T, n, x)| ≤ «envelope»(x)",
		}, func(
			a *Argument,
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			C *Expr[Real],
			x *Expr[A],
			n *Expr[Nat],
			h Fact,
		) {
			k, finite := a.ObtainAs[Nat](
				"choose the finite stopping index",
				"∃k:num. T(x) = some(k)",
				By(h, option.Cases.At(T.Apply(x))))
			increments := a.Have(
				"the absolute constant bounds every increment",
				"∀j:num. |M(j + 1, x) - M(j, x)| ≤ |C|",
				ByArith(h, real_sgn_abs.AbsDominates.At(C)))
			indexBound := a.Have(
				"the truncated index lies below the real stopping time",
				"&(stopping_time_min_nat(T(x), n)) ≤ «τ»(x)",
				By(
					Normalized,
					finite,
					At(truncatedIndex, T.Apply(x), k, n),
					At(finiteTimeValues, T, x, k),
					real_construction.OfNumLessEq.At(a.TermAs[Nat]("stopping_time_min_nat(T(x), n)"), k)))
			atCutoff := a.Have(
				"the linear growth estimate applies at the truncated index",
				"|M(stopping_time_min_nat(T(x), n), x)| ≤ |M(0, x)| + |C| * &(stopping_time_min_nat(T(x), n))",
				By(
					increments,
					At(
						growth,
						a.TermAs[Fun[Nat, Real]]("λj:num. M(j, x)"),
						a.TermAs[Real]("|C|"),
						a.TermAs[Nat]("stopping_time_min_nat(T(x), n)"))))
			a.Show(
				"nonnegative scaling gives the common envelope for every truncation",
				ByArith(
					atCutoff,
					indexBound,
					real_sgn_abs.AbsNonneg.At(C),
					stopping_time.StoppedProcessDef.At(M, T, n, x)))
		})
		envelopeIntegrable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀M:(num → A → real). " +
				"∀T:(A → option(num)). " +
				"∀C:real.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"real_integrable(Ω, S, μ, M(0))",
				"real_integrable(Ω, S, μ, «τ»)",
			},
			Conclusion: "real_integrable(Ω, S, μ, «envelope»)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			C *Expr[Real],
			h Fact,
		) {
			parts := a.Have(
				"the initial absolute value and scaled stopping time are integrable",
				"real_integrable(Ω, S, μ, λx:A. |M(0, x)|) ∧ real_integrable(Ω, S, μ, λx:A. |C| * «τ»(x))",
				By(
					h,
					measure_integral.IntegrableAbs.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("M(0)")),
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_integral.IntegrableScale.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("«τ»"), a.TermAs[Real]("|C|"))))
			a.Show(
				"adding the two integrable parts gives the envelope",
				By(
					h,
					parts,
					measure_integral.IntegrableAdd.At(
						Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. |M(0, x)|"), a.TermAs[Fun[A, Real]]("λx:A. |C| * «τ»(x)"))))
		})
		aeDomination := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀M:(num → A → real). " +
				"∀T:(A → option(num)). " +
				"∀C:real. " +
				"∀n:num.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"measure_ae(Ω, S, μ, λx:A. T(x) ≠ none)",
				"∀j:num. measure_ae(Ω, S, μ, λx:A. |M(j + 1, x) - M(j, x)| ≤ C)",
			},
			Conclusion: "measure_ae(Ω, S, μ, λx:A. |stopped_process(M, T, n, x)| ≤ «envelope»(x))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			C *Expr[Real],
			n *Expr[Nat],
			h Fact,
		) {
			increments := a.Have(
				"all increment bounds hold on one set of full measure",
				"measure_ae(Ω, S, μ, λx:A. ∀j:num. |M(j + 1, x) - M(j, x)| ≤ C)",
				By(
					h,
					measure_space.AECountable.At(
						Ω, S, μ, a.TermAs[Fun2[Nat, A, Bool]]("λj:num. λx:A. |M(j + 1, x) - M(j, x)| ≤ C"))))
			joint := a.Have(
				"finite stopping and all increment bounds hold together almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. T(x) ≠ none ∧ (∀j:num. |M(j + 1, x) - M(j, x)| ≤ C))",
				By(
					h,
					increments,
					measure_space.AEConjunction.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. T(x) ≠ none"),
						a.TermAs[Set[A]]("λx:A. ∀j:num. |M(j + 1, x) - M(j, x)| ≤ C"))))
			a.Show(
				"the pointwise estimate supplies almost everywhere domination at every cutoff",
				By(
					joint,
					At(pointwiseDomination, M, T, C),
					measure_space.AEMono.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("λx:A. T(x) ≠ none ∧ (∀j:num. |M(j + 1, x) - M(j, x)| ≤ C)"),
						a.TermAs[Set[A]]("λx:A. |stopped_process(M, T, n, x)| ≤ «envelope»(x)"))))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Set[A], Bool],
			M *Arrow2[Nat, A, Real],
			T *Arrow[A, Option[Nat]],
			C *Expr[Real],
			h Fact,
		) {
			data := a.Have(
				"the martingale supplies the measure, integrable values and ambient stopping events",
				"measure_on(Ω, S, μ) ∧ "+
					"sigma_algebra_on(Ω, S) ∧ "+
					"(∀n:num. real_integrable(Ω, S, μ, M(n))) ∧ "+
					"stopping_time_on(Ω, λn:num. S, T)",
				BySets(
					h,
					martingale.MartingaleAdaptedIntegrable.At(Ω, S, μ, F, M),
					filtration.FiltrationDef.At(Ω, S, F),
					stopping_time.StoppingTimeDef.At(Ω, F, T),
					stopping_time.StoppingTimeDef.At(Ω, a.TermAs[Fun[Nat, Set[Set[A]]]]("λn:num. S"), T)))
			time := a.Have(
				"finite expected time gives an integrable clock and almost sure finiteness",
				"real_integrable(Ω, S, μ, «τ») ∧ measure_ae(Ω, S, μ, λx:A. T(x) ≠ none)",
				By(data, h, At(timeIntegrable, Ω, S, μ, T)))
			envelope := a.Have(
				"the common envelope is integrable",
				"real_integrable(Ω, S, μ, «envelope»)",
				By(data, time, At(envelopeIntegrable, Ω, S, μ, M, T, C)))
			dominated := a.Have(
				"the envelope dominates every stopped value almost everywhere",
				"∀n:num. measure_ae(Ω, S, μ, λx:A. |stopped_process(M, T, n, x)| ≤ «envelope»(x))",
				By(data, h, time, At(aeDomination, Ω, S, μ, M, T, C)))
			a.Show(
				"dominated optional stopping gives integrability and preserves expectation",
				By(
					dominated,
					h,
					time,
					envelope,
					OptionalStoppingDominated.At(Ω, S, μ, F, M, T, a.TermAs[Fun[A, Real]]("«envelope»"))))
		})
	}),
})}
