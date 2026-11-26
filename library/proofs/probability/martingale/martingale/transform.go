// transform.go — the martingale transform: bounded predictable weights
// preserve a martingale, and a predictable stop preserves a martingale
// difference row.

package martingale

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// MartingaleTransform — bounded predictable weights preserve a martingale:
// the weighted increments have conditional expectation zero, and their finite
// partial sums are integrable and adapted.
var MartingaleTransform = martingaleTransformThm{family.Add(registry.ProofEntry{
	Name: "MartingaleTransform",
	Reading: "The bound may depend on n. Predictability gives measurable products, and the " +
		"almost-everywhere bound provides domination in the known-factor conditional-expectation law.",
	Key: "prop_37a0be6a3ab566d8",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀M H:(num → A → real).",
		Hypotheses: []string{
			"martingale_on(Ω, S, μ, F, M)",
			"∀n:num. real_measurable(Ω, F(n), H(n))",
			"∀n:num. ∃C:real. measure_ae(Ω, S, μ, λx:A. |H(n, x)| ≤ C)",
		},
		Conclusion: "martingale_on(Ω, S, μ, F, martingale_transform(M, H))",
		Abbrev: Abbrev{
			{Name: "increment", Text: "λM:(num → A → real). λH:(num → A → real). λn:num. λx:A. " +
				"    H(n, x) * (M(n + 1, x) - M(n, x))"},
			{Name: "difference", Text: "λf:(A → real). λg:(A → real). λx:A. f(x) - g(x)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		recurrence := ctx.Lemma(
			"∀M H:(num → A → real). ∀n:num. ∀x:A. "+
				"    martingale_transform(M, H, n + 1, x) = "+
				"    martingale_transform(M, H, n, x) + «increment»(M, H, n, x)",
			func(a *Argument, M, H *Arrow2[Nat, A, Real], n *Expr[Nat], x *Expr[A]) {
				a.Show(
					"the successor sum adds its last summand",
					Simp(Fwd(MartingaleTransformDef)),
					Simp(Rev(nat_arith.Add1), Fwd(real_sum.BelowClauses)),
					ByArith())
			})
		centeredFactor := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀X Y h:(A → real). " +
				"∀C:real.",
			Hypotheses: []string{
				"is_cond_exp(Ω, S, μ, G, X, Y)",
				"real_measurable(Ω, G, h)",
				"measure_ae(Ω, S, μ, λx:A. |h(x)| ≤ C)",
			},
			Conclusion: "is_cond_exp(Ω, S, μ, G, λx:A. h(x) * «difference»(X, Y, x), λx:A. &0)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], G *Expr[Set[Set[A]]],
			X, Y, h *Arrow[A, Real], C *Expr[Real], assumptions Fact) {
			one := a.TermAs[Real]("&1")
			minusOne := a.TermAs[Real]("-&1")
			zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
			difference := a.TermAs[Fun[A, Real]]("«difference»(X, Y)")
			known := a.Have(
				"the conditional expectation is already known at G",
				"is_cond_exp(Ω, S, μ, G, Y, Y)",
				By(
					assumptions,
					conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, X, Y),
					conditional_expectation.CondExpIdentity.At(Ω, S, μ, G, Y)))
			// CondExpLinear states the relation at 1·X + (−1)·Y and 1·Y + (−1)·Y;
			// ByArith closes the goal by normalizing those bodies under λ to
			// X − Y and 0, the arithmetic being the only gap between the two.
			centered := a.Have(
				"subtracting the known part gives conditional expectation zero",
				"is_cond_exp(Ω, S, μ, G, «difference»(X, Y), λx:A. &0)",
				ByArith(
					assumptions,
					known,
					conditional_expectation.CondExpLinear.At(Ω, S, μ, G, X, Y, Y, Y, one, minusOne)))
			a.Show(
				"a bounded known factor preserves the zero conditional expectation",
				ByArith(
					assumptions,
					centered,
					conditional_expectation.CondExpKnownFactor.At(Ω, S, μ, G, difference, zero, h, C)))
		})
		increments := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀F:(num → set(set(A))). " +
				"∀M H:(num → A → real). " +
				"∀n:num.",
			Hypotheses: []string{
				"martingale_on(Ω, S, μ, F, M)",
				"∀n:num. real_measurable(Ω, F(n), H(n))",
				"∀n:num. ∃C:real. measure_ae(Ω, S, μ, λx:A. |H(n, x)| ≤ C)",
			},
			Conclusion: "is_cond_exp(Ω, S, μ, F(n), «increment»(M, H, n), λx:A. &0)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], F *Arrow2[Nat, Set[A], Bool],
			M, H *Arrow2[Nat, A, Real], n *Expr[Nat]) {
			Fn := a.TermAs[Set[Set[A]]]("F(n)")
			Mn := a.TermAs[Fun[A, Real]]("M(n)")
			Mnext := a.TermAs[Fun[A, Real]]("M(n + 1)")
			Hn := a.TermAs[Fun[A, Real]]("H(n)")
			a.Show(
				"the martingale relation and predictable bound center each weighted increment",
				By(MartingaleDef.At(Ω, S, μ, F, M), At(centeredFactor, Ω, S, μ, Fn, Mnext, Mn, Hn)))
		})
		finiteValues := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀F:(num → set(set(A))). " +
				"∀M H:(num → A → real). " +
				"∀n:num.",
			Hypotheses: []string{
				"martingale_on(Ω, S, μ, F, M)",
				"∀n:num. real_measurable(Ω, F(n), H(n))",
				"∀n:num. ∃C:real. measure_ae(Ω, S, μ, λx:A. |H(n, x)| ≤ C)",
			},
			Conclusion: "real_integrable(Ω, S, μ, martingale_transform(M, H, n)) ∧ " +
				"real_measurable(Ω, F(n), martingale_transform(M, H, n))",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], F *Arrow2[Nat, Set[A], Bool],
			M, H *Arrow2[Nat, A, Real], n *Expr[Nat], assumptions Fact) {
			a.Induct(n)
			a.Base(
				"the zero-time transform is the original zero-time value",
				func(a *Argument) {
					a.Show(
						"the original conditional expectation supplies integrability and measurability",
						Simp(Fwd(MartingaleTransformDef), Fwd(real_sum.BelowClauses), Fwd(real_ring.AddRightId)),
						By(
							assumptions,
							MartingaleDef.At(Ω, S, μ, F, M),
							conditional_expectation.IsCondExpDef.At(Ω, S, μ,
								a.TermAs[Set[Set[A]]]("F(0)"),
								a.TermAs[Fun[A, Real]]("M(0 + 1)"), a.TermAs[Fun[A, Real]]("M(0)"))))
				})
			a.Step(
				"adjoin one integrable increment measurable at the next time",
				func(a *Argument, previous Fact) {
					Fn := a.TermAs[Set[Set[A]]]("F(n)")
					Fnext := a.TermAs[Set[Set[A]]]("F(n + 1)")
					Mn := a.TermAs[Fun[A, Real]]("M(n)")
					Mnext := a.TermAs[Fun[A, Real]]("M(n + 1)")
					Hn := a.TermAs[Fun[A, Real]]("H(n)")
					Tn := a.TermAs[Fun[A, Real]]("martingale_transform(M, H, n)")
					increment := a.TermAs[Fun[A, Real]]("«increment»(M, H, n)")
					zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
					a.Do(Simp(Fwd(nat_arith.Add1)), Simp(Fwd(recurrence)))
					structure := a.Have(
						"the next filtration level contains the present information",
						"measure_on(Ω, S, μ) ∧ "+
							"sigma_algebra_on(Ω, F(n + 1)) ∧ "+
							"F(n) ⊆ F(n + 1) ∧ "+
							"real_measurable(Ω, F(n), M(n)) ∧ "+
							"real_measurable(Ω, F(n + 1), M(n + 1))",
						By(
							assumptions,
							MartingaleDef.At(Ω, S, μ, F, M),
							filtration.FiltrationDef.At(Ω, S, F),
							conditional_expectation.IsCondExpDef.At(Ω, S, μ, Fn, Mnext, Mn),
							conditional_expectation.IsCondExpDef.At(Ω, S, μ, Fnext,
								a.TermAs[Fun[A, Real]]("M(n + 1 + 1)"), Mnext)))
					a.Do(SplitConj(
						Case(
							"the partial sum remains integrable",
							By(
								structure,
								assumptions,
								previous,
								At(increments, Ω, S, μ, F, M, H, n),
								conditional_expectation.IsCondExpDef.At(Ω, S, μ, Fn, increment, zero),
								measure_integral.IntegrableAdd.At(Ω, S, μ, Tn, increment))),
						Case(
							"the partial sum is measurable at the next time",
							Derive(func(a *Argument) {
								transported := a.Have(
									"the previous value and both known factors are measurable at the next time",
									"real_measurable(Ω, F(n + 1), martingale_transform(M, H, n)) ∧ "+
										"real_measurable(Ω, F(n + 1), H(n)) ∧ "+
										"real_measurable(Ω, F(n + 1), M(n))",
									By(
										structure,
										assumptions,
										previous,
										measurable_function.RealMeasurableSourceMono.AsFact().At(Ω, Fn, Fnext)))
								measurableDifference := a.Have(
									"the adjacent martingale difference is measurable",
									"real_measurable(Ω, F(n + 1), «difference»(M(n + 1), M(n)))",
									ByArith(
										structure,
										transported,
										measurable_function.RealMeasurableNeg.At(Ω, Fnext, Mn),
										measurable_function.RealMeasurableAdd.At(Ω, Fnext, Mnext,
											a.TermAs[Fun[A, Real]]("λx:A. -M(n, x)"))))
								a.Show(
									"multiplication and addition preserve measurability",
									By(
										structure,
										transported,
										measurableDifference,
										measurable_function.RealMeasurableMul.At(Ω, Fnext, Hn,
											a.TermAs[Fun[A, Real]]("«difference»(M(n + 1), M(n))")),
										measurable_function.RealMeasurableAdd.At(Ω, Fnext, Tn, increment)))
							}))))
				})
		})
		return ctx.Theorem(headline, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], F *Arrow2[Nat, Set[A], Bool],
			M, H *Arrow2[Nat, A, Real], assumptions Fact) {
			a.Do(Simp(Fwd(MartingaleDef)))
			a.Do(SplitConj(
				Case(
					"the original filtration is retained",
					By(assumptions, MartingaleDef.At(Ω, S, μ, F, M))),
				Case(
					"each transformed successor conditions to the present value",
					Derive(func(a *Argument) {
						n := a.FixAs[Nat]("n")
						Fn := a.TermAs[Set[Set[A]]]("F(n)")
						Tn := a.TermAs[Fun[A, Real]]("martingale_transform(M, H, n)")
						increment := a.TermAs[Fun[A, Real]]("«increment»(M, H, n)")
						zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
						one := a.TermAs[Real]("&1")
						known := a.Have(
							"the integrable adapted transform is its own current conditional expectation",
							"is_cond_exp(Ω, S, μ, F(n), martingale_transform(M, H, n), martingale_transform(M, H, n))",
							By(
								assumptions,
								MartingaleDef.At(Ω, S, μ, F, M),
								conditional_expectation.IsCondExpDef.At(Ω, S, μ, Fn,
									a.TermAs[Fun[A, Real]]("M(n + 1)"), a.TermAs[Fun[A, Real]]("M(n)")),
								At(finiteValues, Ω, S, μ, F, M, H, n),
								conditional_expectation.CondExpIdentity.At(Ω, S, μ, Fn, Tn)))
						// ByArith normalizes CondExpLinear's bodies 1·T + 1·increment and
						// 1·T + 1·0 under λ to the recurrence's sum and to T.
						a.Show(
							"the next weighted increment adds zero to the conditional expectation",
							Simp(Fwd(recurrence)),
							ByArith(
								assumptions,
								known,
								At(increments, Ω, S, μ, F, M, H, n),
								conditional_expectation.CondExpLinear.At(Ω, S, μ, Fn, Tn, Tn, increment, zero, one, one)))
					}))))
		})
	}),
})}

// StoppedMartingaleDifferences — stopping a martingale difference row where
// its running conditional variance passes c leaves a martingale difference
// row, whose conditional variances are the stopped ones: the stopping event of
// time k is known at time k, so cutting ξ(k) to it keeps ξ(k) known at time
// k + 1 and centred, and cuts its conditional variance by the same event.
var StoppedMartingaleDifferences = stoppedMartingaleDifferencesThm{family.Add(registry.ProofEntry{
	Name: "StoppedMartingaleDifferences",
	Key:  "prop_6ddd25f11e313827",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀c:real.",
		Hypotheses: []string{"martingale_difference_row(Ω, S, μ, F, n, ξ, v)"},
		Conclusion: "martingale_difference_row(Ω, " +
			"    S, " +
			"    μ, " +
			"    F, " +
			"    n, " +
			"    «stoppedRow»(Ω, v, ξ, c), " +
			"    «stoppedRow»(Ω, v, v, c))",
		Abbrev: Abbrev{
			{Name: "cutEvent", Text: "λE:set(A). λX:(A → real). λx:A. COND(x ∈ E, X(x), &0)"},
			{Name: "stopEvent", Text: "λΩ:set(A). λv:(num → A → real). λc:real. λk:num. " +
				"    {x:A | x ∈ Ω ∧ Σ_{j<k + 1} v(j, x) ≤ c}"},
			{Name: "stoppedRow", Text: "λΩ:set(A). " +
				"λv:(num → A → real). " +
				"λξ:(num → A → real). " +
				"λc:real. " +
				"λk:num. " +
				"    «cutEvent»(«stopEvent»(Ω, v, c, k), ξ(k))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		squareCut := ctx.Lemma(
			"∀E:set(A). ∀X:(A → real). "+
				"    (λx:A. «cutEvent»(E, X, x) * «cutEvent»(E, X, x)) = «cutEvent»(E, λx:A. X(x) * X(x))",
			func(a *Argument, E *Expr[Set[A]], X *Arrow[A, Real]) {
				a.Do(Funext())
				a.FixAs[A]()
				a.Cases(a.Term("x ∈ E"))
				a.When(
					"the square is retained on the event",
					func(b *Argument, included Fact) {
						b.Show(
							"both sides square the original value",
							By(included))
					})
				a.Otherwise(
					"the square vanishes off the event",
					func(b *Argument, excluded Fact) {
						b.Show(
							"both sides are zero",
							ByArith(excluded))
					})
			})
		conditionalCut := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀G:set(set(A)). " +
				"∀E:set(A). " +
				"∀X Y:(A → real).",
			Hypotheses: []string{"is_cond_exp(Ω, S, μ, G, X, Y)", "E ∈ G"},
			Conclusion: "is_cond_exp(Ω, S, μ, G, «cutEvent»(E, X), «cutEvent»(E, Y))",
			Abbrev:     Abbrev{{Name: "retentionWeight", Text: "λx:A. COND(x ∈ E, &1, &0)"}},
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]], E *Expr[Set[A]], X, Y *Arrow[A, Real], assumptions Fact) {
			h := a.TermAs[Fun[A, Real]]("«retentionWeight»")
			one := a.TermAs[Real]("&1")
			base := a.Have(
				"the measure and conditioning sigma algebra",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, G)",
				By(assumptions, conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, X, Y)))
			measurable := a.Have(
				"the indicator of the conditioning event is measurable",
				"real_measurable(Ω, G, «retentionWeight»)",
				By(base, assumptions, measurable_function.RealMeasurableIndicator.At(Ω, G, E, one)))
			bounded := a.Have(
				"the indicator takes values zero and one",
				"∀x:A. |«retentionWeight»(x)| ≤ &1",
				Derive(func(b *Argument) {
					b.FixAs[A]()
					b.Cases(b.Term("x ∈ E"))
					b.When(
						"the indicator is one",
						func(d *Argument, included Fact) {
							d.Show(
								"one has absolute value one",
								ByArith(included))
						})
					b.Otherwise(
						"the indicator is zero",
						func(d *Argument, excluded Fact) {
							d.Show(
								"zero has absolute value zero",
								ByArith(excluded))
						})
				}))
			boundedAE := a.Have(
				"the bound holds almost everywhere",
				"measure_ae(Ω, S, μ, λx:A. |«retentionWeight»(x)| ≤ &1)",
				By(
					base,
					bounded,
					measure_space.AEOfEverywhere.At(Ω, S, μ, a.TermAs[Set[A]]("λx:A. |«retentionWeight»(x)| ≤ &1"))))
			cuts := a.Have(
				"multiplying by the indicator cuts out the complement",
				"∀Z:(A → real). (λx:A. «retentionWeight»(x) * Z(x)) = «cutEvent»(E, Z)",
				Derive(func(b *Argument) {
					b.FixAs[Fun[A, Real]]()
					b.Do(Funext())
					b.FixAs[A]("x")
					b.Cases(b.Term("x ∈ E"))
					b.When(
						"retain the original value",
						func(d *Argument, included Fact) {
							d.Show(
								"the multiplier is one",
								ByArith(included))
						})
					b.Otherwise(
						"discard the original value",
						func(d *Argument, excluded Fact) {
							d.Show(
								"the multiplier is zero",
								ByArith(excluded))
						})
				}))
			weighted := a.Have(
				"the known factor multiplies both sides",
				"is_cond_exp(Ω, S, μ, G, λx:A. «retentionWeight»(x) * X(x), λx:A. «retentionWeight»(x) * Y(x))",
				By(
					assumptions,
					measurable,
					boundedAE,
					conditional_expectation.CondExpKnownFactor.At(Ω, S, μ, G, X, Y, h, one)))
			a.Show(
				"both products are cuts",
				By(a.Simplified(weighted, Fwd(cuts))))
		})
		predictable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀F:(num → set(set(A))). " +
				"∀v:(num → A → real). " +
				"∀c:real. " +
				"∀k:num.",
			Hypotheses: []string{
				"filtration_on(Ω, S, F)",
				"∀j:num. j < k + 1 ⇒ real_measurable(Ω, F(j), v(j))",
			},
			Conclusion: "«stopEvent»(Ω, v, c, k) ∈ F(k)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], F *Arrow[Nat, Set[Set[A]]],
			v *Arrow2[Nat, A, Real], c *Expr[Real], k *Expr[Nat], assumptions Fact) {
			here := a.TermAs[Set[Set[A]]]("F(k)")
			structure := a.Have(
				"the current level is a sigma algebra",
				"sigma_algebra_on(Ω, F(k))",
				By(assumptions, filtration.FiltrationDef.At(Ω, S, F)))
			terms := a.Have(
				"all variances in the prefix are known at the current level",
				"∀j:num. j < k + 1 ⇒ real_measurable(Ω, F(k), v(j))",
				Derive(func(b *Argument) {
					j := b.FixAs[Nat]()
					inPrefix := b.Assume()
					previous := b.Have(
						"the index is at most the current time",
						"j ≤ k",
						ByArith(inPrefix))
					b.Show(
						"measurability passes to the larger sigma algebra",
						By(
							previous,
							inPrefix,
							assumptions,
							filtration.FiltrationMono.At(Ω, S, F, j, k),
							measurable_function.RealMeasurableSourceMono.At(Ω, b.TermAs[Set[Set[A]]]("F(j)"), here,
								b.TermAs[Fun[A, Real]]("v(j)"))))
				}))
			prefix := a.Have(
				"the running variance is measurable",
				"real_measurable(Ω, F(k), λx:A. Σ_{j<k + 1} v(j, x))",
				By(structure, terms, measurable_function.RealMeasurableSum.At(Ω, here, v, a.TermAs[Nat]("k + 1"))))
			a.Show(
				"the cutoff is a measurable sublevel event",
				By(
					structure,
					prefix,
					measurable_function.RealMeasurableAtMost.At(Ω, here,
						a.TermAs[Fun[A, Real]]("λx:A. Σ_{j<k + 1} v(j, x)"), c)))
		})
		return ctx.Theorem(headline, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], F *Arrow[Nat, Set[Set[A]]],
			n *Expr[Nat], ξ, v *Arrow[Nat, Fun[A, Real]], c *Expr[Real], row Fact) {
			conditions := a.Conjuncts(
				a.Unfolded(row, MartingaleDifferenceRowDef),
				"F is a filtration",
				"below n each increment is a martingale difference with conditional variance v")
			isFiltration, differences := conditions[0], conditions[1]
			stopped := a.Have(
				"below n each stopped increment is a martingale difference with the stopped variance",
				Statement{
					Binders:    "∀k:num.",
					Hypotheses: []string{"k < n"},
					Conclusion: "real_measurable(Ω, F(k + 1), «stoppedRow»(Ω, v, ξ, c, k)) ∧ " +
						"is_cond_exp(Ω, S, μ, F(k), «stoppedRow»(Ω, v, ξ, c, k), λx:A. &0) ∧ " +
						"is_cond_exp(Ω, " +
						"    S, " +
						"    μ, " +
						"    F(k), " +
						"    λx:A. «stoppedRow»(Ω, v, ξ, c, k, x) * «stoppedRow»(Ω, v, ξ, c, k, x), " +
						"    «stoppedRow»(Ω, v, v, c, k))",
				},
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					inRow := b.Assume()
					here := b.TermAs[Set[Set[A]]]("F(k)")
					next := b.TermAs[Set[Set[A]]]("F(k + 1)")
					E := b.TermAs[Set[A]]("«stopEvent»(Ω, v, c, k)")
					increment := b.TermAs[Fun[A, Real]]("ξ(k)")
					variance := b.TermAs[Fun[A, Real]]("v(k)")
					square := b.TermAs[Fun[A, Real]]("λx:A. ξ(k, x) * ξ(k, x)")
					zero := b.TermAs[Fun[A, Real]]("λx:A. &0")
					variances := b.Have(
						"each variance is measurable at its own level",
						"∀j:num. j < k + 1 ⇒ real_measurable(Ω, F(j), v(j))",
						Derive(func(d *Argument) {
							d.FixAs[Nat]()
							inPrefix := d.Assume()
							prefixInRow := d.Have(
								"the prefix lies inside the row",
								"j < n",
								ByArith(inPrefix, inRow))
							d.Show(
								"conditional expectation supplies the measurability",
								By(
									prefixInRow,
									differences,
									conditional_expectation.IsCondExpDef.At(Ω, S, μ,
										d.TermAs[Set[Set[A]]]("F(j)"), d.TermAs[Fun[A, Real]]("λx:A. ξ(j, x) * ξ(j, x)"),
										d.TermAs[Fun[A, Real]]("v(j)"))))
						}))
					known := b.Have(
						"the cutoff event is known at the current level",
						"«stopEvent»(Ω, v, c, k) ∈ F(k)",
						By(isFiltration, variances, At(predictable, Ω, S, F, v, c, k)))
					original := b.Have(
						"the current increment satisfies the row conditions",
						"real_measurable(Ω, F(k + 1), ξ(k)) ∧ "+
							"is_cond_exp(Ω, S, μ, F(k), ξ(k), λx:A. &0) ∧ "+
							"is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k))",
						By(inRow, differences))
					nextLevel := b.Have(
						"the next level is a sigma algebra extending the current one",
						"sigma_algebra_on(Ω, F(k + 1)) ∧ F(k) ⊆ F(k + 1)",
						By(isFiltration, filtration.FiltrationDef.At(Ω, S, F)))
					knownNext := b.Have(
						"the cutoff is also known at the next level",
						"«stopEvent»(Ω, v, c, k) ∈ F(k + 1)",
						BySets(known, nextLevel))
					b.Show(
						"cut the adapted increment and its conditional variance",
						SplitConj(
							Case(
								"adaptedness and the conditional mean",
								SplitConj(
									Case(
										"cutting by a measurable event preserves adaptedness",
										By(
											knownNext,
											nextLevel,
											original,
											measurable_function.RealMeasurableOnEvent.At(Ω, next, E, increment))),
									Case(
										"cutting zero leaves zero",
										By(known, original, At(conditionalCut, Ω, S, μ, here, E, increment, zero))))),
							Case(
								"squaring commutes with cutting",
								Simp(Fwd(squareCut)),
								By(known, original, At(conditionalCut, Ω, S, μ, here, E, square, variance)))))
				}))
			a.Show(
				"the stopped row is a martingale difference row along the same filtration",
				Simp(Fwd(MartingaleDifferenceRowDef)),
				By(isFiltration, stopped))
		})
	}),
})}
