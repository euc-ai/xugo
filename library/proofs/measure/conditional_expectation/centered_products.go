// centered_products.go — a known factor times a conditionally centered
// variable integrates to zero. A bounded G-measurable factor B passes through
// the conditional expectation Y of X, so B·X and B·Y have one integral and
// B·(X − Y) integrates to zero. A G-measurable factor h with no bound, against
// an X of conditional expectation 0, still gives ∫h·X = 0 once h·X is
// integrable: truncate h at n, pass each truncation through the conditional
// expectation, and let n grow under the domination of |h·X|.

package conditional_expectation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// CondExpBoundedProductResidual — a bounded known factor times the residual
// X − Y of a conditional expectation Y of X integrates to zero: the factor
// passes through the conditional expectation, so B·X and B·Y are integrable
// with the same integral, and B·(X − Y) is their difference.
var CondExpBoundedProductResidual = condExpBoundedProductResidualThm{family.Add(registry.ProofEntry{
	Name: "CondExpBoundedProductResidual",
	Key:  "prop_e82958cc396e4a8a",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X Y B:(A → real). " +
			"∀C:real.",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, Y)",
			"real_measurable(Ω, G, B)",
			"measure_ae(Ω, S, μ, λx:A. |B(x)| ≤ C)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. B(x) * (X(x) - Y(x))) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. B(x) * (X(x) - Y(x))) = &0",
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, Y, B *Arrow[A, Real],
			C *Expr[Real],
			condExp, known, bounded Fact,
		) {
			left := a.TermAs[Fun[A, Real]]("λx:A. B(x) * X(x)")
			right := a.TermAs[Fun[A, Real]]("λx:A. B(x) * Y(x)")
			products := a.Have(
				"the bounded known factor B passes through the conditional expectation",
				"is_cond_exp(Ω, S, μ, G, λx:A. B(x) * X(x), λx:A. B(x) * Y(x))",
				By(condExp, known, bounded, CondExpKnownFactor.At(Ω, S, μ, G, X, Y, B, C)))
			integrable := a.Have(
				"so both products are integrable",
				"measure_on(Ω, S, μ) ∧ "+
					"real_integrable(Ω, S, μ, λx:A. B(x) * X(x)) ∧ "+
					"real_integrable(Ω, S, μ, λx:A. B(x) * Y(x))",
				By(products, IsCondExpDef.At(Ω, S, μ, G, left, right)))
			equal := a.Have(
				"and they have the same integral",
				"measure_integral(Ω, S, μ, λx:A. B(x) * X(x)) = measure_integral(Ω, S, μ, λx:A. B(x) * Y(x))",
				By(products, CondExpIntegral.At(Ω, S, μ, G, left, right)))
			difference := a.Have(
				"so their difference is integrable with integral zero",
				"real_integrable(Ω, S, μ, λx:A. B(x) * X(x) - B(x) * Y(x)) ∧ "+
					"measure_integral(Ω, S, μ, λx:A. B(x) * X(x) - B(x) * Y(x)) = &0",
				ByArith(
					Normalized,
					integrable,
					equal,
					measure_integral.IntegrableSub.At(Ω, S, μ, left, right),
					measure_integral.IntegralSub.At(Ω, S, μ, left, right)))
			distributes := a.Have(
				"B·(X − Y) is that difference",
				"(λx:A. B(x) * (X(x) - Y(x))) = λx:A. B(x) * X(x) - B(x) * Y(x)",
				Funext(),
				Derive(func(b *Argument) {
					x := b.FixAs[A]("x")
					b.Show(
						"multiplication distributes over the difference",
						By(real_ring.SubLeftDistrib.At(B.Apply(x), X.Apply(x), Y.Apply(x))))
				}))
			a.Show(
				"so the factor times the residual is integrable with integral zero",
				By(distributes, difference))
		}),
})}

// CondExpZeroPredictableProduct — a known factor h times a variable X of
// conditional expectation 0 integrates to zero wherever the product h·X is
// integrable, h being G-measurable and nothing more. Truncate h at n, to 0
// where |h| exceeds n. Each truncation is a known factor bounded by n, which
// passes through the conditional expectation, so its product with X has
// integral 0. At every point the truncation is h from some n on, so the
// products converge to h·X, and |h·X| dominates them all: by dominated
// convergence their integrals, all 0, converge to the integral of h·X.
var CondExpZeroPredictableProduct = condExpZeroPredictableProductThm{family.Add(registry.ProofEntry{
	Name: "CondExpZeroPredictableProduct",
	Key:  "prop_c6b1555f1744b576",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀X h:(A → real).",
		Hypotheses: []string{
			"is_cond_exp(Ω, S, μ, G, X, λx:A. &0)",
			"real_measurable(Ω, G, h)",
			"real_integrable(Ω, S, μ, λx:A. h(x) * X(x))",
		},
		Conclusion: "measure_integral(Ω, S, μ, λx:A. h(x) * X(x)) = &0",
		Abbrev: Abbrev{
			{Name: "large", Text: "λn:num. {y:A | y ∈ Ω ∧ &n < |h(y)|}"},
			{Name: "truncated", Text: "λn:num. λy:A. COND(y ∉ «large»(n), h(y), &0)"},
		},
	},
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			G *Expr[Set[Set[A]]],
			X, h *Arrow[A, Real],
			centered, known, integrable Fact,
		) {
			zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
			product := a.TermAs[Fun[A, Real]]("λx:A. h(x) * X(x)")
			setting := a.Have(
				"μ is a measure on S, and S and G are σ-algebras on Ω",
				"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(Ω, G)",
				By(centered, IsCondExpDef.At(Ω, S, μ, G, X, zero), measure_space.MeasureOn.At(Ω, S, μ)))

			// Truncate h at n.
			size := a.Have(
				"|h| is G-measurable",
				"real_measurable(Ω, G, λx:A. |h(x)|)",
				By(setting, known, measurable_function.RealMeasurableAbs.At(Ω, G, h)))
			largeEvents := a.Have(
				"so the points of Ω where |h| exceeds n form an event of G",
				"∀n:num. «large»(n) ∈ G",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.Show(
						"a G-measurable function pulls each ray back into G",
						By(
							setting,
							size,
							measurable_function.RealMeasurableIffRay.At(Ω, G, b.TermAs[Fun[A, Real]]("λx:A. |h(x)|"))))
				}))
			truncatedMeasurable := a.Have(
				"and h truncated at n, cut to 0 on that event, is G-measurable",
				"∀n:num. real_measurable(Ω, G, «truncated»(n))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"a cut of a measurable function to 0 on an event is measurable",
						By(
							setting,
							known,
							largeEvents.At(n),
							measurable_function.RealMeasurableCut.At(Ω, G, b.TermAs[Set[A]]("«large»(n)"), h)))
				}))
			truncatedBound := a.Have(
				"h truncated at n is at most n in size on Ω",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ |«truncated»(n, x)| ≤ &n",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[A]("x")
					inΩ := b.Assume()
					outside := b.Have(
						"x lies outside the event exactly where |h(x)| ≤ n",
						"x ∉ «large»(n) ⇔ |h(x)| ≤ &n",
						BySets(inΩ, real_order_ring.NotLessThan.At(b.TermAs[Real]("&n"), b.TermAs[Real]("|h(x)|"))))
					b.Show(
						"there the truncation is h(x), and elsewhere 0",
						ByArith(outside, real_order_ring.NumNonneg.At(n), real_sgn_abs.AbsOfZero))
				}))

			// Each truncation is a known factor bounded by n, so CondExpKnownFactor applies.
			cutProducts := a.Have(
				"each truncation passes through the conditional expectation, "+
					"so its product with X has conditional expectation 0",
				"∀n:num. is_cond_exp(Ω, S, μ, G, λx:A. «truncated»(n, x) * X(x), λx:A. &0)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					bound := b.TermAs[Real]("&n")
					almost := b.Have(
						"the bound n holds almost everywhere",
						"measure_ae(Ω, S, μ, λx:A. |«truncated»(n, x)| ≤ &n)",
						By(
							setting,
							truncatedBound.At(n),
							measure_space.AEOfEverywhere.At(Ω, S, μ, b.TermAs[Set[A]]("λx:A. |«truncated»(n, x)| ≤ &n"))))
					vanishing := b.Have(
						"the truncation times 0 is 0",
						"(λx:A. «truncated»(n, x) * &0) = λx:A. &0",
						Funext(),
						Derive(func(c *Argument) {
							c.FixAs[A]("x")
							c.Show(
								"a product with 0 is 0",
								ByArith())
						}))
					b.Show(
						"the known factor passes through",
						By(
							centered,
							truncatedMeasurable.At(n),
							almost,
							vanishing,
							CondExpKnownFactor.At(Ω, S, μ, G, X, zero, b.TermAs[Fun[A, Real]]("«truncated»(n)"), bound)))
				}))
			cutIntegrals := a.Have(
				"so each product is S-measurable with integral 0",
				"∀n:num. "+
					"    real_measurable(Ω, S, λx:A. «truncated»(n, x) * X(x)) ∧ "+
					"    measure_integral(Ω, S, μ, λx:A. «truncated»(n, x) * X(x)) = &0",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					cut := b.TermAs[Fun[A, Real]]("λx:A. «truncated»(n, x) * X(x)")
					b.Show(
						"a conditional expectation is integrable, and keeps the integral",
						By(
							cutProducts.At(n),
							IsCondExpDef.At(Ω, S, μ, G, cut, zero),
							measure_integral.RealIntegrableDef.At(Ω, S, μ, cut),
							CondExpIntegral.At(Ω, S, μ, G, cut, zero),
							measure_integral.IntegralZero.At(Ω, S, μ)))
				}))

			// Dominated convergence under |h·X|.
			dominating := a.Have(
				"|h·X| is integrable, h·X being so",
				"real_integrable(Ω, S, μ, λx:A. |h(x) * X(x)|)",
				By(setting, integrable, measure_integral.IntegrableAbs.At(Ω, S, μ, product)))
			dominated := a.Have(
				"|h·X| dominates every product, the truncation being h or 0",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ |«truncated»(n, x) * X(x)| ≤ |h(x) * X(x)|",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					b.FixAs[A]("x")
					b.Assume()
					b.Show(
						"|h(x)X(x)| is nonnegative and |0| = 0",
						ByArith(real_sgn_abs.AbsNonneg.At(b.TermAs[Real]("h(x) * X(x)")), real_sgn_abs.AbsOfZero))
				}))
			converges := a.Have(
				"at every point of Ω the products converge to h·X, being h(x)X(x) from some n on",
				"∀x:A. x ∈ Ω ⇒ (λn:num. «truncated»(n, x) * X(x)) ⟶ h(x) * X(x)",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Assume()
					N, above := b.ObtainAs[Nat](
						"some N exceeds |h(x)|",
						"∃N:num. |h(x)| < &N",
						ByArith(real_archimedean.Archimedean.At(b.TermAs[Real]("&1"), b.TermAs[Real]("|h(x)|"))))
					eventually := b.Have(
						"from N on the truncation at x is h(x)",
						"∀n:num. N ≤ n ⇒ «truncated»(n, x) * X(x) = h(x) * X(x)",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							late := c.Assume()
							below := c.Have(
								"|h(x)| < N ≤ n",
								"|h(x)| ≤ &n",
								ByArith(late, above, real_construction.OfNumLessEq.At(N, n)))
							outside := c.Have(
								"so x lies outside the event where |h| exceeds n",
								"x ∉ «large»(n)",
								BySets(below, real_order_ring.NotLessThan.At(c.TermAs[Real]("&n"), c.TermAs[Real]("|h(x)|"))))
							c.Show(
								"and the truncation keeps h(x)",
								ByArith(outside))
						}))
					constant := b.TermAs[Fun[Nat, Real]]("λn:num. h(x) * X(x)")
					value := b.TermAs[Real]("h(x) * X(x)")
					b.Show(
						"equal from N on to the constant sequence at h(x)X(x), which converges there",
						By(
							eventually,
							real_sequences.LimitConst.At(value),
							real_sequences.LimitEventuallyEqual.At(
								constant,
								b.TermAs[Fun[Nat, Real]]("λn:num. «truncated»(n, x) * X(x)"),
								value,
								N)))
				}))
			sequence := a.TermAs[Fun[Nat, Real]](
				"λn:num. measure_integral(Ω, S, μ, λx:A. «truncated»(n, x) * X(x))")
			limit := a.Have(
				"by dominated convergence the integrals of the products converge to the integral of h·X",
				"(λn:num. measure_integral(Ω, S, μ, λx:A. «truncated»(n, x) * X(x))) ⟶ "+
					"measure_integral(Ω, S, μ, λx:A. h(x) * X(x))",
				By(
					setting,
					cutIntegrals,
					converges,
					dominated,
					dominating,
					integral_convergence.DominatedConvergence.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. «truncated»(n, x) * X(x)"),
						product,
						a.TermAs[Fun[A, Real]]("λx:A. |h(x) * X(x)|"))))

			// The limit: a sequence of zeros converges to 0 alone.
			zeros := a.Have(
				"but those integrals are all 0",
				"(λn:num. measure_integral(Ω, S, μ, λx:A. «truncated»(n, x) * X(x))) = (λn:num. &0)",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.Show(
						"the integral of each product is 0",
						By(cutIntegrals.At(n)))
				}))
			a.Show(
				"so the integral of h·X is their limit, 0",
				By(
					limit,
					zeros,
					real_sequences.LimitConst.At(a.TermAs[Real]("&0")),
					real_sequences.LimitUnique.At(
						sequence, a.TermAs[Real]("measure_integral(Ω, S, μ, λx:A. h(x) * X(x))"), a.TermAs[Real]("&0"))))
		}),
})}
