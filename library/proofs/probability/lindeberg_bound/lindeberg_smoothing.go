// lindeberg_smoothing.go — Lindeberg's replacement along a row of martingale differences,
// smoothed by a normal variable of the variance the row leaves of its clock.

package lindeberg_bound

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/product_measure"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_convolution"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_moments"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_taylor"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/registry"
)

// MartingaleLindebergSmoothing — Lindeberg's replacement along a row of martingale
// differences, with a clock c: the expectation of D(0) at the row's sum, smoothed by a normal
// variable of the variance the row leaves of c, is within M₃·ε·c/6 + M₂·L + (M₃/3)·c·√(ε² + L)
// of the normal integral of D(0) at √c, L the Lindeberg sum at ε. Write Φ(k) for D(0) at the
// first k terms smoothed by the variance left after them. Φ(0) is the normal integral and Φ(n)
// the integrand on the left, so the difference telescopes into the n replacements
// Φ(k + 1) − Φ(k); stepBound bounds each by its budget, Taylor's formula against the two
// conditional moments of ξ(k), and rowMoments sums the three parts of the budgets.
var MartingaleLindebergSmoothing = martingaleLindebergSmoothingThm{family.Add(registry.ProofEntry{
	Name: "MartingaleLindebergSmoothing",
	Key:  "prop_b9336dfbd143ea46",
	Reading: "c is the clock: the row's conditional variances sum to at most c, and what " +
		"is left of c after the row is spent on a normal variable. F(k) is what is known " +
		"before ξ(k), which is F(k + 1)-measurable, and v(k) is the conditional variance of " +
		"ξ(k). D is a tower of derivatives with test function D(0); no bound is asked of D(1). " +
		"The constant M₃/3 stands for M₃/6 times the third absolute moment of the standard " +
		"normal distribution, 2·√(2/π). At n = 0 the left side is 0 and the right side M₃·ε·c/2.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → set(set(A))). " +
			"∀n:num. " +
			"∀ξ v:(num → A → real). " +
			"∀D:(num → real → real). " +
			"∀c M₂ M₃ ε:real.",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"martingale_difference_row(Ω, S, μ, F, n, ξ, v)",
			"measure_ae(Ω, S, μ, λx:A. real_sum({k:num | k < n}, λk:num. v(k, x)) ≤ c)",
			"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
			"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
			"&0 < ε",
		},
		Conclusion: "|expectation(Ω, " +
			"    S, " +
			"    μ, " +
			"    λx:A. " +
			"        expectation(𝕌, " +
			"            borel_sets(real_topology), " +
			"            normal_distribution(&0, &1), " +
			"            λy:real. " +
			"                D(0)(real_sum({k:num | k < n}, λk:num. ξ(k, x)) + " +
			"                    real_sqrt(c - real_sum({k:num | k < n}, λk:num. v(k, x))) * y))) - " +
			"expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. D(0)(real_sqrt(c) * y))| ≤ " +
			"M₃ * ε / &6 * c + " +
			"M₂ * lindeberg_sum(Ω, S, μ, n, ξ, ε) + " +
			"M₃ / &3 * c * real_sqrt(real_pow(ε, 2) + lindeberg_sum(Ω, S, μ, n, ξ, ε))",
		Abbrev: Abbrev{
			{Name: "gauss", Text: "λf:(real → real). " +
				"    expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), f)"},
			{Name: "rowSum", Text: "λm:num. λx:A. real_sum({i:num | i < m}, λi:num. ξ(i, x))"},
			{Name: "rowVariance", Text: "λm:num. λx:A. real_sum({i:num | i < m}, λi:num. v(i, x))"},
			{Name: "smoothed", Text: "λm:num. λx:A. " +
				"    «gauss»(λy:real. D(0)(«rowSum»(m, x) + real_sqrt(c - «rowVariance»(m, x)) * y))"},
			{Name: "derivativeAverage", Text: "λi:num. λm:num. λx:A. " +
				"    «gauss»(λy:real. D(i)(«rowSum»(m, x) + real_sqrt(c - «rowVariance»(m + 1, x)) * y))"},
			{Name: "withinClock", Text: "λx:A. " +
				"    (∀j:num. j < n ⇒ &0 ≤ v(j, x)) ∧ " +
				"    (∀j:num. j ≤ n ⇒ &0 ≤ «rowVariance»(j, x) ∧ «rowVariance»(j, x) ≤ c)"},
			{Name: "stepCost", Text: "λk:num. λx:A. " +
				"    M₃ * ε / &6 * (ξ(k, x) * ξ(k, x)) + " +
				"    M₂ * COND(ε < |ξ(k, x)|, ξ(k, x) * ξ(k, x), &0) + " +
				"    M₃ / &3 * (v(k, x) * real_sqrt(v(k, x)))"},
			{Name: "stepBudget", Text: "λk:num. " +
				"    M₃ * ε / &6 * measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) + " +
				"    M₂ * event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x)) + " +
				"    M₃ / &3 * measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A conditional variance of a square is nonnegative almost everywhere: CondExpMono
			// against the conditional expectation 0 of 0.
			varianceNonnegative := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real).",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"∀k:num. k < n ⇒ is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k))",
				},
				Conclusion: "measure_ae(Ω, S, μ, λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				probability, conditional Fact,
			) {
				zero := a.TermAs[Fun[A, Real]]("λx:A. &0")
				space := a.Have(
					"a probability is a measure, under which 0 is integrable",
					"measure_on(Ω, S, μ) ∧ real_integrable(Ω, S, μ, λx:A. &0)",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						probability_space.ExpectationConstant.At(Ω, S, μ, a.TermAs[Real]("&0"))))
				termwise := a.Have(
					"each conditional variance is nonnegative almost everywhere",
					"∀j:num. measure_ae(Ω, S, μ, λx:A. j < n ⇒ &0 ≤ v(j, x))",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						b.Cases(b.TermAs[Bool]("j < n"))
						b.When(
							"within the row v(j) dominates the conditional expectation 0 of 0",
							func(c *Argument, early Fact) {
								field := F.Apply(j)
								square := c.TermAs[Fun[A, Real]]("λx:A. ξ(j, x) * ξ(j, x)")
								variance := c.TermAs[Fun[A, Real]]("v(j)")
								conditionalAt := c.Have(
									"v(j) is the conditional expectation of ξ(j)² given F(j)",
									"is_cond_exp(Ω, S, μ, F(j), λx:A. ξ(j, x) * ξ(j, x), v(j))",
									By(conditional, early))
								zeroConditional := c.Have(
									"0 is its own conditional expectation",
									"is_cond_exp(Ω, S, μ, F(j), λx:A. &0, λx:A. &0)",
									By(
										space,
										conditionalAt,
										conditional_expectation.IsCondExpDef.At(Ω, S, μ, field, square, variance),
										measurable_function.RealMeasurableConst.At(Ω, field, c.TermAs[Real]("&0")),
										conditional_expectation.CondExpIdentity.At(Ω, S, μ, field, zero)))
								squareNonnegative := c.Have(
									"ξ(j)² is nonnegative",
									"measure_ae(Ω, S, μ, λx:A. &0 ≤ ξ(j, x) * ξ(j, x))",
									By(
										space,
										measure_space.AEOfEverywhere.At(
											Ω, S, μ, c.TermAs[Set[A]]("λx:A. &0 ≤ ξ(j, x) * ξ(j, x)")),
										real_order_ring.SquareNonneg))
								c.Show(
									"conditional expectation is monotone",
									By(
										conditionalAt,
										zeroConditional,
										squareNonnegative,
										conditional_expectation.CondExpMono.At(Ω, S, μ, field, zero, zero, square, variance),
										measure_space.AEMono.At(
											Ω,
											S,
											μ,
											c.TermAs[Set[A]]("λx:A. &0 ≤ v(j, x)"),
											c.TermAs[Set[A]]("λx:A. j < n ⇒ &0 ≤ v(j, x)"))))
							})
						b.Otherwise(
							"beyond the row there is nothing to prove",
							func(c *Argument, late Fact) {
								c.Show(
									"the implication holds everywhere",
									By(
										Normalized,
										space,
										late,
										measure_space.AEOfEverywhere.At(
											Ω, S, μ, c.TermAs[Set[A]]("λx:A. j < n ⇒ &0 ≤ v(j, x)"))))
							})
					}))
				a.Show(
					"countably many almost-everywhere statements hold together",
					By(
						space,
						termwise,
						measure_space.AECountable.At(
							Ω, S, μ, a.TermAs[Fun2[Nat, A, Bool]]("λj:num. λx:A. j < n ⇒ &0 ≤ v(j, x)"))))
			})
			// The prefix sums of nonnegative terms lie between 0 and the whole sum.
			prefixSumBounds := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀w:(num → real). ∀k:num.",
				Hypotheses: []string{
					"∀i:num. i < n ⇒ &0 ≤ w(i)",
					"k ≤ n",
				},
				Conclusion: "&0 ≤ sum({i:num | i < k}, w) ∧ sum({i:num | i < k}, w) ≤ sum({i:num | i < n}, w)",
			}, func(a *Argument, n *Expr[Nat], w *Arrow[Nat, Real], k *Expr[Nat], nonnegative, within Fact) {
				prefix := a.TermAs[Set[Nat]]("{i:num | i < k}")
				whole := a.TermAs[Set[Nat]]("{i:num | i < n}")
				included := a.Have(
					"the prefix is a part of the row",
					"{i:num | i < k} ⊆ {i:num | i < n}",
					BySets(within, nat_order.LessThanLessEqTrans))
				onPrefix := a.Have(
					"the terms of the prefix are nonnegative",
					"∀i:num. i ∈ {j:num | j < k} ⇒ &0 ≤ w(i)",
					BySets(included, nonnegative))
				outside := a.Have(
					"so are the terms left out",
					"∀i:num. i ∈ {j:num | j < n} ∖ {j:num | j < k} ⇒ &0 ≤ w(i)",
					BySets(nonnegative))
				a.Show(
					"a sum of nonnegative terms is nonnegative and grows with its range",
					By(
						included,
						onPrefix,
						outside,
						real_sum.Nonneg.At(prefix, w),
						real_sum.Subset.At(prefix, whole, w),
						num_segment.FiniteBelowStrict.At(n)))
			})

			// Almost everywhere the variances are nonnegative and every prefix of them lies in
			// [0, c].
			clockEvent := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀n:num. " +
					"∀v:(num → A → real). " +
					"∀c:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"measure_ae(Ω, S, μ, λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x))",
					"measure_ae(Ω, S, μ, λx:A. Σ_{j<n} v(j, x) ≤ c)",
				},
				Conclusion: "measure_ae(Ω, " +
					"    S, " +
					"    μ, " +
					"    λx:A. " +
					"        (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ " +
					"        (∀k:num. k ≤ n ⇒ &0 ≤ Σ_{j<k} v(j, x) ∧ Σ_{j<k} v(j, x) ≤ c))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				n *Expr[Nat],
				v *Arrow2[Nat, A, Real],
				c *Expr[Real],
				probability, nonnegative, budget Fact,
			) {
				nonnegativeRow := a.TermAs[Set[A]]("λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x)")
				withinBudget := a.TermAs[Set[A]]("λx:A. Σ_{j<n} v(j, x) ≤ c")
				both := a.Have(
					"almost everywhere the variances are nonnegative and sum to at most c",
					"measure_ae(Ω, S, μ, λx:A. (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{j<n} v(j, x) ≤ c)",
					By(
						probability,
						nonnegative,
						budget,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.AEConjunction.At(Ω, S, μ, nonnegativeRow, withinBudget)))
				prefixes := a.Have(
					"there every prefix of the variances lies in [0, c]",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ Ω",
							"(∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{j<n} v(j, x) ≤ c",
						},
						Conclusion: "(∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ " +
							"(∀k:num. k ≤ n ⇒ &0 ≤ Σ_{j<k} v(j, x) ∧ Σ_{j<k} v(j, x) ≤ c)",
					},
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						clockAt := b.Assume()
						bounded := b.Have(
							"every prefix lies between 0 and the whole sum, which is at most c",
							"∀k:num. k ≤ n ⇒ &0 ≤ Σ_{j<k} v(j, x) ∧ Σ_{j<k} v(j, x) ≤ c",
							Derive(func(d *Argument) {
								k := d.FixAs[Nat]("k")
								within := d.Assume()
								prefix := d.Have(
									"the prefix lies between 0 and the whole sum",
									"&0 ≤ Σ_{j<k} v(j, x) ∧ Σ_{j<k} v(j, x) ≤ Σ_{j<n} v(j, x)",
									By(clockAt, within, At(prefixSumBounds, n, d.TermAs[Fun[Nat, Real]]("λj:num. v(j, x)"), k)))
								d.Show(
									"the whole sum is at most c",
									ByArith(prefix, clockAt))
							}))
						b.Show(
							"the variances stay nonnegative",
							By(bounded, clockAt))
					}))
				a.Show(
					"so the prefix bounds hold almost everywhere",
					By(
						both,
						prefixes,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							a.TermAs[Set[A]]("λx:A. (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{j<n} v(j, x) ≤ c"),
							a.TermAs[Set[A]](
								"λx:A. "+
									"    (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ "+
									"    (∀k:num. k ≤ n ⇒ &0 ≤ Σ_{j<k} v(j, x) ∧ Σ_{j<k} v(j, x) ≤ c)"))))
			})
			// Square-integrable p and q have square-integrable sum and integrable product:
			// (p + q)² ≤ 2(p² + q²) and |p·q| ≤ p² + q².
			productSquareIntegrable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p q:(A → real).",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_measurable(Ω, S, p)",
					"real_measurable(Ω, S, q)",
					"real_integrable(Ω, S, μ, λx:A. p(x) * p(x))",
					"real_integrable(Ω, S, μ, λx:A. q(x) * q(x))",
				},
				Conclusion: "real_integrable(Ω, S, μ, λx:A. (p(x) + q(x)) * (p(x) + q(x))) ∧ " +
					"real_integrable(Ω, S, μ, λx:A. p(x) * q(x))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				p, q *Arrow[A, Real],
				probability, pMeasurable, qMeasurable, pSquare, qSquare Fact,
			) {
				sum := a.TermAs[Fun[A, Real]]("λx:A. p(x) + q(x)")
				sumSquare := a.TermAs[Fun[A, Real]]("λx:A. (p(x) + q(x)) * (p(x) + q(x))")
				product := a.TermAs[Fun[A, Real]]("λx:A. p(x) * q(x)")
				squares := a.TermAs[Fun[A, Real]]("λx:A. p(x) * p(x) + q(x) * q(x)")
				space := a.Have(
					"a probability is a measure on a σ-algebra",
					"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ)))
				measurable := a.Have(
					"p + q, its square and p·q are measurable",
					"real_measurable(Ω, S, λx:A. p(x) + q(x)) ∧ "+
						"real_measurable(Ω, S, λx:A. (p(x) + q(x)) * (p(x) + q(x))) ∧ "+
						"real_measurable(Ω, S, λx:A. p(x) * q(x))",
					By(
						pMeasurable,
						qMeasurable,
						space,
						measurable_function.RealMeasurableAdd.At(Ω, S, p, q),
						measurable_function.RealMeasurableMul.At(Ω, S, sum, sum),
						measurable_function.RealMeasurableMul.At(Ω, S, p, q)))
				majorants := a.Have(
					"p² + q² and twice it are integrable",
					"real_integrable(Ω, S, μ, λx:A. p(x) * p(x) + q(x) * q(x)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. &2 * (p(x) * p(x) + q(x) * q(x)))",
					By(
						pSquare,
						qSquare,
						space,
						measure_integral.IntegrableAdd.At(
							Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. p(x) * p(x)"), a.TermAs[Fun[A, Real]]("λx:A. q(x) * q(x)")),
						measure_integral.IntegrableScale.At(Ω, S, μ, squares, a.TermAs[Real]("&2"))))
				pointwise := a.Have(
					"(p + q)² ≤ 2(p² + q²) and |p·q| ≤ p² + q²",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ Ω",
						},
						Conclusion: "|(p(x) + q(x)) * (p(x) + q(x))| ≤ &2 * (p(x) * p(x) + q(x) * q(x)) ∧ " +
							"|p(x) * q(x)| ≤ p(x) * p(x) + q(x) * q(x)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Assume()
						b.Show(
							"the squares of p − q and p + q are nonnegative",
							ByArith(
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("p(x) - q(x)")),
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("p(x) + q(x)")),
								real_order_ring.SquareNonneg.At(p.Apply(x)),
								real_order_ring.SquareNonneg.At(q.Apply(x)),
								real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("(p(x) + q(x)) * (p(x) + q(x))")),
								real_sgn_abs.AbsBounds.At(
									b.TermAs[Real]("p(x) * q(x)"), b.TermAs[Real]("p(x) * p(x) + q(x) * q(x)"))))
					}))
				a.Show(
					"both are dominated by integrable functions",
					By(
						measurable,
						majorants,
						pointwise,
						measure_integral.IntegrableDominated.At(
							Ω, S, μ, sumSquare, a.TermAs[Fun[A, Real]]("λx:A. &2 * (p(x) * p(x) + q(x) * q(x))")),
						measure_integral.IntegrableDominated.At(Ω, S, μ, product, squares)))
			})
			// The first k terms of the row are measurable and square-integrable for F(k), and
			// v(0), …, v(k) integrable there.
			rowAtField := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real). " +
					"∀k:num.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"filtration_on(Ω, S, F)",
					"∀j:num. " +
						"    j < n ⇒ " +
						"    real_measurable(Ω, F(j + 1), ξ(j)) ∧ " +
						"    is_cond_exp(Ω, S, μ, F(j), λx:A. ξ(j, x) * ξ(j, x), v(j))",
					"k ≤ n",
				},
				Conclusion: "probability_on(Ω, F(k), μ) ∧ " +
					"(∀j:num. " +
					"    j < k ⇒ " +
					"    real_measurable(Ω, F(k), ξ(j)) ∧ real_integrable(Ω, F(k), μ, λx:A. ξ(j, x) * ξ(j, x))) ∧ " +
					"(∀j:num. j < k + 1 ∧ j < n ⇒ real_integrable(Ω, F(k), μ, v(j)))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				k *Expr[Nat],
				probability, isFiltration, row, kWithin Fact,
			) {
				fieldK := F.Apply(k)
				fields := a.Have(
					"each field of the filtration is a σ-algebra inside S",
					"∀i:num. sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S",
					By(isFiltration, filtration.FiltrationDef.At(Ω, S, F)))
				atK := a.Have(
					"F(k) is a σ-algebra inside S, on which μ is again a probability",
					"sigma_algebra_on(Ω, F(k)) ∧ F(k) ⊆ S ∧ measure_on(Ω, S, μ) ∧ probability_on(Ω, F(k), μ)",
					By(
						probability,
						fields.At(k),
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						probability_space.ProbabilityOnDef.At(Ω, fieldK, μ),
						measure_space.SubSigmaMeasure.At(Ω, S, μ, fieldK)))
				increments := a.Have(
					"the first k increments are F(k)-measurable and square-integrable there",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j < k",
						},
						Conclusion: "real_measurable(Ω, F(k), ξ(j)) ∧ real_integrable(Ω, F(k), μ, λx:A. ξ(j, x) * ξ(j, x))",
					},
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						early := b.Assume()
						increment := b.TermAs[Fun[A, Real]]("ξ(j)")
						square := b.TermAs[Fun[A, Real]]("λx:A. ξ(j, x) * ξ(j, x)")
						next := b.TermAs[Nat]("j + 1")
						order := b.Have(
							"j lies in the row and j + 1 ≤ k",
							"j < n ∧ j + 1 ≤ k",
							ByArith(early, kWithin))
						term := b.Have(
							"ξ(j) is F(j + 1)-measurable and ξ(j)² integrable, as v(j) is its conditional variance",
							"real_measurable(Ω, F(j + 1), ξ(j)) ∧ real_integrable(Ω, S, μ, λx:A. ξ(j, x) * ξ(j, x))",
							By(
								row.At(j),
								order,
								conditional_expectation.IsCondExpDef.At(
									Ω, S, μ, F.Apply(j), square, b.TermAs[Fun[A, Real]]("v(j)"))))
						measurable := b.Have(
							"ξ(j) and ξ(j)² are F(k)-measurable, since F(j + 1) ⊆ F(k)",
							"real_measurable(Ω, F(k), ξ(j)) ∧ real_measurable(Ω, F(k), λx:A. ξ(j, x) * ξ(j, x))",
							By(
								isFiltration,
								atK,
								order,
								term,
								filtration.FiltrationMono.At(Ω, S, F, next, k),
								measurable_function.RealMeasurableSourceMono.At(Ω, F.Apply(next), fieldK, increment),
								measurable_function.RealMeasurableMul.At(Ω, fieldK, increment, increment)))
						b.Show(
							"integrability passes to the sub-σ-algebra",
							By(atK, term, measurable, measure_integral.SubSigmaRealIntegral.At(Ω, S, μ, fieldK, square)))
					}))
				variances := a.Have(
					"v(0), …, v(k) are integrable on F(k)",
					"∀j:num. j < k + 1 ∧ j < n ⇒ real_integrable(Ω, F(k), μ, v(j))",
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						early := b.Assume()
						variance := b.TermAs[Fun[A, Real]]("v(j)")
						order := b.Have(
							"j ≤ k and j lies in the row",
							"j ≤ k ∧ j < n",
							ByArith(early))
						term := b.Have(
							"v(j) is F(j)-measurable and integrable, as a conditional expectation",
							"real_measurable(Ω, F(j), v(j)) ∧ real_integrable(Ω, S, μ, v(j))",
							By(
								row.At(j),
								order,
								conditional_expectation.IsCondExpDef.At(
									Ω, S, μ, F.Apply(j), b.TermAs[Fun[A, Real]]("λx:A. ξ(j, x) * ξ(j, x)"), variance)))
						measurable := b.Have(
							"v(j) is F(k)-measurable, since F(j) ⊆ F(k)",
							"real_measurable(Ω, F(k), v(j))",
							By(
								isFiltration,
								order,
								term,
								filtration.FiltrationMono.At(Ω, S, F, j, k),
								measurable_function.RealMeasurableSourceMono.At(Ω, F.Apply(j), fieldK, variance)))
						b.Show(
							"integrability passes to the sub-σ-algebra",
							By(atK, term, measurable, measure_integral.SubSigmaRealIntegral.At(Ω, S, μ, fieldK, variance)))
					}))
				a.Show(
					"the three parts",
					By(atK, increments, variances))
			})
			// Integrating out the second variable of a product-measurable function leaves a
			// measurable function: Tonelli on its positive and negative parts.
			sectionIntegralMeasurable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀V:set(B). " +
					"∀T:set(set(B)). " +
					"∀ν:(set(B) → extended_nonneg_real). " +
					"∀f:(A → B → real).",
				Hypotheses: []string{
					"sigma_finite_on(Ω, S, μ)",
					"sigma_finite_on(V, T, ν)",
					"real_measurable(set_cross(Ω, V), product_sigma(Ω, S, V, T), λp:prod(A, B). f(fst(p), snd(p)))",
				},
				Conclusion: "real_measurable(Ω, S, λx:A. measure_integral(V, T, ν, λy:B. f(x, y)))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				V *Expr[Set[B]],
				T *Expr[Set[Set[B]]],
				ν *Arrow[Set[B], ExtendedNonnegReal],
				f *Arrow2[A, B, Real],
				μFinite, νFinite, measurable Fact,
			) {
				cross := a.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
				productField := a.TermAs[Set[Set[Prod[A, B]]]]("product_sigma(Ω, S, V, T)")
				joint := a.TermAs[Fun[Prod[A, B], Real]]("λq:prod(A, B). f(fst(q), snd(q))")
				positiveMass := a.TermAs[Fun[A, ExtendedNonnegReal]](
					"λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y)))")
				negativeMass := a.TermAs[Fun[A, ExtendedNonnegReal]](
					"λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y)))")
				positivePart := a.TermAs[Fun[A, Real]](
					"λx:A. extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y))))")
				negativePart := a.TermAs[Fun[A, Real]](
					"λx:A. -extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y))))")
				fields := a.Have(
					"both σ-finite measures live on σ-algebras",
					"sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(V, T)",
					By(
						μFinite,
						νFinite,
						measure_space.SigmaFiniteDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ),
						measure_space.SigmaFiniteDef.At(V, T, ν),
						measure_space.MeasureOn.At(V, T, ν)))
				productAlgebra := a.Have(
					"so does the product",
					"sigma_algebra_on(set_cross(Ω, V), product_sigma(Ω, S, V, T))",
					By(fields, measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
				extended := a.Have(
					"f and −f are extended-measurable on the product",
					"extended_measurable(set_cross(Ω, V), "+
						"    product_sigma(Ω, S, V, T), "+
						"    λq:prod(A, B). extended_of_real(f(fst(q), snd(q)))) ∧ "+
						"extended_measurable(set_cross(Ω, V), "+
						"    product_sigma(Ω, S, V, T), "+
						"    λq:prod(A, B). extended_of_real(-f(fst(q), snd(q))))",
					By(
						measurable,
						productAlgebra,
						measurable_function.RealMeasurableNeg.At(cross, productField, joint),
						measurable_function.ExtendedMeasurableOfReal.At(cross, productField, joint),
						measurable_function.ExtendedMeasurableOfReal.At(
							cross, productField, a.TermAs[Fun[Prod[A, B], Real]]("λq:prod(A, B). -f(fst(q), snd(q))"))))
				tonelli := a.Have(
					"by Tonelli the masses of the two parts are measurable in x",
					"extended_measurable(Ω, S, λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y)))) ∧ "+
						"extended_measurable(Ω, S, λx:A. nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y))))",
					By(
						μFinite,
						νFinite,
						extended,
						product_measure.ProductNonnegIntegral.At(
							Ω,
							S,
							μ,
							V,
							T,
							ν,
							a.TermAs[Fun2[A, B, ExtendedNonnegReal]]("λx:A. λy:B. extended_of_real(f(x, y))")),
						product_measure.ProductNonnegIntegral.At(
							Ω,
							S,
							μ,
							V,
							T,
							ν,
							a.TermAs[Fun2[A, B, ExtendedNonnegReal]]("λx:A. λy:B. extended_of_real(-f(x, y))"))))
				parts := a.Have(
					"their real parts are measurable",
					"real_measurable(Ω, "+
						"    S, "+
						"    λx:A. extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y))))) ∧ "+
						"real_measurable(Ω, "+
						"    S, "+
						"    λx:A. -extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y)))))",
					By(
						fields,
						tonelli,
						measurable_function.ExtendedMeasurableToReal.At(Ω, S, positiveMass),
						measurable_function.ExtendedMeasurableToReal.At(Ω, S, negativeMass),
						measurable_function.RealMeasurableNeg.At(
							Ω,
							S,
							a.TermAs[Fun[A, Real]](
								"λx:A. extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y))))"))))
				split := a.Have(
					"the integral in y is the difference of the two parts",
					"(λx:A. measure_integral(V, T, ν, λy:B. f(x, y))) = "+
						"λx:A. "+
						"    extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(f(x, y)))) + "+
						"    -extended_to_real(nonneg_integral(V, T, ν, λy:B. extended_of_real(-f(x, y))))",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.Show(
							"the definition of the integral",
							ByArith(
								Normalized,
								measure_integral.RealIntegralDef.At(V, T, ν, b.TermAs[Fun[B, Real]]("λy:B. f(x, y)"))))
					}))
				a.Show(
					"a sum of measurable functions",
					By(
						fields,
						parts,
						split,
						measurable_function.RealMeasurableAdd.At(Ω, S, positivePart, negativePart)))
			})
			// x ↦ the ν-average of h(a(x) + s(x)·y) is measurable for measurable a and s and
			// Borel h: (x, y) ↦ h(a(x) + s(x)·y) is measurable on the product, and integrating
			// out y keeps measurability.
			gaussianAverageMeasurable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀ν:(set(real) → extended_nonneg_real). " +
					"∀a s:(A → real). " +
					"∀h:(real → real).",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"probability_on(𝕌, borel_sets(real_topology), ν)",
					"real_measurable(Ω, S, a)",
					"real_measurable(Ω, S, s)",
					"real_measurable(𝕌, borel_sets(real_topology), h)",
				},
				Conclusion: "real_measurable(Ω, " +
					"    S, " +
					"    λx:A. expectation(𝕌, borel_sets(real_topology), ν, λy:real. h(a(x) + s(x) * y)))",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				ν *Arrow[Set[Real], ExtendedNonnegReal],
				a, s *Arrow[A, Real],
				h *Arrow[Real, Real],
				μProbability, νProbability, aMeasurable, sMeasurable, hBorel Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				cross := arg.TermAs[Set[Prod[A, Real]]]("set_cross(Ω, 𝕌)")
				productField := arg.TermAs[Set[Set[Prod[A, Real]]]](
					"product_sigma(Ω, S, 𝕌, borel_sets(real_topology))")
				first := arg.TermAs[Fun[Prod[A, Real], A]]("λp:prod(A, real). fst(p)")
				second := arg.TermAs[Fun[Prod[A, Real], Real]]("λp:prod(A, real). snd(p)")
				aFirst := arg.TermAs[Fun[Prod[A, Real], Real]]("λp:prod(A, real). a(fst(p))")
				sFirst := arg.TermAs[Fun[Prod[A, Real], Real]]("λp:prod(A, real). s(fst(p))")
				affine := arg.TermAs[Fun[Prod[A, Real], Real]]("λp:prod(A, real). a(fst(p)) + s(fst(p)) * snd(p)")
				fields := arg.Have(
					"both probabilities live on σ-algebras",
					"sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(𝕌, borel_sets(real_topology))",
					By(
						μProbability,
						νProbability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						probability_space.ProbabilityOnDef.At(line, borel, ν),
						measure_space.MeasureOn.At(Ω, S, μ),
						measure_space.MeasureOn.At(line, borel, ν)))
				projections := arg.Have(
					"the product σ-algebra, for which the first coordinate is measurable and the second Borel",
					"sigma_algebra_on(set_cross(Ω, 𝕌), product_sigma(Ω, S, 𝕌, borel_sets(real_topology))) ∧ "+
						"measurable_map(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    Ω, "+
						"    S, "+
						"    λp:prod(A, real). fst(p)) ∧ "+
						"real_measurable(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    λp:prod(A, real). snd(p))",
					By(
						fields,
						measurable_space.ProductSigmaProjections.At(Ω, S, line, borel),
						measurable_function.RealMeasurableDef.At(cross, productField, second)))
				maps := arg.Have(
					"a and s are measurable maps to the Borel line",
					"measurable_map(Ω, S, 𝕌, borel_sets(real_topology), a) ∧ "+
						"measurable_map(Ω, S, 𝕌, borel_sets(real_topology), s)",
					By(
						aMeasurable,
						sMeasurable,
						measurable_function.RealMeasurableDef.At(Ω, S, a),
						measurable_function.RealMeasurableDef.At(Ω, S, s)))
				composed := arg.Have(
					"so are a and s after the first coordinate",
					"measurable_map(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    𝕌, "+
						"    borel_sets(real_topology), "+
						"    a ∘ λp:prod(A, real). fst(p)) ∧ "+
						"measurable_map(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    𝕌, "+
						"    borel_sets(real_topology), "+
						"    s ∘ λp:prod(A, real). fst(p))",
					By(
						projections,
						maps,
						measurable_space.MeasurableCompose.At(cross, productField, Ω, S, line, borel, first, a),
						measurable_space.MeasurableCompose.At(cross, productField, Ω, S, line, borel, first, s)))
				coordinates := arg.Have(
					"(x, y) ↦ a(x) and (x, y) ↦ s(x) are measurable on the product",
					"real_measurable(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    λp:prod(A, real). a(fst(p))) ∧ "+
						"real_measurable(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    λp:prod(A, real). s(fst(p)))",
					By(
						composed,
						functions.ComposeApply.At(a, first),
						functions.ComposeApply.At(s, first),
						measurable_function.RealMeasurableDef.At(cross, productField, aFirst),
						measurable_function.RealMeasurableDef.At(cross, productField, sFirst)))
				affineMeasurable := arg.Have(
					"(x, y) ↦ a(x) + s(x)·y is measurable on the product",
					"real_measurable(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    λp:prod(A, real). a(fst(p)) + s(fst(p)) * snd(p))",
					By(
						projections,
						coordinates,
						measurable_function.RealMeasurableMul.At(cross, productField, sFirst, second),
						measurable_function.RealMeasurableAdd.At(
							cross,
							productField,
							aFirst,
							arg.TermAs[Fun[Prod[A, Real], Real]]("λp:prod(A, real). s(fst(p)) * snd(p)"))))
				integrand := arg.Have(
					"and so is h of it, h being Borel",
					"real_measurable(set_cross(Ω, 𝕌), "+
						"    product_sigma(Ω, S, 𝕌, borel_sets(real_topology)), "+
						"    λp:prod(A, real). h(a(fst(p)) + s(fst(p)) * snd(p)))",
					By(
						hBorel,
						affineMeasurable,
						borel_function.RealMeasurableCompose.At(cross, productField, affine, h)))
				finite := arg.Have(
					"both probabilities are σ-finite",
					"sigma_finite_on(Ω, S, μ) ∧ sigma_finite_on(𝕌, borel_sets(real_topology), ν)",
					By(
						μProbability,
						νProbability,
						probability_space.ProbabilitySigmaFinite.At(Ω, S, μ),
						probability_space.ProbabilitySigmaFinite.At(line, borel, ν)))
				section := arg.Have(
					"integrating out y keeps measurability in x",
					"real_measurable(Ω, "+
						"    S, "+
						"    λx:A. measure_integral(𝕌, borel_sets(real_topology), ν, λy:real. h(a(x) + s(x) * y)))",
					By(
						finite,
						integrand,
						At(sectionIntegralMeasurable,
							Ω,
							S,
							μ,
							line,
							borel,
							ν,
							arg.TermAs[Fun2[A, Real, Real]]("λx:A. λy:real. h(a(x) + s(x) * y)"))))
				expectation := arg.Have(
					"the average is the integral",
					"(λx:A. expectation(𝕌, borel_sets(real_topology), ν, λy:real. h(a(x) + s(x) * y))) = "+
						"λx:A. measure_integral(𝕌, borel_sets(real_topology), ν, λy:real. h(a(x) + s(x) * y))",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.Show(
							"the definition of expectation",
							By(
								probability_space.ExpectationDef.At(
									line, borel, ν, b.TermAs[Fun[Real, Real]]("λy:real. h(a(x) + s(x) * y)"))))
					}))
				arg.Show(
					"both facts together",
					By(section, expectation))
			})
			// Taylor's formula with Lagrange remainder, to order m ≤ 2, for the tower D: Taylor–
			// Lagrange on the interval between a and x, whichever side x lies on.
			taylorExpansion := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀m:num. ∀a x:real.",
				Hypotheses: []string{
					"m ≤ 2",
					"a ≠ x",
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
				},
				Conclusion: "∃z:real. " +
					"    D(0)(x) = " +
					"    Σ_{k∈0 .. m} D(k)(a) * (x - a) ^ k / &factorial(k) + " +
					"    D(m + 1)(z) * (x - a) ^ (m + 1) / &factorial(m + 1)",
			}, func(
				arg *Argument,
				D *Arrow2[Nat, Real, Real],
				m *Expr[Nat],
				a, x *Expr[Real],
				order, distinct, tower Fact,
			) {
				derivatives := arg.Have(
					"D(0), …, D(m) have their successors as derivatives",
					"∀k:num. ∀y:real. k ≤ m ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						b.FixAs[Real]("y")
						below := b.Assume()
						within := b.Have(
							"k ≤ m ≤ 2",
							"k ≤ 2",
							ByArith(below, order))
						b.Show(
							"a derivative of the tower",
							By(within, tower))
					}))
				continuous := arg.Have(
					"so they are continuous on every set",
					"∀A:set(real). ∀k:num. k ≤ m ⇒ real_continuous_on(A, D(k))",
					Derive(func(b *Argument) {
						A := b.FixAs[Set[Real]]("A")
						k := b.FixAs[Nat]("k")
						below := b.Assume()
						b.Show(
							"a differentiable function is continuous",
							By(
								derivatives.At(k),
								below,
								real_derivative.DerivativeContinuousOn.At(
									b.TermAs[Fun[Real, Real]]("D(k)"), b.TermAs[Fun[Real, Real]]("D(k + 1)"), A)))
					}))
				arg.Cases(arg.TermAs[Bool]("a < x"))
				arg.When(
					"x lies above a: Taylor–Lagrange on [a, x]",
					func(b *Argument, above Fact) {
						b.Show(
							"forget where the intermediate point lies",
							By(
								above,
								continuous.At(b.TermAs[Set[Real]]("⟦a, x⟧")),
								derivatives,
								real_taylor.TaylorLagrangeAbove.At(D, m, a, x)))
					})
				arg.Otherwise(
					"x lies below a: Taylor–Lagrange on [x, a]",
					func(b *Argument, notAbove Fact) {
						below := b.Have(
							"x < a",
							"x < a",
							ByArith(notAbove, distinct))
						b.Show(
							"forget where the intermediate point lies",
							By(
								below,
								continuous.At(b.TermAs[Set[Real]]("⟦x, a⟧")),
								derivatives,
								real_taylor.TaylorLagrangeBelow.At(D, m, a, x)))
					})
			})
			// 1! = 1, 2! = 2 and 3! = 6.
			smallFactorials := ctx.Lemma("factorial(1) = 1 ∧ factorial(2) = 2 ∧ factorial(3) = 6",
				func(a *Argument) {
					successors := a.Have(
						"1, 2 and 3 as successors",
						"suc(0) = 1 ∧ suc(1) = 2 ∧ suc(2) = 3",
						ByArith())
					recursion := a.Have(
						"the recursion of the factorial",
						"factorial(0) = 1 ∧ "+
							"factorial(suc(0)) = suc(0) * factorial(0) ∧ "+
							"factorial(suc(1)) = suc(1) * factorial(1) ∧ "+
							"factorial(suc(2)) = suc(2) * factorial(2)",
						By(nat_arith.Factorial))
					a.Show(
						"unwind the recursion three times",
						ByArith(successors, recursion))
				})

			// The Taylor polynomials of orders 1 and 2, written out.
			taylorPolynomials := ctx.Lemma("∀D:(num → real → real). ∀a x:real. "+
				"    Σ_{k∈0 .. 1} D(k)(a) * (x - a) ^ k / &factorial(k) = D(0)(a) + D(1)(a) * (x - a) ∧ "+
				"    Σ_{k∈0 .. 2} D(k)(a) * (x - a) ^ k / &factorial(k) = "+
				"    D(0)(a) + D(1)(a) * (x - a) + D(2)(a) * (x - a) * (x - a) / &2",
				func(arg *Argument, D *Arrow2[Nat, Real, Real], a, x *Expr[Real]) {
					recursion := arg.Have(
						"the Taylor sums of orders 0, 1 and 2 by their recursion",
						"Σ_{k∈0 .. 0} D(k)(a) * (x - a) ^ k / &factorial(k) = D(0)(a) ∧ "+
							"Σ_{k∈0 .. 1} D(k)(a) * (x - a) ^ k / &factorial(k) = "+
							"Σ_{k∈0 .. 0} D(k)(a) * (x - a) ^ k / &factorial(k) + D(1)(a) * ((x - a) ^ 1 / &factorial(1)) ∧ "+
							"Σ_{k∈0 .. 2} D(k)(a) * (x - a) ^ k / &factorial(k) = "+
							"Σ_{k∈0 .. 1} D(k)(a) * (x - a) ^ k / &factorial(k) + D(2)(a) * ((x - a) ^ 2 / &factorial(2))",
						By(
							real_taylor.TaylorSumRecursion.At(D, arg.TermAs[Nat]("0"), x),
							real_taylor.TaylorSumRecursion.At(D, arg.TermAs[Nat]("1"), x)))
					powers := arg.Have(
						"the first two normalized powers",
						"(x - a) ^ 1 / &factorial(1) = x - a ∧ (x - a) ^ 2 / &factorial(2) = (x - a) * (x - a) / &2",
						ByArith(smallFactorials))
					arg.Show(
						"substitute them",
						ByArith(recursion, powers))
				})
			// The second-order Taylor remainder R of D(0) is at most M₂·(x − a)² and at most
			// M₃·|x − a|³/6: R is (D(2)(u) − D(2)(a))·(x − a)²/2 by the first-order expansion and
			// D(3)(w)·(x − a)³/6 by the second-order one.
			taylorRemainderBounds := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀M₂ M₃ a x:real.",
				Hypotheses: []string{
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
				},
				Conclusion: "|D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2| ≤ " +
					"M₂ * (x - a) * (x - a) ∧ " +
					"|D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2| ≤ " +
					"M₃ * |x - a| * (x - a) * (x - a) / &6",
			}, func(
				arg *Argument,
				D *Arrow2[Nat, Real, Real],
				M2, M3, a, x *Expr[Real],
				tower, bounds Fact,
			) {
				arg.Cases(arg.TermAs[Bool]("a = x"))
				arg.When(
					"at x = a the remainder and both bounds vanish",
					func(b *Argument, same Fact) {
						vanish := b.Have(
							"the remainder and both bounds are 0",
							"D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2 = &0 ∧ "+
								"M₂ * (x - a) * (x - a) = &0 ∧ "+
								"M₃ * |x - a| * (x - a) * (x - a) / &6 = &0",
							ByArith(same))
						b.Show(
							"|0| ≤ 0",
							By(vanish, real_sgn_abs.AbsOfZero, real_order_ring.LessEqRefl.At(b.TermAs[Real]("&0"))))
					})
				arg.Otherwise(
					"otherwise expand to orders 1 and 2",
					func(b *Argument, distinct Fact) {
						step := b.TermAs[Real]("x - a")
						_, lowOrder := b.Obtain(
							"the first-order expansion, with remainder D(2)(u)·(x − a)²/2",
							"∃z:real. "+
								"    D(0)(x) = "+
								"    Σ_{k∈0 .. 1} D(k)(a) * (x - a) ^ k / &factorial(k) + D(2)(z) * (x - a) ^ 2 / &factorial(2)",
							By(distinct, tower, At(taylorExpansion, D, b.TermAs[Nat]("1"), a, x)),
							Named("u"))
						_, highOrder := b.Obtain(
							"the second-order expansion, with remainder D(3)(w)·(x − a)³/6",
							"∃z:real. "+
								"    D(0)(x) = "+
								"    Σ_{k∈0 .. 2} D(k)(a) * (x - a) ^ k / &factorial(k) + D(3)(z) * (x - a) ^ 3 / &factorial(3)",
							By(distinct, tower, At(taylorExpansion, D, b.TermAs[Nat]("2"), a, x)),
							Named("w"))
						polynomials := b.Have(
							"the Taylor polynomials of orders 1 and 2",
							"Σ_{k∈0 .. 1} D(k)(a) * (x - a) ^ k / &factorial(k) = D(0)(a) + D(1)(a) * (x - a) ∧ "+
								"Σ_{k∈0 .. 2} D(k)(a) * (x - a) ^ k / &factorial(k) = "+
								"D(0)(a) + D(1)(a) * (x - a) + D(2)(a) * (x - a) * (x - a) / &2",
							By(At(taylorPolynomials, D, a, x)))
						remainder := b.Have(
							"R through the second and through the third derivative",
							"D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2 = "+
								"(D(2)(u) - D(2)(a)) * (x - a) * (x - a) / &2 ∧ "+
								"D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2 = "+
								"D(3)(w) * (x - a) * (x - a) * (x - a) / &6",
							Derive(func(c *Argument) {
								c.Do(Simp(Fwd(real_field.RealDivDef)))
								sums := c.Simplified(polynomials, Fwd(real_field.RealDivDef))
								first := c.Simplified(lowOrder, Fwd(real_field.RealDivDef), Fwd(smallFactorials))
								second := c.Simplified(highOrder, Fwd(real_field.RealDivDef), Fwd(smallFactorials))
								c.Do(RingNf())
								three := c.Have(
									"3 is 2 + 1",
									"2 + 1 = 3",
									ByArith())
								cube := c.Have(
									"(x − a)³ = (x − a)·(x − a)²",
									"(x - a) ^ 3 = (x - a) * ((x - a) * (x - a))",
									By(Normalized, three, real_pow.PowAddOne.At(step, c.TermAs[Nat]("2")), real_pow.PowTwo.At(step)))
								first = c.Simplified(first, Fwd(real_pow.PowTwo))
								second = c.Simplified(second, Fwd(cube))
								c.Show(
									"the two expansions against the polynomials",
									ByArith(first, second, sums))
							}))
						bounded := b.Have(
							"the derivatives at u, a and w obey their bounds",
							"|D(2)(u)| ≤ M₂ ∧ |D(2)(a)| ≤ M₂ ∧ |D(3)(w)| ≤ M₃",
							By(bounds))
						spread := b.Have(
							"D(2)(u) − D(2)(a) lies in [−2M₂, 2M₂]",
							"-(M₂ + M₂) ≤ D(2)(u) - D(2)(a) ∧ D(2)(u) - D(2)(a) ≤ M₂ + M₂",
							ByArith(
								Normalized,
								bounded,
								real_sgn_abs.AbsBounds.At(b.TermAs[Real]("D(2)(u)"), M2),
								real_sgn_abs.AbsBounds.At(b.TermAs[Real]("D(2)(a)"), M2)))
						gap := b.Have(
							"|D(2)(u) − D(2)(a)| ≤ 2M₂",
							"|D(2)(u) - D(2)(a)| ≤ M₂ + M₂",
							By(
								spread,
								real_sgn_abs.AbsBounds.At(b.TermAs[Real]("D(2)(u) - D(2)(a)"), b.TermAs[Real]("M₂ + M₂"))))
						weights := b.Have(
							"1/2, 1/6 and (x − a)² are nonnegative",
							"&0 ≤ real_inv(&2) ∧ &0 ≤ real_inv(&6) ∧ &0 ≤ (x - a) * (x - a)",
							ByArith(
								Normalized,
								real_order_field.InvNonneg.At(b.TermAs[Real]("&2")),
								real_order_field.InvNonneg.At(b.TermAs[Real]("&6")),
								real_order_ring.SquareNonneg.At(step)))
						scaled := b.Have(
							"so are (x − a)²/2 and (x − a)²/6",
							"&0 ≤ real_inv(&2) * (x - a) * (x - a) ∧ &0 ≤ real_inv(&6) * (x - a) * (x - a)",
							ByArith(weights))
						third := b.Have(
							"|D(3)(w)·(x − a)| ≤ M₃·|x − a|",
							"|D(3)(w) * (x - a)| ≤ M₃ * |x - a|",
							By(
								bounded,
								real_sgn_abs.AbsMul.At(b.TermAs[Real]("D(3)(w)"), step),
								real_sgn_abs.AbsNonneg.At(step),
								real_order_ring.LessEqMulRight.At(b.TermAs[Real]("|D(3)(w)|"), M3, b.TermAs[Real]("|x - a|"))))
						factored := b.Have(
							"both remainders factor through (x − a)²",
							"(D(2)(u) - D(2)(a)) * (x - a) * (x - a) / &2 = "+
								"real_inv(&2) * (x - a) * (x - a) * (D(2)(u) - D(2)(a)) ∧ "+
								"D(3)(w) * (x - a) * (x - a) * (x - a) / &6 = "+
								"real_inv(&6) * (x - a) * (x - a) * (D(3)(w) * (x - a))",
							Simp(Fwd(real_field.RealDivDef)),
							ByArith())
						halfSquare := b.TermAs[Real]("real_inv(&2) * (x - a) * (x - a)")
						sixthSquare := b.TermAs[Real]("real_inv(&6) * (x - a) * (x - a)")
						absolute := b.Have(
							"(x − a)²/2 and (x − a)²/6 are their own absolute values",
							"|real_inv(&2) * (x - a) * (x - a)| = real_inv(&2) * (x - a) * (x - a) ∧ "+
								"|real_inv(&6) * (x - a) * (x - a)| = real_inv(&6) * (x - a) * (x - a)",
							By(
								scaled,
								real_sgn_abs.AbsFixedIffNonneg.At(halfSquare),
								real_sgn_abs.AbsFixedIffNonneg.At(sixthSquare)))
						estimates := b.Have(
							"the two estimates of |R|",
							"|D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2| ≤ "+
								"real_inv(&2) * (x - a) * (x - a) * (M₂ + M₂) ∧ "+
								"|D(0)(x) - D(0)(a) - D(1)(a) * (x - a) - D(2)(a) * (x - a) * (x - a) / &2| ≤ "+
								"real_inv(&6) * (x - a) * (x - a) * (M₃ * |x - a|)",
							SplitConj(
								Case(
									"through the second derivative",
									By(
										remainder,
										factored,
										scaled,
										absolute,
										gap,
										real_sgn_abs.AbsMul.At(halfSquare, b.TermAs[Real]("D(2)(u) - D(2)(a)")),
										real_order_ring.LessEqMulLeft.At(
											halfSquare, b.TermAs[Real]("|D(2)(u) - D(2)(a)|"), b.TermAs[Real]("M₂ + M₂")))),
								Case(
									"through the third derivative",
									By(
										remainder,
										factored,
										scaled,
										absolute,
										third,
										real_sgn_abs.AbsMul.At(sixthSquare, b.TermAs[Real]("D(3)(w) * (x - a)")),
										real_order_ring.LessEqMulLeft.At(
											sixthSquare, b.TermAs[Real]("|D(3)(w) * (x - a)|"), b.TermAs[Real]("M₃ * |x - a|"))))))
						half := b.Have(
							"1/2 · 2 = 1",
							"real_inv(&2) * &2 = &1",
							By(real_construction.MulLeftInverse.At(b.TermAs[Real]("&2"))))
						simplified := b.Have(
							"the bounds simplify",
							"real_inv(&2) * (x - a) * (x - a) * (M₂ + M₂) = M₂ * (x - a) * (x - a) ∧ "+
								"real_inv(&6) * (x - a) * (x - a) * (M₃ * |x - a|) = M₃ * |x - a| * (x - a) * (x - a) / &6",
							Simp(Fwd(real_field.RealDivDef)),
							ByArith(half))
						b.Show(
							"the two bounds",
							By(estimates, simplified))
					})
			})
			// The same two bounds at x = a + h.
			taylorRemainderAtShift := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀M₂ M₃ a h:real.",
				Hypotheses: []string{
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
				},
				Conclusion: "|D(0)(a + h) - D(0)(a) - D(1)(a) * h - D(2)(a) * h * h / &2| ≤ M₂ * h * h ∧ " +
					"|D(0)(a + h) - D(0)(a) - D(1)(a) * h - D(2)(a) * h * h / &2| ≤ M₃ * |h| * h * h / &6",
			}, func(
				arg *Argument,
				D *Arrow2[Nat, Real, Real],
				M2, M3, a, h *Expr[Real],
				tower, bounds Fact,
			) {
				shift := arg.Have(
					"the step from a to a + h is h",
					"a + h - a = h",
					ByArith())
				arg.Show(
					"the remainder bounds at x = a + h",
					By(shift, tower, bounds, At(taylorRemainderBounds, D, M2, M3, a, arg.TermAs[Real]("a + h"))))
			})
			// D(0), D(1) and D(2) are differentiable, hence continuous and Borel.
			derivativesBorel := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀k:num.",
				Hypotheses: []string{
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"k ≤ 2",
				},
				Conclusion: "real_measurable(𝕌, borel_sets(real_topology), D(k))",
			}, func(arg *Argument, D *Arrow2[Nat, Real, Real], k *Expr[Nat], tower, within Fact) {
				value := arg.TermAs[Fun[Real, Real]]("D(k)")
				arg.Show(
					"a differentiable function is continuous, and a continuous one Borel",
					By(
						tower,
						within,
						real_derivative.DerivativeContinuousOn.At(
							value, arg.TermAs[Fun[Real, Real]]("D(k + 1)"), arg.TermAs[Set[Real]]("𝕌")),
						borel_function.ContinuousBorelMeasurable.At(value)))
			})
			// An everywhere integrable majorant of |f| makes f integrable and bounds |∫ f|.
			integralDominated := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
				Hypotheses: []string{
					"measure_on(Ω, S, μ)",
					"real_measurable(Ω, S, f)",
					"real_integrable(Ω, S, μ, g)",
					"∀x:A. x ∈ Ω ⇒ |f(x)| ≤ g(x)",
				},
				Conclusion: "real_integrable(Ω, S, μ, f) ∧ " +
					"|measure_integral(Ω, S, μ, f)| ≤ measure_integral(Ω, S, μ, g)",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				f, g *Arrow[A, Real],
				measure, measurable, majorant, dominated Fact,
			) {
				absolute := a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")
				integrable := a.Have(
					"f is dominated by an integrable function",
					"real_integrable(Ω, S, μ, f)",
					By(measurable, majorant, dominated, measure_integral.IntegrableDominated.At(Ω, S, μ, f, g)))
				absoluteIntegrable := a.Have(
					"so is |f|",
					"real_integrable(Ω, S, μ, λx:A. |f(x)|)",
					By(
						measure,
						integrable,
						measure_space.MeasureOn.At(Ω, S, μ),
						measure_integral.IntegrableAbs.At(Ω, S, μ, f)))
				belowAbsolute := a.Have(
					"|∫ f| ≤ ∫ |f|",
					"|measure_integral(Ω, S, μ, f)| ≤ measure_integral(Ω, S, μ, λx:A. |f(x)|)",
					By(
						integrable,
						real_sgn_abs.AbsNonneg,
						measure_integral.IntegralAbsLe.At(Ω, S, μ, f),
						measure_integral.IntegralOfNonneg.At(Ω, S, μ, absolute)))
				a.Show(
					"and ∫ |f| ≤ ∫ g by monotonicity",
					By(
						measure,
						majorant,
						dominated,
						integrable,
						absoluteIntegrable,
						belowAbsolute,
						measure_integral.IntegralMono.At(Ω, S, μ, absolute, g),
						real_construction.LessEqTrans))
			})
			// The integral of c + a·u + b·v under a probability, by linearity.
			affineIntegral := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀u v:(A → real). " +
					"∀c a b:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_integrable(Ω, S, μ, u)",
					"real_integrable(Ω, S, μ, v)",
				},
				Conclusion: "real_integrable(Ω, S, μ, λx:A. c + a * u(x) + b * v(x)) ∧ " +
					"measure_integral(Ω, S, μ, λx:A. c + a * u(x) + b * v(x)) = " +
					"c + a * measure_integral(Ω, S, μ, u) + b * measure_integral(Ω, S, μ, v)",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				u, v *Arrow[A, Real],
				c, a, b *Expr[Real],
				probability, uIntegrable, vIntegrable Fact,
			) {
				constant := arg.TermAs[Fun[A, Real]]("λx:A. c")
				scaledU := arg.TermAs[Fun[A, Real]]("λx:A. a * u(x)")
				measure := arg.Have(
					"a probability is a measure",
					"measure_on(Ω, S, μ)",
					By(probability, probability_space.ProbabilityOnDef.At(Ω, S, μ)))
				constantMean := arg.Have(
					"the constant c has integral c",
					"real_integrable(Ω, S, μ, λx:A. c) ∧ measure_integral(Ω, S, μ, λx:A. c) = c",
					By(
						Normalized,
						probability,
						probability_space.ExpectationConstant.At(Ω, S, μ, c),
						probability_space.ExpectationDef.At(Ω, S, μ, constant)))
				scaled := arg.Have(
					"a·u and b·v are integrable, with the scalars pulled out",
					"real_integrable(Ω, S, μ, λx:A. a * u(x)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. b * v(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. a * u(x)) = a * measure_integral(Ω, S, μ, u) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. b * v(x)) = b * measure_integral(Ω, S, μ, v)",
					By(
						uIntegrable,
						vIntegrable,
						measure,
						measure_integral.IntegrableScale.At(Ω, S, μ, u, a),
						measure_integral.IntegrableScale.At(Ω, S, μ, v, b),
						measure_integral.IntegralScale.At(Ω, S, μ, u, a),
						measure_integral.IntegralScale.At(Ω, S, μ, v, b)))
				partial := arg.Have(
					"c + a·u integrates term by term",
					"real_integrable(Ω, S, μ, λx:A. c + a * u(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. c + a * u(x)) = c + a * measure_integral(Ω, S, μ, u)",
					By(
						measure,
						constantMean,
						scaled,
						measure_integral.IntegrableAdd.At(Ω, S, μ, constant, scaledU),
						measure_integral.IntegralAdd.At(Ω, S, μ, constant, scaledU)))
				front := arg.TermAs[Fun[A, Real]]("λx:A. c + a * u(x)")
				scaledV := arg.TermAs[Fun[A, Real]]("λx:A. b * v(x)")
				arg.Show(
					"and so does the last term",
					By(
						measure,
						partial,
						scaled,
						measure_integral.IntegrableAdd.At(Ω, S, μ, front, scaledV),
						measure_integral.IntegralAdd.At(Ω, S, μ, front, scaledV)))
			})
			// The ν-average of D(0)(a + s·Z) is D(0)(a) + D(2)(a)·s²/2 up to M₃·s³/3, for ν with
			// the standard normal moments: the second-order Taylor polynomial integrates to
			// D(0)(a) + D(2)(a)·s²/2 against the first two moments, and the remainder is at most
			// M₃·s³·|z|³/6, whose integral the third absolute moment bounds.
			gaussianSecondOrder := ctx.Lemma(Statement{
				Binders: "∀ν:(set(real) → extended_nonneg_real). ∀D:(num → real → real). ∀M₂ M₃ a s:real.",
				Hypotheses: []string{
					"probability_on(𝕌, borel_sets(real_topology), ν)",
					"real_integrable(𝕌, borel_sets(real_topology), ν, λz:real. z)",
					"real_integrable(𝕌, borel_sets(real_topology), ν, λz:real. z * z)",
					"real_integrable(𝕌, borel_sets(real_topology), ν, λz:real. |z| * z * z)",
					"measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. z) = &0",
					"measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. z * z) = &1",
					"measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. |z| * z * z) ≤ &2",
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
					"&0 ≤ s",
				},
				Conclusion: "real_integrable(𝕌, borel_sets(real_topology), ν, λz:real. D(0)(a + s * z)) ∧ " +
					"|measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. D(0)(a + s * z)) - " +
					"D(0)(a) - " +
					"D(2)(a) * s * s / &2| ≤ " +
					"&2 * (M₃ * s * s * s / &6)",
				Abbrev: Abbrev{
					{Name: "quadratic", Text: "λz:real. D(0)(a) + D(1)(a) * s * z + D(2)(a) * s * s / &2 * (z * z)"},
					{Name: "remainder", Text: "λz:real. D(0)(a + s * z) + -«quadratic»(z)"},
					{Name: "cubic", Text: "λz:real. M₃ * s * s * s / &6 * (|z| * z * z)"},
				},
			}, func(
				arg *Argument,
				ν *Arrow[Set[Real], ExtendedNonnegReal],
				D *Arrow2[Nat, Real, Real],
				M2, M3, a, s *Expr[Real],
				probability, identityIntegrable, squareIntegrable, cubeIntegrable, mean, second, third, tower, bounds,
				spreadNonnegative Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				identity := arg.TermAs[Fun[Real, Real]]("λz:real. z")
				square := arg.TermAs[Fun[Real, Real]]("λz:real. z * z")
				absoluteCube := arg.TermAs[Fun[Real, Real]]("λz:real. |z| * z * z")
				quadratic := arg.TermAs[Fun[Real, Real]]("«quadratic»")
				remainder := arg.TermAs[Fun[Real, Real]]("«remainder»")
				cubic := arg.TermAs[Fun[Real, Real]]("«cubic»")
				weight := arg.TermAs[Real]("M₃ * s * s * s / &6")
				space := arg.Have(
					"ν is a measure on the Borel σ-algebra",
					"measure_on(𝕌, borel_sets(real_topology), ν) ∧ sigma_algebra_on(𝕌, borel_sets(real_topology))",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(line, borel, ν),
						measure_space.MeasureOn.At(line, borel, ν)))
				quadraticMean := arg.Have(
					"the Taylor polynomial integrates term by term",
					"real_integrable(𝕌, borel_sets(real_topology), ν, «quadratic») ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «quadratic») = "+
						"D(0)(a) + "+
						"D(1)(a) * s * measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. z) + "+
						"D(2)(a) * s * s / &2 * measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. z * z)",
					By(
						probability,
						identityIntegrable,
						squareIntegrable,
						At(affineIntegral,
							line,
							borel,
							ν,
							identity,
							square,
							arg.TermAs[Real]("D(0)(a)"),
							arg.TermAs[Real]("D(1)(a) * s"),
							arg.TermAs[Real]("D(2)(a) * s * s / &2"))))
				shift := arg.Have(
					"z ↦ a + s·z is Borel",
					"real_measurable(𝕌, borel_sets(real_topology), λz:real. a + s * z)",
					By(
						space,
						identityIntegrable,
						measure_integral.RealIntegrableDef.At(line, borel, ν, identity),
						measurable_function.RealMeasurableConst.At(line, borel, a),
						measurable_function.RealMeasurableConst.At(line, borel, s),
						measurable_function.RealMeasurableMul.At(
							line, borel, arg.TermAs[Fun[Real, Real]]("λz:real. s"), identity),
						measurable_function.RealMeasurableAdd.At(
							line,
							borel,
							arg.TermAs[Fun[Real, Real]]("λz:real. a"),
							arg.TermAs[Fun[Real, Real]]("λz:real. s * z"))))
				valueMeasurable := arg.Have(
					"so is D(0) at it, D(0) being differentiable",
					"real_measurable(𝕌, borel_sets(real_topology), λz:real. D(0)(a + s * z))",
					By(
						tower,
						shift,
						At(derivativesBorel, D, arg.TermAs[Nat]("0")),
						borel_function.RealMeasurableCompose.At(
							line,
							borel,
							arg.TermAs[Fun[Real, Real]]("λz:real. a + s * z"),
							arg.TermAs[Fun[Real, Real]]("D(0)")),
						nat_order.ZeroLessEq))
				remainderMeasurable := arg.Have(
					"the Taylor remainder is Borel",
					"real_measurable(𝕌, borel_sets(real_topology), «remainder»)",
					By(
						space,
						valueMeasurable,
						quadraticMean,
						measure_integral.RealIntegrableDef.At(line, borel, ν, quadratic),
						measurable_function.RealMeasurableNeg.At(line, borel, quadratic),
						measurable_function.RealMeasurableAdd.At(
							line,
							borel,
							arg.TermAs[Fun[Real, Real]]("λz:real. D(0)(a + s * z)"),
							arg.TermAs[Fun[Real, Real]]("λz:real. -«quadratic»(z)"))))
				pointwise := arg.Have(
					"pointwise the remainder is at most M₃·s³·|z|³/6",
					"∀z:real. |«remainder»(z)| ≤ «cubic»(z)",
					Derive(func(b *Argument) {
						z := b.FixAs[Real]("z")
						scale := b.Have(
							"|s·z| = s·|z|, s being nonnegative",
							"|s * z| = s * |z|",
							By(
								Normalized,
								spreadNonnegative,
								real_sgn_abs.AbsMul.At(s, z),
								real_sgn_abs.AbsFixedIffNonneg.At(s)))
						rearranged := b.Have(
							"the remainder is the Taylor remainder at a with step s·z, and its bound the cubic one",
							"«remainder»(z) = "+
								"D(0)(a + s * z) - D(0)(a) - D(1)(a) * (s * z) - D(2)(a) * (s * z) * (s * z) / &2 ∧ "+
								"M₃ * |s * z| * (s * z) * (s * z) / &6 = «cubic»(z)",
							Simp(Fwd(real_field.RealDivDef), Fwd(scale)),
							ByArith())
						b.Show(
							"the Taylor remainder bound at the step s·z",
							By(tower, bounds, rearranged, At(taylorRemainderAtShift, D, M2, M3, a, b.TermAs[Real]("s * z"))))
					}))
				cubicMean := arg.Have(
					"the cubic bound integrates to M₃·s³/6 times the third absolute moment",
					"real_integrable(𝕌, borel_sets(real_topology), ν, «cubic») ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «cubic») = "+
						"M₃ * s * s * s / &6 * measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. |z| * z * z)",
					By(
						cubeIntegrable,
						space,
						measure_integral.IntegrableScale.At(line, borel, ν, absoluteCube, weight),
						measure_integral.IntegralScale.At(line, borel, ν, absoluteCube, weight)))
				remainderMean := arg.Have(
					"so the remainder is integrable, with integral at most that of the cubic bound",
					"real_integrable(𝕌, borel_sets(real_topology), ν, «remainder») ∧ "+
						"|measure_integral(𝕌, borel_sets(real_topology), ν, «remainder»)| ≤ "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «cubic»)",
					By(
						space,
						remainderMeasurable,
						cubicMean,
						pointwise,
						At(integralDominated, line, borel, ν, remainder, cubic)))
				recombined := arg.Have(
					"D(0)(a + s·z) is the polynomial plus the remainder",
					"(λz:real. «quadratic»(z) + «remainder»(z)) = λz:real. D(0)(a + s * z)",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[Real]("z")
						b.Show(
							"the polynomial cancels",
							ByArith())
					}))
				valueMean := arg.Have(
					"so D(0)(a + s·z) is integrable, with integral the sum of the two",
					"real_integrable(𝕌, borel_sets(real_topology), ν, λz:real. D(0)(a + s * z)) ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. D(0)(a + s * z)) = "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «quadratic») + "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «remainder»)",
					By(
						space,
						quadraticMean,
						remainderMean,
						recombined,
						measure_integral.IntegrableAdd.At(line, borel, ν, quadratic, remainder),
						measure_integral.IntegralAdd.At(line, borel, ν, quadratic, remainder)))
				polynomialMean := arg.Have(
					"the polynomial integrates to D(0)(a) + D(2)(a)·s²/2, the first moment vanishing",
					"measure_integral(𝕌, borel_sets(real_topology), ν, «quadratic») = D(0)(a) + D(2)(a) * s * s / &2",
					ByArith(mean, second, quadraticMean))
				signs := arg.Have(
					"M₃ bounds |D(3)(0)|, so M₃ and s are nonnegative",
					"&0 ≤ M₃ ∧ &0 ≤ s",
					ByArith(
						bounds.At(arg.TermAs[Real]("&0")),
						real_sgn_abs.AbsNonneg.At(arg.TermAs[Real]("D(3)(&0)")),
						spreadNonnegative))
				products := arg.Have(
					"the products are nonnegative",
					"&0 ≤ M₃ * s ∧ &0 ≤ s * s",
					ByArith(signs))
				weightNonnegative := arg.Have(
					"so is the weight M₃·s³/6",
					"&0 ≤ M₃ * s * s * s / &6",
					ByArith(products))
				weighted := arg.Have(
					"the third absolute moment, weighted",
					"M₃ * s * s * s / &6 * measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. |z| * z * z) ≤ "+
						"M₃ * s * s * s / &6 * &2",
					By(
						third,
						weightNonnegative,
						real_order_ring.LessEqMulLeft.At(
							weight,
							arg.TermAs[Real]("measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. |z| * z * z)"),
							arg.TermAs[Real]("&2"))))
				cubicBound := arg.Have(
					"the cubic bound integrates to at most 2·M₃·s³/6",
					"measure_integral(𝕌, borel_sets(real_topology), ν, «cubic») ≤ &2 * (M₃ * s * s * s / &6)",
					ByArith(weighted, cubicMean))
				difference := arg.Have(
					"the error of the second-order value is the integral of the remainder",
					"measure_integral(𝕌, borel_sets(real_topology), ν, λz:real. D(0)(a + s * z)) - "+
						"D(0)(a) - "+
						"D(2)(a) * s * s / &2 = "+
						"measure_integral(𝕌, borel_sets(real_topology), ν, «remainder»)",
					ByArith(polynomialMean, valueMean))
				arg.Show(
					"chain the bounds",
					By(Normalized, valueMean, remainderMean, cubicBound, difference, real_construction.LessEqTrans))
			})
			// x ↦ x·|x| is strictly increasing.
			signedSquareMonotone := ctx.Lemma(Statement{
				Binders:    "∀x y:real.",
				Hypotheses: []string{"x < y"},
				Conclusion: "x * |x| < y * |y|",
			}, func(arg *Argument, x, y *Expr[Real], below Fact) {
				exponent := arg.Have(
					"the exponent 2 is not 0",
					"2 ≠ 0",
					ByArith())
				two := arg.TermAs[Nat]("2")
				arg.Cases(arg.TermAs[Bool]("&0 ≤ x"))
				arg.When(
					"both are nonnegative, where the square is increasing",
					func(b *Argument, xNonnegative Fact) {
						yNonnegative := b.Have(
							"y ≥ x ≥ 0",
							"&0 ≤ y",
							ByArith(xNonnegative, below))
						b.Show(
							"x·|x| = x² < y² = y·|y|",
							By(
								Normalized,
								xNonnegative,
								yNonnegative,
								below,
								exponent,
								real_sgn_abs.AbsFixedIffNonneg.At(x),
								real_sgn_abs.AbsFixedIffNonneg.At(y),
								real_pow.PowMonoBaseStrict.At(x, y, two),
								real_pow.PowTwo.At(x),
								real_pow.PowTwo.At(y)))
					})
				arg.Otherwise(
					"x is negative",
					func(b *Argument, xNegative Fact) {
						b.Cases(b.TermAs[Bool]("&0 ≤ y"))
						b.When(
							"y is nonnegative, so x·|x| < 0 ≤ y·|y|",
							func(c *Argument, yNonnegative Fact) {
								signs := c.Have(
									"x ≤ 0 < −x and 0 ≤ y",
									"x ≤ &0 ∧ &0 < -x ∧ &0 ≤ y",
									ByArith(xNegative, yNonnegative))
								absolutes := c.Have(
									"|x| = −x and |y| = y",
									"|x| = -x ∧ |y| = y",
									By(signs, real_sgn_abs.AbsNegatedIffNonpos.At(x), real_sgn_abs.AbsFixedIffNonneg.At(y)))
								squares := c.Have(
									"(−x)² > 0 and y² ≥ 0",
									"&0 < -x * -x ∧ &0 ≤ y * y",
									By(
										signs,
										real_order_ring.MulPos.At(c.TermAs[Real]("-x"), c.TermAs[Real]("-x")),
										real_order_ring.SquareNonneg.At(y)))
								c.Show(
									"compare the signs",
									Simp(Fwd(absolutes)),
									ByArith(squares))
							})
						b.Otherwise(
							"both are negative, and the square is increasing in −y < −x",
							func(c *Argument, yNegative Fact) {
								signs := c.Have(
									"x, y ≤ 0 and 0 ≤ −y < −x",
									"x ≤ &0 ∧ y ≤ &0 ∧ &0 ≤ -y ∧ -y < -x",
									ByArith(below, yNegative))
								absolutes := c.Have(
									"|x| = −x and |y| = −y",
									"|x| = -x ∧ |y| = -y",
									By(signs, real_sgn_abs.AbsNegatedIffNonpos.At(x), real_sgn_abs.AbsNegatedIffNonpos.At(y)))
								negX := c.TermAs[Real]("-x")
								negY := c.TermAs[Real]("-y")
								squares := c.Have(
									"(−y)² < (−x)²",
									"-y * -y < -x * -x",
									By(
										Normalized,
										signs,
										exponent,
										real_pow.PowMonoBaseStrict.At(negY, negX, two),
										real_pow.PowTwo.At(negX),
										real_pow.PowTwo.At(negY)))
								c.Show(
									"compare the negatives",
									Simp(Fwd(absolutes)),
									ByArith(squares))
							})
					})
			})

			// √z·|√z| = z for every z: √z has the sign of z and the square |z|.
			sqrtSignedSquare := ctx.Lemma("∀z:real. real_sqrt(z) * |real_sqrt(z)| = z",
				func(arg *Argument, z *Expr[Real]) {
					signed := arg.Have(
						"sgn(z)·|z| = z",
						"sgn(z) * |z| = z",
						Derive(func(b *Argument) {
							b.Cases(b.TermAs[Bool]("z = &0"))
							b.When(
								"at 0 both sides vanish",
								func(c *Argument, zero Fact) {
									c.Show(
										"sgn(0)·|0| = 0",
										Simp(Fwd(zero), Fwd(real_sgn_abs.AbsOfZero), Fwd(real_sgn_abs.SgnOfZero)),
										ByArith())
								})
							b.Otherwise(
								"away from 0, sgn(z) = z/|z|",
								func(c *Argument, nonzero Fact) {
									positive := c.Have(
										"|z| > 0",
										"&0 < |z|",
										By(nonzero, real_sgn_abs.AbsPosIffNonzero.At(z)))
									quotient := c.Have(
										"z/|z|·|z| = z",
										"z / |z| * |z| = z",
										ByArith(positive))
									c.Show(
										"the sign as a quotient",
										By(Normalized, quotient, real_sgn_abs.SgnEqSelfDivAbs.At(z)))
								})
						}))
					root := arg.TermAs[Real]("real_sqrt(z)")
					rewritten := arg.Have(
						"√z·|√z| = sgn(√z)·(√z)²",
						"real_sqrt(z) * |real_sqrt(z)| = sgn(real_sqrt(z)) * real_sqrt(z) ^ 2",
						ByArith(real_sgn_abs.SgnMulSelfIsAbs.At(root), real_pow.PowTwo.At(root)))
					arg.Show(
						"√z has the sign of z and the square |z|",
						By(Normalized, signed, rewritten, real_sqrt.Works.At(z)))
				})

			// t < √z exactly when t·|t| < z.
			belowSqrtIff := ctx.Lemma("∀t z:real. t < real_sqrt(z) ⇔ t * |t| < z",
				func(arg *Argument, t, z *Expr[Real]) {
					root := arg.TermAs[Real]("real_sqrt(z)")
					signedT := arg.TermAs[Real]("t * |t|")
					arg.Show(
						"x ↦ x·|x| is strictly increasing and takes √z to z",
						By(
							At(sqrtSignedSquare, z),
							At(signedSquareMonotone, t, root),
							At(signedSquareMonotone, root, t),
							real_order_ring.LessThanTrichotomy.At(t, root),
							real_order_ring.LessThanAsym.At(signedT, arg.TermAs[Real]("real_sqrt(z) * |real_sqrt(z)|")),
							real_order_ring.LessThanIrrefl.At(signedT)))
				})

			// The square root of a measurable function is measurable: the level t of √g is the
			// level t·|t| of g.
			sqrtMeasurable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀g:(A → real).",
				Hypotheses: []string{
					"sigma_algebra_on(Ω, S)",
					"real_measurable(Ω, S, g)",
				},
				Conclusion: "real_measurable(Ω, S, λx:A. real_sqrt(g(x)))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				g *Arrow[A, Real],
				field, measurable Fact,
			) {
				rays := a.Have(
					"the upper level sets of g are measurable",
					"∀t:real. {x:A | x ∈ Ω ∧ t < g(x)} ∈ S",
					By(field, measurable, measurable_function.RealMeasurableIffRay.At(Ω, S, g)))
				rootRays := a.Have(
					"so are those of √g",
					"∀t:real. {x:A | x ∈ Ω ∧ t < real_sqrt(g(x))} ∈ S",
					Derive(func(b *Argument) {
						t := b.FixAs[Real]("t")
						same := b.Have(
							"the level t of √g is the level t·|t| of g",
							"{x:A | x ∈ Ω ∧ t < real_sqrt(g(x))} = {x:A | x ∈ Ω ∧ t * |t| < g(x)}",
							BySets(At(belowSqrtIff, t)))
						b.Show(
							"a level set of g",
							By(rays.At(b.TermAs[Real]("t * |t|")), same))
					}))
				a.Show(
					"by the level-set criterion",
					By(
						field,
						measurable,
						rootRays,
						measurable_function.RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. real_sqrt(g(x))"))))
			})
			// The standard normal law: its first, second, absolute and third absolute moments,
			// gathered from NormalDistributionMoments, StandardNormalAbsoluteMoment and
			// StandardNormalThirdAbsoluteMoment.
			standardNormalMoments := ctx.Lemma("probability_on(𝕌, "+
				"    borel_sets(real_topology), "+
				"    normal_distribution(&0, &1)) ∧ "+
				"real_measurable(𝕌, borel_sets(real_topology), λy:real. y) ∧ "+
				"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y) ∧ "+
				"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y) ∧ "+
				"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. |y|) ∧ "+
				"real_integrable(𝕌, "+
				"    borel_sets(real_topology), "+
				"    normal_distribution(&0, &1), "+
				"    λy:real. |y| * y * y) ∧ "+
				"«gauss»(λy:real. y) = &0 ∧ "+
				"«gauss»(λy:real. y * y) = &1 ∧ "+
				"&0 ≤ «gauss»(λy:real. |y|) ∧ "+
				"«gauss»(λy:real. |y| * y * y) ≤ &2",
				func(a *Argument) {
					line := a.TermAs[Set[Real]]("𝕌")
					borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					gaussian := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
					identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
					absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y|")
					moments := a.Have(
						"N(0, 1) has mean 0 and variance 1",
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y) ∧ "+
							"«gauss»(λy:real. y) = &0 ∧ "+
							"variance(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y) = &1",
						ByArith(
							Normalized,
							normal_moments.NormalDistributionMoments.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1"))))
					centred := a.Have(
						"with mean 0 the variance is the second moment",
						"(λx:real. (x - «gauss»(λy:real. y)) * (x - «gauss»(λy:real. y))) = λy:real. y * y",
						Funext(),
						Derive(func(b *Argument) {
							b.FixAs[Real]("x")
							b.Show(
								"the mean vanishes",
								ByArith(Normalized, moments))
						}))
					reflexive := a.Have(
						"|y| ≤ |y|",
						"∀x:real. x ∈ 𝕌 ⇒ |x| ≤ |x|",
						ByArith())
					absoluteMean := a.Have(
						"|y| has a nonnegative mean",
						"&0 ≤ «gauss»(λy:real. |y|)",
						ByArith(
							Normalized,
							probability_space.ExpectationDef.At(line, borel, gaussian, absolute),
							measure_integral.IntegralNonneg.At(line, borel, gaussian, absolute)))
					a.Show(
						"y is dominated by the integrable |y|",
						By(
							moments,
							centred,
							reflexive,
							borel_function.RealMeasurableIdentity,
							absoluteMean,
							normal_distribution.NormalDistributionProbability.At(a.TermAs[Real]("&0"), a.TermAs[Real]("&1")),
							normal_moments.StandardNormalAbsoluteMoment,
							normal_moments.StandardNormalThirdAbsoluteMoment,
							probability_space.VarianceDef.At(line, borel, gaussian, identity),
							measure_integral.IntegrableDominated.At(line, borel, gaussian, identity, absolute)))
				})
			// A pointwise bound on f − g − a·u − b·v integrates: the integral of the combination
			// is the combination of the integrals, and it lies between the integrals of ±C.
			affineIntegralBound := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀f g u v:(A → real). " +
					"∀a b C:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_integrable(Ω, S, μ, f)",
					"real_integrable(Ω, S, μ, g)",
					"real_integrable(Ω, S, μ, u)",
					"real_integrable(Ω, S, μ, v)",
					"∀x:A. x ∈ Ω ⇒ |f(x) - g(x) - a * u(x) - b * v(x)| ≤ C",
				},
				Conclusion: "|measure_integral(Ω, S, μ, f) - " +
					"measure_integral(Ω, S, μ, g) - " +
					"a * measure_integral(Ω, S, μ, u) - " +
					"b * measure_integral(Ω, S, μ, v)| ≤ " +
					"C",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				f, g, u, v *Arrow[A, Real],
				a, b, C *Expr[Real],
				probability, fIntegrable, gIntegrable, uIntegrable, vIntegrable, bounded Fact,
			) {
				difference := arg.TermAs[Fun[A, Real]]("λx:A. f(x) - g(x)")
				scaledU := arg.TermAs[Fun[A, Real]]("λx:A. a * u(x)")
				scaledV := arg.TermAs[Fun[A, Real]]("λx:A. b * v(x)")
				partial := arg.TermAs[Fun[A, Real]]("λx:A. f(x) - g(x) - a * u(x)")
				combination := arg.TermAs[Fun[A, Real]]("λx:A. f(x) - g(x) - a * u(x) - b * v(x)")
				lower := arg.TermAs[Fun[A, Real]]("λx:A. -C")
				upper := arg.TermAs[Fun[A, Real]]("λx:A. C")
				measure := arg.Have(
					"a probability is a measure",
					"measure_on(Ω, S, μ)",
					By(probability, probability_space.ProbabilityOnDef.At(Ω, S, μ)))
				scaled := arg.Have(
					"a·u and b·v integrate with the scalars pulled out",
					"real_integrable(Ω, S, μ, λx:A. a * u(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. a * u(x)) = a * measure_integral(Ω, S, μ, u) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. b * v(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. b * v(x)) = b * measure_integral(Ω, S, μ, v)",
					By(
						uIntegrable,
						vIntegrable,
						measure,
						measure_integral.IntegrableScale.At(Ω, S, μ, u, a),
						measure_integral.IntegralScale.At(Ω, S, μ, u, a),
						measure_integral.IntegrableScale.At(Ω, S, μ, v, b),
						measure_integral.IntegralScale.At(Ω, S, μ, v, b)))
				firstDifference := arg.Have(
					"f − g integrates term by term",
					"real_integrable(Ω, S, μ, λx:A. f(x) - g(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x)) = "+
						"measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g)",
					By(
						fIntegrable,
						gIntegrable,
						measure,
						measure_integral.IntegrableSub.At(Ω, S, μ, f, g),
						measure_integral.IntegralSub.At(Ω, S, μ, f, g)))
				secondDifference := arg.Have(
					"so does f − g − a·u",
					"real_integrable(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x)) = "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x)) - measure_integral(Ω, S, μ, λx:A. a * u(x))",
					By(
						scaled,
						firstDifference,
						measure,
						measure_integral.IntegrableSub.At(Ω, S, μ, difference, scaledU),
						measure_integral.IntegralSub.At(Ω, S, μ, difference, scaledU)))
				thirdDifference := arg.Have(
					"and f − g − a·u − b·v",
					"real_integrable(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x) - b * v(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x) - b * v(x)) = "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x)) - "+
						"measure_integral(Ω, S, μ, λx:A. b * v(x))",
					By(
						scaled,
						secondDifference,
						measure,
						measure_integral.IntegrableSub.At(Ω, S, μ, partial, scaledV),
						measure_integral.IntegralSub.At(Ω, S, μ, partial, scaledV)))
				constants := arg.Have(
					"the constants ±C integrate to ±C",
					"real_integrable(Ω, S, μ, λx:A. C) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. -C) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. C) = C ∧ "+
						"measure_integral(Ω, S, μ, λx:A. -C) = -C",
					By(
						Normalized,
						probability,
						probability_space.ExpectationConstant.At(Ω, S, μ, C),
						probability_space.ExpectationConstant.At(Ω, S, μ, arg.TermAs[Real]("-C")),
						probability_space.ExpectationDef.At(Ω, S, μ, upper),
						probability_space.ExpectationDef.At(Ω, S, μ, lower)))
				between := arg.Have(
					"pointwise the combination lies in [−C, C]",
					"∀x:A. x ∈ Ω ⇒ -C ≤ f(x) - g(x) - a * u(x) - b * v(x) ∧ f(x) - g(x) - a * u(x) - b * v(x) ≤ C",
					Derive(func(c *Argument) {
						x := c.FixAs[A]("x")
						inside := c.Assume()
						c.Show(
							"an absolute value bound is a two-sided bound",
							By(
								inside,
								bounded.At(x),
								real_sgn_abs.AbsBounds.At(c.TermAs[Real]("f(x) - g(x) - a * u(x) - b * v(x)"), C)))
					}))
				below := arg.Have(
					"−C lies below the combination",
					"∀x:A. x ∈ Ω ⇒ -C ≤ f(x) - g(x) - a * u(x) - b * v(x)",
					By(between))
				above := arg.Have(
					"and C above it",
					"∀x:A. x ∈ Ω ⇒ f(x) - g(x) - a * u(x) - b * v(x) ≤ C",
					By(between))
				integralBetween := arg.Have(
					"so its integral lies in [−C, C]",
					"-C ≤ measure_integral(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x) - b * v(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. f(x) - g(x) - a * u(x) - b * v(x)) ≤ C",
					By(
						thirdDifference,
						constants,
						below,
						above,
						measure_integral.IntegralMono.At(Ω, S, μ, lower, combination),
						measure_integral.IntegralMono.At(Ω, S, μ, combination, upper)))
				arg.Show(
					"the integral of the combination is the combination of the integrals",
					ByArith(
						Normalized,
						integralBetween,
						scaled,
						firstDifference,
						secondDifference,
						thirdDifference,
						real_sgn_abs.AbsBounds.At(
							arg.TermAs[Real](
								"measure_integral(Ω, S, μ, f) - "+
									"measure_integral(Ω, S, μ, g) - "+
									"a * measure_integral(Ω, S, μ, u) - "+
									"b * measure_integral(Ω, S, μ, v)"),
							C)))
			})
			// Taylor's formula at p + s·y averaged against the normal law, the variance v spent on
			// a second normal variable. Pointwise in y the step h costs the Taylor remainder, at
			// most M₃·ε·h²/6 off the tail ε < |h| and M₂·h² on it; the second normal variable
			// costs the remainder gaussianSecondOrder bounds by M₃·v·√v/3. Averaging in y,
			// affineIntegralBound integrates the pointwise bound.
			gaussianTaylor := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀M₂ M₃ p s v h ε:real.",
				Hypotheses: []string{
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
					"&0 ≤ v",
					"&0 < ε",
					"real_integrable(𝕌, " +
						"    borel_sets(real_topology), " +
						"    normal_distribution(&0, &1), " +
						"    λy:real. D(0)(p + s * y + h))",
					"real_integrable(𝕌, " +
						"    borel_sets(real_topology), " +
						"    normal_distribution(&0, &1), " +
						"    λy:real. «gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)))",
					"real_integrable(𝕌, " +
						"    borel_sets(real_topology), " +
						"    normal_distribution(&0, &1), " +
						"    λy:real. D(1)(p + s * y))",
					"real_integrable(𝕌, " +
						"    borel_sets(real_topology), " +
						"    normal_distribution(&0, &1), " +
						"    λy:real. D(2)(p + s * y))",
				},
				Conclusion: "|«gauss»(λy:real. D(0)(p + s * y + h)) - " +
					"«gauss»(λy:real. «gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z))) - " +
					"h * «gauss»(λy:real. D(1)(p + s * y)) - " +
					"(h * h - v) / &2 * «gauss»(λy:real. D(2)(p + s * y))| ≤ " +
					"«cost»",
				Abbrev: Abbrev{
					{Name: "cost", Text: "M₃ * ε / &6 * h * h + " +
						"M₂ * COND(ε < |h|, h * h, &0) + " +
						"M₃ / &3 * v * real_sqrt(v)"},
				},
			}, func(
				arg *Argument,
				D *Arrow2[Nat, Real, Real],
				M2, M3, p, s, v, h, ε *Expr[Real],
				tower, bounds, vNonnegative, positive, shiftIntegrable, smoothIntegrable, slopeIntegrable,
				curvatureIntegrable Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				gaussian := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				root := arg.TermAs[Real]("real_sqrt(v)")
				shifted := arg.TermAs[Fun[Real, Real]]("λy:real. D(0)(p + s * y + h)")
				smoothed := arg.TermAs[Fun[Real, Real]](
					"λy:real. «gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z))")
				slope := arg.TermAs[Fun[Real, Real]]("λy:real. D(1)(p + s * y)")
				curvature := arg.TermAs[Fun[Real, Real]]("λy:real. D(2)(p + s * y)")
				signs := arg.Have(
					"M₂ and M₃ bound absolute values, ε is positive and v has the root √v",
					"&0 ≤ M₃ ∧ &0 ≤ M₂ ∧ &0 ≤ ε ∧ &0 ≤ real_sqrt(v) ∧ real_sqrt(v) * real_sqrt(v) = v",
					ByArith(
						Normalized,
						positive,
						vNonnegative,
						bounds.At(arg.TermAs[Real]("&0")),
						real_sgn_abs.AbsNonneg.At(arg.TermAs[Real]("D(2)(&0)")),
						real_sgn_abs.AbsNonneg.At(arg.TermAs[Real]("D(3)(&0)")),
						real_sqrt.SqrtNonneg.At(v),
						real_sqrt.SqrtPowTwo.At(v)))
				moments := arg.Have(
					"the standard normal moments, as integrals",
					"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λz:real. z) ∧ "+
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λz:real. z * z) ∧ "+
						"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λz:real. |z| * z * z) ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λz:real. z) = &0 ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λz:real. z * z) = "+
						"&1 ∧ "+
						"measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λz:real. |z| * z * z) ≤ "+
						"&2",
					By(
						standardNormalMoments,
						probability_space.ExpectationDef.At(
							line, borel, gaussian, arg.TermAs[Fun[Real, Real]]("λz:real. z")),
						probability_space.ExpectationDef.At(
							line, borel, gaussian, arg.TermAs[Fun[Real, Real]]("λz:real. z * z")),
						probability_space.ExpectationDef.At(
							line, borel, gaussian, arg.TermAs[Fun[Real, Real]]("λz:real. |z| * z * z"))))
				pointwise := arg.Have(
					"pointwise in y the step costs at most «cost»",
					Statement{
						Binders: "∀y:real.",
						Hypotheses: []string{
							"y ∈ 𝕌",
						},
						Conclusion: "|D(0)(p + s * y + h) - " +
							"«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - " +
							"h * D(1)(p + s * y) - " +
							"(h * h - v) / &2 * D(2)(p + s * y)| ≤ " +
							"«cost»",
					},
					Derive(func(b *Argument) {
						b.FixAs[Real]("y")
						b.Assume()
						point := b.TermAs[Real]("p + s * y")
						remainder := b.Have(
							"the Taylor remainder bounds at p + s·y with step h",
							"|D(0)(p + s * y + h) - D(0)(p + s * y) - D(1)(p + s * y) * h - D(2)(p + s * y) * h * h / &2| ≤ "+
								"M₂ * h * h ∧ "+
								"|D(0)(p + s * y + h) - D(0)(p + s * y) - D(1)(p + s * y) * h - D(2)(p + s * y) * h * h / &2| ≤ "+
								"M₃ * |h| * h * h / &6",
							By(tower, bounds, At(taylorRemainderAtShift, D, M2, M3, point, h)))
						cubeWeight := b.Have(
							"M₃·h²/6 is nonnegative",
							"&0 ≤ M₃ * h * h / &6",
							ByArith(
								Normalized,
								signs,
								real_order_ring.SquareNonneg.At(h),
								real_order_ring.LessEqMulRight.At(b.TermAs[Real]("&0"), M3, b.TermAs[Real]("h * h"))))
						step := b.Have(
							"the step costs at most M₃·ε·h²/6, plus M₂·h² on the tail",
							"|D(0)(p + s * y + h) - D(0)(p + s * y) - D(1)(p + s * y) * h - D(2)(p + s * y) * h * h / &2| ≤ "+
								"M₃ * ε / &6 * h * h + M₂ * COND(ε < |h|, h * h, &0)",
							Derive(func(c *Argument) {
								cubic := c.TermAs[Real]("M₃ * h * h / &6")
								c.Cases(c.TermAs[Bool]("ε < |h|"))
								c.When(
									"on the tail the second-derivative bound M₂·h² serves",
									func(d *Argument, large Fact) {
										d.Show(
											"M₂·h² plus a nonnegative term",
											ByArith(
												Normalized,
												large,
												signs,
												cubeWeight,
												remainder,
												real_order_ring.LessEqMulRight.At(d.TermAs[Real]("&0"), ε, cubic)))
									})
								c.Otherwise(
									"off the tail |h| ≤ ε turns the third-derivative bound into M₃·ε·h²/6",
									func(d *Argument, small Fact) {
										d.Show(
											"M₃·|h|·h²/6 ≤ M₃·ε·h²/6",
											ByArith(
												Normalized,
												small,
												cubeWeight,
												remainder,
												real_order_ring.NotLessThan.At(ε, d.TermAs[Real]("|h|")),
												real_order_ring.LessEqMulRight.At(d.TermAs[Real]("|h|"), ε, cubic)))
									})
							}))
						secondOrder := b.Have(
							"the normal average at p + s·y with spread √v, to second order",
							"|measure_integral(𝕌, "+
								"    borel_sets(real_topology), "+
								"    normal_distribution(&0, &1), "+
								"    λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - "+
								"D(0)(p + s * y) - "+
								"D(2)(p + s * y) * real_sqrt(v) * real_sqrt(v) / &2| ≤ "+
								"&2 * (M₃ * real_sqrt(v) * real_sqrt(v) * real_sqrt(v) / &6)",
							By(moments, tower, bounds, signs, At(gaussianSecondOrder, gaussian, D, M2, M3, point, root)))
						spent := b.Have(
							"the variance v costs at most M₃·v·√v/3",
							"|«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - "+
								"D(0)(p + s * y) - "+
								"D(2)(p + s * y) * v / &2| ≤ "+
								"M₃ / &3 * v * real_sqrt(v)",
							Derive(func(c *Argument) {
								regrouped := c.Have(
									"regroup the factors of √v",
									"D(2)(p + s * y) * real_sqrt(v) * real_sqrt(v) / &2 = "+
										"D(2)(p + s * y) * (real_sqrt(v) * real_sqrt(v)) / &2 ∧ "+
										"&2 * (M₃ * real_sqrt(v) * real_sqrt(v) * real_sqrt(v) / &6) = "+
										"M₃ / &3 * (real_sqrt(v) * real_sqrt(v)) * real_sqrt(v)",
									ByArith(Normalized))
								squared := c.Have(
									"and square √v back to v",
									"D(2)(p + s * y) * real_sqrt(v) * real_sqrt(v) / &2 = D(2)(p + s * y) * v / &2 ∧ "+
										"&2 * (M₃ * real_sqrt(v) * real_sqrt(v) * real_sqrt(v) / &6) = M₃ / &3 * v * real_sqrt(v)",
									By(regrouped, signs))
								c.Show(
									"the second-order estimate, as an average",
									By(
										secondOrder,
										squared,
										probability_space.ExpectationDef.At(
											line,
											borel,
											gaussian,
											c.TermAs[Fun[Real, Real]]("λz:real. D(0)(p + s * y + real_sqrt(v) * z)"))))
							}))
						rearranged := b.Have(
							"the error is the step's Taylor remainder minus the smoothing remainder",
							"D(0)(p + s * y + h) - "+
								"«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - "+
								"h * D(1)(p + s * y) - "+
								"(h * h - v) / &2 * D(2)(p + s * y) = "+
								"D(0)(p + s * y + h) - "+
								"D(0)(p + s * y) - "+
								"D(1)(p + s * y) * h - "+
								"D(2)(p + s * y) * h * h / &2 - "+
								"(«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - "+
								"    D(0)(p + s * y) - "+
								"    D(2)(p + s * y) * v / &2)",
							ByArith(Normalized))
						stepRemainder := b.TermAs[Real](
							"D(0)(p + s * y + h) - D(0)(p + s * y) - D(1)(p + s * y) * h - D(2)(p + s * y) * h * h / &2")
						smoothingRemainder := b.TermAs[Real](
							"«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - D(0)(p + s * y) - D(2)(p + s * y) * v / &2")
						combined := b.Have(
							"the two costs add",
							"|D(0)(p + s * y + h) - "+
								"D(0)(p + s * y) - "+
								"D(1)(p + s * y) * h - "+
								"D(2)(p + s * y) * h * h / &2 - "+
								"(«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - D(0)(p + s * y) - D(2)(p + s * y) * v / &2)| ≤ "+
								"«cost»",
							ByArith(
								Normalized,
								step,
								spent,
								real_sgn_abs.AbsBounds.At(
									stepRemainder, b.TermAs[Real]("M₃ * ε / &6 * h * h + M₂ * COND(ε < |h|, h * h, &0)")),
								real_sgn_abs.AbsBounds.At(smoothingRemainder, b.TermAs[Real]("M₃ / &3 * v * real_sqrt(v)")),
								real_sgn_abs.AbsBounds.At(
									b.TermAs[Real](
										"D(0)(p + s * y + h) - "+
											"D(0)(p + s * y) - "+
											"D(1)(p + s * y) * h - "+
											"D(2)(p + s * y) * h * h / &2 - "+
											"(«gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z)) - "+
											"    D(0)(p + s * y) - "+
											"    D(2)(p + s * y) * v / &2)"),
									b.TermAs[Real]("«cost»"))))
						b.Show(
							"rearrange",
							By(rearranged, combined))
					}))
				averaged := arg.Have(
					"averaging in y integrates the pointwise bound",
					"|measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. D(0)(p + s * y + h)) - "+
						"measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. «gauss»(λz:real. D(0)(p + s * y + real_sqrt(v) * z))) - "+
						"h * "+
						"measure_integral(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. D(1)(p + s * y)) - "+
						"(h * h - v) / "+
						"&2 * "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. D(2)(p + s * y))| ≤ "+
						"«cost»",
					By(
						shiftIntegrable,
						smoothIntegrable,
						slopeIntegrable,
						curvatureIntegrable,
						pointwise,
						standardNormalMoments,
						At(affineIntegralBound,
							line,
							borel,
							gaussian,
							shifted,
							smoothed,
							slope,
							curvature,
							h,
							arg.TermAs[Real]("(h * h - v) / &2"),
							arg.TermAs[Real]("«cost»"))))
				arg.Show(
					"the integrals are the normal averages",
					By(
						averaged,
						probability_space.ExpectationDef.At(line, borel, gaussian, shifted),
						probability_space.ExpectationDef.At(line, borel, gaussian, smoothed),
						probability_space.ExpectationDef.At(line, borel, gaussian, slope),
						probability_space.ExpectationDef.At(line, borel, gaussian, curvature)))
			})
			// A Borel f of at most quadratic growth is integrable at a + s·Y for Y standard normal,
			// with the bound read off its growth: |f(a + s·y)| is at most p + q·|a| + 2r·a² +
			// q·|s|·|y| + 2r·s²·y², whose normal average the first two moments give.
			quadraticGrowthAverage := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀a s p q r:real.",
				Hypotheses: []string{
					"real_measurable(𝕌, borel_sets(real_topology), f)",
					"&0 ≤ p",
					"&0 ≤ q",
					"&0 ≤ r",
					"∀x:real. |f(x)| ≤ p + q * |x| + r * x * x",
				},
				Conclusion: "real_integrable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    normal_distribution(&0, &1), " +
					"    λy:real. f(a + s * y)) ∧ " +
					"|«gauss»(λy:real. f(a + s * y))| ≤ " +
					"p + q * |a| + &2 * r * a * a + q * |s| * «gauss»(λy:real. |y|) + &2 * r * s * s",
				Abbrev: Abbrev{
					{Name: "majorant", Text: "λy:real. " +
						"    p + q * |a| + &2 * r * a * a + q * |s| * |y| + &2 * r * s * s * y * y"},
				},
			}, func(
				arg *Argument,
				f *Arrow[Real, Real],
				a, s, p, q, r *Expr[Real],
				fBorel, pNonnegative, qNonnegative, rNonnegative, growth Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				shift := arg.TermAs[Fun[Real, Real]]("λy:real. a + s * y")
				composed := arg.TermAs[Fun[Real, Real]]("λy:real. f(a + s * y)")
				absolute := arg.TermAs[Fun[Real, Real]]("λy:real. |y|")
				law := arg.Have(
					"N(0, 1) on the Borel σ-algebra, with y² and |y| integrable and y² of mean 1",
					"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"measure_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"sigma_algebra_on(𝕌, borel_sets(real_topology)) ∧ "+
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. y) ∧ "+
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y) ∧ "+
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. |y|) ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y) = &1",
					By(
						standardNormalMoments,
						probability_space.ProbabilityOnDef.At(line, borel, standard),
						borel_function.LineBorelSigmaAlgebra,
						probability_space.ExpectationDef.At(
							line, borel, standard, arg.TermAs[Fun[Real, Real]]("λy:real. y * y"))))
				shiftMeasurable := arg.Have(
					"y ↦ a + s·y is Borel",
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. a + s * y)",
					By(
						law,
						measurable_function.RealMeasurableConst.At(line, borel, a),
						measurable_function.RealMeasurableScale.At(
							line, borel, arg.TermAs[Fun[Real, Real]]("λy:real. y"), s),
						measurable_function.RealMeasurableAdd.At(
							line,
							borel,
							arg.TermAs[Fun[Real, Real]]("λy:real. a"),
							arg.TermAs[Fun[Real, Real]]("λy:real. s * y"))))
				measurable := arg.Have(
					"so is f at it",
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. f(a + s * y))",
					By(fBorel, shiftMeasurable, borel_function.RealMeasurableCompose.At(line, borel, shift, f)))
				majorantMean := arg.Have(
					"the majorant integrates against the first two absolute moments",
					"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), «majorant») ∧ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), «majorant») = "+
						"p + q * |a| + &2 * r * a * a + q * |s| * «gauss»(λy:real. |y|) + &2 * r * s * s",
					Derive(func(b *Argument) {
						linear := b.Have(
							"the majorant grouped as c + a'·|y| + b'·y², by linearity",
							"real_integrable(𝕌, "+
								"    borel_sets(real_topology), "+
								"    normal_distribution(&0, &1), "+
								"    λy:real. p + q * |a| + &2 * r * a * a + q * |s| * |y| + &2 * r * s * s * (y * y)) ∧ "+
								"measure_integral(𝕌, "+
								"    borel_sets(real_topology), "+
								"    normal_distribution(&0, &1), "+
								"    λy:real. p + q * |a| + &2 * r * a * a + q * |s| * |y| + &2 * r * s * s * (y * y)) = "+
								"p + q * |a| + &2 * r * a * a + q * |s| * «gauss»(λy:real. |y|) + &2 * r * s * s",
							By(
								law,
								At(affineIntegral,
									line,
									borel,
									standard,
									absolute,
									b.TermAs[Fun[Real, Real]]("λy:real. y * y"),
									b.TermAs[Real]("p + q * |a| + &2 * r * a * a"),
									b.TermAs[Real]("q * |s|"),
									b.TermAs[Real]("&2 * r * s * s")),
								probability_space.ExpectationDef.At(line, borel, standard, absolute),
								real_ring.MulRightId.At(b.TermAs[Real]("&2 * r * s * s"))))
						regrouped := b.Have(
							"which is the majorant",
							"«majorant» = λy:real. p + q * |a| + &2 * r * a * a + q * |s| * |y| + &2 * r * s * s * (y * y)",
							Funext(),
							ByArith(Normalized))
						b.Show(
							"as written",
							By(regrouped, linear))
					}))
				dominated := arg.Have(
					"pointwise |f(a + s·y)| is at most the majorant",
					"∀y:real. y ∈ 𝕌 ⇒ |f(a + s * y)| ≤ «majorant»(y)",
					Derive(func(b *Argument) {
						y := b.FixAs[Real]("y")
						b.Assume()
						point := b.TermAs[Real]("a + s * y")
						spread := b.Have(
							"|a + s·y| ≤ |a| + |s|·|y| and (a + s·y)² ≤ 2a² + 2s²·y²",
							"|a + s * y| ≤ |a| + |s| * |y| ∧ (a + s * y) * (a + s * y) ≤ &2 * a * a + &2 * s * s * y * y",
							ByArith(
								Normalized,
								real_sgn_abs.AbsTriangle.At(a, b.TermAs[Real]("s * y")),
								real_sgn_abs.AbsMul.At(s, y),
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("a - s * y"))))
						weighted := b.Have(
							"weighted by q and r",
							"q * |a + s * y| ≤ q * (|a| + |s| * |y|) ∧ "+
								"r * ((a + s * y) * (a + s * y)) ≤ r * (&2 * a * a + &2 * s * s * y * y)",
							By(
								qNonnegative,
								rNonnegative,
								spread,
								real_order_ring.LessEqMulLeft.At(
									q, b.TermAs[Real]("|a + s * y|"), b.TermAs[Real]("|a| + |s| * |y|")),
								real_order_ring.LessEqMulLeft.At(
									r,
									b.TermAs[Real]("(a + s * y) * (a + s * y)"),
									b.TermAs[Real]("&2 * a * a + &2 * s * s * y * y"))))
						b.Show(
							"the growth bound at a + s·y",
							ByArith(Normalized, growth.At(point), weighted))
					}))
				bounded := arg.Have(
					"so f(a + s·y) is integrable, with integral at most that of the majorant",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. f(a + s * y)) ∧ "+
						"|measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. f(a + s * y))| ≤ "+
						"measure_integral(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), «majorant»)",
					By(
						law,
						measurable,
						majorantMean,
						dominated,
						At(integralDominated, line, borel, standard, composed, arg.TermAs[Fun[Real, Real]]("«majorant»"))))
				arg.Show(
					"the integral is the normal average",
					By(bounded, majorantMean, probability_space.ExpectationDef.At(line, borel, standard, composed)))
			})
			// x ↦ the normal average of f(a(x) + s(x)·y) is integrable for f of quadratic growth
			// and a square-integrable: where s(x)² ≤ c, quadraticGrowthAverage bounds the average
			// by K + 2K·c + 2K·a(x)², an integrable function.
			smoothedIntegrable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀a s:(A → real). " +
					"∀f:(real → real). " +
					"∀K c:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_measurable(Ω, S, a)",
					"real_measurable(Ω, S, s)",
					"real_measurable(𝕌, borel_sets(real_topology), f)",
					"real_integrable(Ω, S, μ, λx:A. a(x) * a(x))",
					"&0 ≤ K",
					"measure_ae(Ω, S, μ, λx:A. s(x) * s(x) ≤ c)",
					"∀z:real. |f(z)| ≤ K * (&1 + z * z)",
				},
				Conclusion: "real_integrable(Ω, S, μ, λx:A. «gauss»(λy:real. f(a(x) + s(x) * y)))",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				a, s *Arrow[A, Real],
				f *Arrow[Real, Real],
				K, c *Expr[Real],
				probability, aMeasurable, sMeasurable, fBorel, aSquare, kNonnegative, spreadBound, growth Fact,
			) {
				standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				average := arg.TermAs[Fun[A, Real]]("λx:A. «gauss»(λy:real. f(a(x) + s(x) * y))")
				majorant := arg.TermAs[Fun[A, Real]]("λx:A. K + &2 * K * c + &2 * K * (a(x) * a(x))")
				measurable := arg.Have(
					"the average is measurable, and μ a measure",
					"real_measurable(Ω, S, λx:A. «gauss»(λy:real. f(a(x) + s(x) * y))) ∧ measure_on(Ω, S, μ)",
					By(
						probability,
						aMeasurable,
						sMeasurable,
						fBorel,
						standardNormalMoments,
						At(gaussianAverageMeasurable, Ω, S, μ, standard, a, s, f),
						probability_space.ProbabilityOnDef.At(Ω, S, μ)))
				majorantIntegrable := arg.Have(
					"K + 2K·c + 2K·a² is integrable",
					"real_integrable(Ω, S, μ, λx:A. K + &2 * K * c + &2 * K * (a(x) * a(x)))",
					By(
						probability,
						aSquare,
						measurable,
						probability_space.ExpectationConstant.At(Ω, S, μ, arg.TermAs[Real]("K + &2 * K * c")),
						measure_integral.IntegrableScale.At(
							Ω, S, μ, arg.TermAs[Fun[A, Real]]("λx:A. a(x) * a(x)"), arg.TermAs[Real]("&2 * K")),
						measure_integral.IntegrableAdd.At(
							Ω,
							S,
							μ,
							arg.TermAs[Fun[A, Real]]("λx:A. K + &2 * K * c"),
							arg.TermAs[Fun[A, Real]]("λx:A. &2 * K * (a(x) * a(x))"))))
				growthForm := arg.Have(
					"the growth as p + q·|y| + r·y², with p = r = K and q = 0",
					"∀y:real. |f(y)| ≤ K + &0 * |y| + K * y * y",
					Derive(func(b *Argument) {
						y := b.FixAs[Real]("y")
						b.Show(
							"expand K·(1 + y²)",
							ByArith(Normalized, growth.At(y)))
					}))
				pointwise := arg.Have(
					"where s(x)² ≤ c the average is at most the majorant",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ Ω", "s(x) * s(x) ≤ c"},
						Conclusion: "|«gauss»(λy:real. f(a(x) + s(x) * y))| ≤ K + &2 * K * c + &2 * K * (a(x) * a(x))",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						spreadAt := b.Assume()
						averageBound := b.Have(
							"the growth bound averaged at a(x) + s(x)·Y",
							"|«gauss»(λy:real. f(a(x) + s(x) * y))| ≤ "+
								"K + "+
								"&0 * |a(x)| + "+
								"&2 * K * a(x) * a(x) + "+
								"&0 * |s(x)| * «gauss»(λy:real. |y|) + "+
								"&2 * K * s(x) * s(x)",
							By(
								fBorel,
								kNonnegative,
								growthForm,
								At(quadraticGrowthAverage, f, a.Apply(x), s.Apply(x), K, b.TermAs[Real]("&0"), K)))
						spreadWeighted := b.Have(
							"2K·s(x)² ≤ 2K·c",
							"&2 * K * (s(x) * s(x)) ≤ &2 * K * c",
							ByArith(
								Normalized,
								kNonnegative,
								spreadAt,
								real_order_ring.LessEqMulLeft.At(b.TermAs[Real]("&2 * K"), b.TermAs[Real]("s(x) * s(x)"), c)))
						b.Show(
							"combine the two",
							ByArith(Normalized, averageBound, spreadWeighted))
					}))
				almostSurely := arg.Have(
					"so the bound holds almost everywhere",
					"measure_ae(Ω, "+
						"    S, "+
						"    μ, "+
						"    λx:A. |«gauss»(λy:real. f(a(x) + s(x) * y))| ≤ K + &2 * K * c + &2 * K * (a(x) * a(x)))",
					By(
						spreadBound,
						pointwise,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							arg.TermAs[Set[A]]("λx:A. s(x) * s(x) ≤ c"),
							arg.TermAs[Set[A]](
								"λx:A. |«gauss»(λy:real. f(a(x) + s(x) * y))| ≤ K + &2 * K * c + &2 * K * (a(x) * a(x))"))))
				arg.Show(
					"a measurable function dominated by an integrable one",
					By(
						measurable,
						majorantIntegrable,
						almostSurely,
						measure_integral.AEBoundedIntegral.At(Ω, S, μ, average, majorant)))
			})
			// The same average is square-integrable for f of linear growth: where s(x)² ≤ c,
			// quadraticGrowthAverage bounds |average(x)| by L + K·|a(x)|, L = K + K·(1 + c)·E|Y|,
			// and its square by 2L² + 2K²·a(x)², an integrable function.
			smoothedSquareIntegrable := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀a s:(A → real). " +
					"∀f:(real → real). " +
					"∀K c:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_measurable(Ω, S, a)",
					"real_measurable(Ω, S, s)",
					"real_measurable(𝕌, borel_sets(real_topology), f)",
					"real_integrable(Ω, S, μ, λx:A. a(x) * a(x))",
					"&0 ≤ K",
					"measure_ae(Ω, S, μ, λx:A. s(x) * s(x) ≤ c)",
					"∀z:real. |f(z)| ≤ K * (&1 + |z|)",
				},
				Conclusion: "real_integrable(Ω, " +
					"    S, " +
					"    μ, " +
					"    λx:A. «gauss»(λy:real. f(a(x) + s(x) * y)) * «gauss»(λy:real. f(a(x) + s(x) * y)))",
				Abbrev: Abbrev{
					{Name: "average", Text: "λx:A. «gauss»(λy:real. f(a(x) + s(x) * y))"},
					{Name: "level", Text: "K + K * (&1 + c) * «gauss»(λy:real. |y|)"},
					{Name: "majorant", Text: "λx:A. &2 * «level» * «level» + &2 * K * K * (a(x) * a(x))"},
				},
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				a, s *Arrow[A, Real],
				f *Arrow[Real, Real],
				K, c *Expr[Real],
				probability, aMeasurable, sMeasurable, fBorel, aSquare, kNonnegative, spreadBound, growth Fact,
			) {
				standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				average := arg.TermAs[Fun[A, Real]]("«average»")
				squared := arg.TermAs[Fun[A, Real]]("λx:A. «average»(x) * «average»(x)")
				majorant := arg.TermAs[Fun[A, Real]]("«majorant»")
				measurable := arg.Have(
					"the average and its square are measurable, and E|Y| ≥ 0",
					"real_measurable(Ω, S, «average») ∧ "+
						"real_measurable(Ω, S, λx:A. «average»(x) * «average»(x)) ∧ "+
						"measure_on(Ω, S, μ) ∧ "+
						"&0 ≤ «gauss»(λy:real. |y|)",
					By(
						probability,
						aMeasurable,
						sMeasurable,
						fBorel,
						standardNormalMoments,
						At(gaussianAverageMeasurable, Ω, S, μ, standard, a, s, f),
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ),
						measurable_function.RealMeasurableMul.At(Ω, S, average, average)))
				majorantIntegrable := arg.Have(
					"2L² + 2K²·a² is integrable",
					"real_integrable(Ω, S, μ, «majorant»)",
					By(
						probability,
						aSquare,
						measurable,
						probability_space.ExpectationConstant.At(Ω, S, μ, arg.TermAs[Real]("&2 * «level» * «level»")),
						measure_integral.IntegrableScale.At(
							Ω, S, μ, arg.TermAs[Fun[A, Real]]("λx:A. a(x) * a(x)"), arg.TermAs[Real]("&2 * K * K")),
						measure_integral.IntegrableAdd.At(
							Ω,
							S,
							μ,
							arg.TermAs[Fun[A, Real]]("λx:A. &2 * «level» * «level»"),
							arg.TermAs[Fun[A, Real]]("λx:A. &2 * K * K * (a(x) * a(x))"))))
				growthForm := arg.Have(
					"the growth as p + q·|z| + r·z², with p = q = K and r = 0",
					"∀z:real. |f(z)| ≤ K + K * |z| + &0 * z * z",
					Derive(func(b *Argument) {
						z := b.FixAs[Real]("z")
						b.Show(
							"expand K·(1 + |z|)",
							ByArith(Normalized, growth.At(z)))
					}))
				pointwise := arg.Have(
					"where s(x)² ≤ c the square of the average is at most the majorant",
					"∀x:A. x ∈ Ω ∧ s(x) * s(x) ≤ c ⇒ |«average»(x) * «average»(x)| ≤ «majorant»(x)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						spreadAt := b.Assume()
						value := b.TermAs[Real]("«average»(x)")
						bound := b.TermAs[Real]("«level» + K * |a(x)|")
						averageBound := b.Have(
							"the growth bound averaged at a(x) + s(x)·Y",
							"|«average»(x)| ≤ "+
								"K + "+
								"K * |a(x)| + "+
								"&2 * &0 * a(x) * a(x) + "+
								"K * |s(x)| * «gauss»(λy:real. |y|) + "+
								"&2 * &0 * s(x) * s(x)",
							By(
								fBorel,
								kNonnegative,
								growthForm,
								At(quadraticGrowthAverage, f, a.Apply(x), s.Apply(x), K, K, b.TermAs[Real]("&0"))))
						spread := b.Have(
							"|s(x)| ≤ 1 + c, as s(x)² ≤ c",
							"|s(x)| ≤ &1 + c",
							ByArith(
								Normalized,
								spreadAt,
								real_sgn_abs.AbsBounds.At(s.Apply(x), b.TermAs[Real]("&1 + c")),
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("s(x) - &1")),
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("s(x) + &1")),
								real_order_ring.SquareNonneg.At(s.Apply(x))))
						spreadWeighted := b.Have(
							"so K·|s(x)|·E|Y| ≤ K·(1 + c)·E|Y|",
							"K * |s(x)| * «gauss»(λy:real. |y|) ≤ K * (&1 + c) * «gauss»(λy:real. |y|)",
							By(
								kNonnegative,
								spread,
								measurable,
								real_order_ring.LessEqMulLeft.At(K, b.TermAs[Real]("|s(x)|"), b.TermAs[Real]("&1 + c")),
								real_order_ring.LessEqMulRight.At(
									b.TermAs[Real]("K * |s(x)|"),
									b.TermAs[Real]("K * (&1 + c)"),
									b.TermAs[Real]("«gauss»(λy:real. |y|)"))))
						linear := b.Have(
							"|average(x)| ≤ L + K·|a(x)|",
							"|«average»(x)| ≤ «level» + K * |a(x)|",
							ByArith(Normalized, averageBound, spreadWeighted))
						boundNonnegative := b.Have(
							"L + K·|a(x)| is nonnegative, its own absolute value",
							"&0 ≤ «level» + K * |a(x)| ∧ |«level» + K * |a(x)|| = «level» + K * |a(x)|",
							ByArith(
								Normalized,
								linear,
								real_sgn_abs.AbsNonneg.At(value),
								real_sgn_abs.AbsFixedIffNonneg.At(bound)))
						square := b.Have(
							"so average(x)² ≤ (L + K·|a(x)|)²",
							"«average»(x) * «average»(x) ≤ («level» + K * |a(x)|) * («level» + K * |a(x)|)",
							By(
								linear,
								boundNonnegative,
								real_pow.AbsLessEqIffPowTwoLessEq.At(value, bound),
								real_pow.PowTwo.At(value),
								real_pow.PowTwo.At(bound)))
						absoluteSquare := b.Have(
							"|a(x)|² = a(x)²",
							"|a(x)| * |a(x)| = a(x) * a(x)",
							By(
								Normalized,
								real_pow.SquareOfAbs.At(a.Apply(x)),
								real_pow.PowTwo.At(a.Apply(x)),
								real_pow.PowTwo.At(b.TermAs[Real]("|a(x)|"))))
						expanded := b.Have(
							"(u + v)² ≤ 2u² + 2v²",
							"(«level» + K * |a(x)|) * («level» + K * |a(x)|) ≤ «majorant»(x)",
							ByArith(
								Normalized,
								absoluteSquare,
								real_order_ring.SquareNonneg.At(b.TermAs[Real]("«level» - K * |a(x)|"))))
						nonnegative := b.Have(
							"the square is its own absolute value",
							"|«average»(x) * «average»(x)| = «average»(x) * «average»(x)",
							By(
								real_order_ring.SquareNonneg.At(value),
								real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("«average»(x) * «average»(x)"))))
						b.Show(
							"chain the two bounds",
							By(
								nonnegative,
								expanded,
								square,
								real_construction.LessEqTrans.At(
									b.TermAs[Real]("«average»(x) * «average»(x)"),
									b.TermAs[Real]("(«level» + K * |a(x)|) * («level» + K * |a(x)|)"),
									b.TermAs[Real]("«majorant»(x)"))))
					}))
				almostSurely := arg.Have(
					"so the bound holds almost everywhere",
					"measure_ae(Ω, S, μ, λx:A. |«average»(x) * «average»(x)| ≤ «majorant»(x))",
					By(
						spreadBound,
						pointwise,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							arg.TermAs[Set[A]]("λx:A. s(x) * s(x) ≤ c"),
							arg.TermAs[Set[A]]("λx:A. |«average»(x) * «average»(x)| ≤ «majorant»(x)"))))
				arg.Show(
					"a measurable function dominated by an integrable one",
					By(
						measurable,
						majorantIntegrable,
						almostSurely,
						measure_integral.AEBoundedIntegral.At(Ω, S, μ, squared, majorant)))
			})
			// The first two Taylor terms have expectation zero: P·ξ by CondExpZeroPredictableProduct,
			// Q·(ξ² − v) by CondExpBoundedProductResidual. So E K − E H is the integral of the
			// residual K − H − P·ξ − Q·(ξ² − v)/2, which W bounds.
			conditionalCancellation := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀G:set(set(A)). " +
					"∀ξ v P Q H K W:(A → real). " +
					"∀M:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"is_cond_exp(Ω, S, μ, G, ξ, λx:A. &0)",
					"is_cond_exp(Ω, S, μ, G, λx:A. ξ(x) * ξ(x), v)",
					"real_measurable(Ω, G, P)",
					"real_measurable(Ω, G, Q)",
					"measure_ae(Ω, S, μ, λx:A. |Q(x)| ≤ M)",
					"real_integrable(Ω, S, μ, λx:A. P(x) * ξ(x))",
					"real_integrable(Ω, S, μ, H)",
					"real_integrable(Ω, S, μ, K)",
					"real_integrable(Ω, S, μ, W)",
					"measure_ae(Ω, " +
						"    S, " +
						"    μ, " +
						"    λx:A. |K(x) - H(x) - P(x) * ξ(x) - &1 / &2 * (Q(x) * (ξ(x) * ξ(x) - v(x)))| ≤ W(x))",
				},
				Conclusion: "|expectation(Ω, S, μ, K) - expectation(Ω, S, μ, H)| ≤ measure_integral(Ω, S, μ, W)",
				Abbrev: Abbrev{
					{Name: "correction", Text: "λx:A. Q(x) * (ξ(x) * ξ(x) - v(x))"},
					{Name: "residual", Text: "λx:A. K(x) - H(x) - P(x) * ξ(x) - &1 / &2 * «correction»(x)"},
				},
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				G *Expr[Set[Set[A]]],
				ξ, v, P, Q, H, K, W *Arrow[A, Real],
				M *Expr[Real],
				probability, martingale, conditionalVariance, pPredictable, qPredictable, qBounded, productIntegrable,
				hIntegrable, kIntegrable, wIntegrable, residualBound Fact,
			) {
				correction := a.TermAs[Fun[A, Real]]("«correction»")
				residual := a.TermAs[Fun[A, Real]]("«residual»")
				product := a.TermAs[Fun[A, Real]]("λx:A. P(x) * ξ(x)")
				difference := a.TermAs[Fun[A, Real]]("λx:A. K(x) - H(x)")
				partial := a.TermAs[Fun[A, Real]]("λx:A. K(x) - H(x) - P(x) * ξ(x)")
				half := a.TermAs[Real]("&1 / &2")
				measure := a.Have(
					"a probability is a measure",
					"measure_on(Ω, S, μ)",
					By(probability, probability_space.ProbabilityOnDef.At(Ω, S, μ)))
				cancelled := a.Have(
					"the predictable terms have mean zero",
					"measure_integral(Ω, S, μ, λx:A. P(x) * ξ(x)) = &0 ∧ "+
						"real_integrable(Ω, S, μ, «correction») ∧ "+
						"measure_integral(Ω, S, μ, «correction») = &0",
					By(
						probability,
						martingale,
						conditionalVariance,
						pPredictable,
						qPredictable,
						qBounded,
						productIntegrable,
						conditional_expectation.CondExpZeroPredictableProduct.At(Ω, S, μ, G, ξ, P),
						conditional_expectation.CondExpBoundedProductResidual.At(
							Ω, S, μ, G, a.TermAs[Fun[A, Real]]("λx:A. ξ(x) * ξ(x)"), v, Q, M)))
				halved := a.Have(
					"so does half the second one",
					"real_integrable(Ω, S, μ, λx:A. &1 / &2 * «correction»(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. &1 / &2 * «correction»(x)) = "+
						"&1 / &2 * measure_integral(Ω, S, μ, «correction»)",
					By(
						measure,
						cancelled,
						measure_integral.IntegrableScale.At(Ω, S, μ, correction, half),
						measure_integral.IntegralScale.At(Ω, S, μ, correction, half)))
				firstDifference := a.Have(
					"K − H integrates term by term",
					"real_integrable(Ω, S, μ, λx:A. K(x) - H(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. K(x) - H(x)) = "+
						"measure_integral(Ω, S, μ, K) - measure_integral(Ω, S, μ, H)",
					By(
						kIntegrable,
						hIntegrable,
						measure,
						measure_integral.IntegrableSub.At(Ω, S, μ, K, H),
						measure_integral.IntegralSub.At(Ω, S, μ, K, H)))
				secondDifference := a.Have(
					"so does K − H − P·ξ",
					"real_integrable(Ω, S, μ, λx:A. K(x) - H(x) - P(x) * ξ(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. K(x) - H(x) - P(x) * ξ(x)) = "+
						"measure_integral(Ω, S, μ, λx:A. K(x) - H(x)) - measure_integral(Ω, S, μ, λx:A. P(x) * ξ(x))",
					By(
						productIntegrable,
						firstDifference,
						measure,
						measure_integral.IntegrableSub.At(Ω, S, μ, difference, product),
						measure_integral.IntegralSub.At(Ω, S, μ, difference, product)))
				residualMean := a.Have(
					"and the residual",
					"real_integrable(Ω, S, μ, «residual») ∧ "+
						"measure_integral(Ω, S, μ, «residual») = "+
						"measure_integral(Ω, S, μ, λx:A. K(x) - H(x) - P(x) * ξ(x)) - "+
						"measure_integral(Ω, S, μ, λx:A. &1 / &2 * «correction»(x))",
					By(
						halved,
						secondDifference,
						measure,
						measure_integral.IntegrableSub.At(
							Ω, S, μ, partial, a.TermAs[Fun[A, Real]]("λx:A. &1 / &2 * «correction»(x)")),
						measure_integral.IntegralSub.At(
							Ω, S, μ, partial, a.TermAs[Fun[A, Real]]("λx:A. &1 / &2 * «correction»(x)"))))
				residualMeasurable := a.Have(
					"the residual is measurable",
					"real_measurable(Ω, S, «residual»)",
					By(residualMean, measure_integral.RealIntegrableDef.At(Ω, S, μ, residual)))
				residualBounded := a.Have(
					"its integral is at most that of W, which dominates it almost everywhere",
					"|measure_integral(Ω, S, μ, «residual»)| ≤ measure_integral(Ω, S, μ, W)",
					By(
						wIntegrable,
						residualBound,
						measure,
						residualMeasurable,
						measure_integral.AEBoundedIntegral.At(Ω, S, μ, residual, W)))
				meanDifference := a.Have(
					"the integral of the residual is E K − E H",
					"measure_integral(Ω, S, μ, «residual») = expectation(Ω, S, μ, K) - expectation(Ω, S, μ, H)",
					ByArith(
						Normalized,
						cancelled,
						halved,
						firstDifference,
						secondDifference,
						residualMean,
						probability_space.ExpectationDef.At(Ω, S, μ, K),
						probability_space.ExpectationDef.At(Ω, S, μ, H)))
				a.Show(
					"so W bounds E K − E H",
					By(residualBounded, meanDifference))
			})
			// The tail of ξ² beyond ε is integrable, with integral the event integral over
			// {ε < |ξ|}: it is the cut of the integrable ξ² to a measurable event.
			tailIntegral := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀ξ:(A → real). " +
					"∀ε:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"real_measurable(Ω, S, ξ)",
					"real_integrable(Ω, S, μ, λx:A. ξ(x) * ξ(x))",
				},
				Conclusion: "real_integrable(Ω, S, μ, λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)) ∧ " +
					"measure_integral(Ω, S, μ, λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)) = " +
					"event_integral(Ω, S, μ, {x:A | ε < |ξ(x)|}, λx:A. ξ(x) * ξ(x)) ∧ " +
					"&0 ≤ event_integral(Ω, S, μ, {x:A | ε < |ξ(x)|}, λx:A. ξ(x) * ξ(x))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				ξ *Arrow[A, Real],
				ε *Expr[Real],
				probability, measurable, squareIntegrable Fact,
			) {
				square := a.TermAs[Fun[A, Real]]("λx:A. ξ(x) * ξ(x)")
				tail := a.TermAs[Fun[A, Real]]("λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)")
				field := a.Have(
					"S is a σ-algebra",
					"sigma_algebra_on(Ω, S)",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ)))
				event := a.Have(
					"the tail event is measurable, |ξ| being measurable",
					"{x:A | x ∈ Ω ∧ ε < |ξ(x)|} ∈ S",
					By(
						measurable,
						field,
						measurable_function.RealMeasurableAbs.At(Ω, S, ξ),
						measurable_function.RealMeasurableIffRay.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |ξ(x)|"))))
				cut := a.Have(
					"so the cut of ξ² to it is integrable",
					"real_integrable(Ω, S, μ, λx:A. COND(x ∈ {x:A | x ∈ Ω ∧ ε < |ξ(x)|}, ξ(x) * ξ(x), &0))",
					By(
						probability,
						squareIntegrable,
						field,
						event,
						event_integral.IntegrableOnEvent.At(
							Ω, S, μ, a.TermAs[Set[A]]("{x:A | x ∈ Ω ∧ ε < |ξ(x)|}"), square)))
				sameOnCarrier := a.Have(
					"on the carrier the cut is the tail",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ Ω",
						},
						Conclusion: "COND(x ∈ {x:A | x ∈ Ω ∧ ε < |ξ(x)|}, ξ(x) * ξ(x), &0) = " +
							"COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)",
					},
					BySets())
				integrable := a.Have(
					"the tail is integrable",
					"real_integrable(Ω, S, μ, λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0))",
					By(
						cut,
						sameOnCarrier,
						measure_integral.RealIntegrableEqOn.At(
							Ω,
							S,
							μ,
							a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ {x:A | x ∈ Ω ∧ ε < |ξ(x)|}, ξ(x) * ξ(x), &0)"),
							tail)))
				sameEverywhere := a.Have(
					"the tail is the cut of ξ² to {ε < |ξ|}",
					"(λx:A. COND(x ∈ {x:A | ε < |ξ(x)|}, ξ(x) * ξ(x), &0)) = λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)",
					Funext(),
					BySets())
				eventIntegral := a.Have(
					"so its integral is the event integral",
					"measure_integral(Ω, S, μ, λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)) = "+
						"event_integral(Ω, S, μ, {x:A | ε < |ξ(x)|}, λx:A. ξ(x) * ξ(x))",
					By(
						sameEverywhere,
						event_integral.EventIntegralDef.At(Ω, S, μ, a.TermAs[Set[A]]("{x:A | ε < |ξ(x)|}"), square)))
				nonnegative := a.Have(
					"the tail is nonnegative",
					"∀x:A. x ∈ Ω ⇒ &0 ≤ COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)",
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						b.Assume()
						b.Show(
							"a square or zero",
							ByArith(Normalized, real_order_ring.SquareNonneg.At(ξ.Apply(x))))
					}))
				a.Show(
					"a nonnegative integrable function has nonnegative integral",
					By(nonnegative, eventIntegral, integrable, measure_integral.IntegralNonneg.At(Ω, S, μ, tail)))
			})
			// The clock is nonnegative and the second moments of the row sum to at most c: each
			// second moment is the mean of its conditional variance, and the summed variance lies
			// in [0, c] almost everywhere.
			secondMomentsBudget := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real). " +
					"∀c:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"∀k:num. k < n ⇒ is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k))",
					"measure_ae(Ω, S, μ, λx:A. (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{k<n} v(k, x) ≤ c)",
				},
				Conclusion: "&0 ≤ c ∧ Σ_{k<n} measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) ≤ c",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				c *Expr[Real],
				probability, conditional, clock Fact,
			) {
				rowSet := a.TermAs[Set[Nat]]("{k:num | k < n}")
				summedVariance := a.TermAs[Fun[A, Real]]("λx:A. Σ_{k<n} v(k, x)")
				constant := a.TermAs[Fun[A, Real]]("λx:A. c")
				meanOfSum := a.TermAs[Real]("measure_integral(Ω, S, μ, λx:A. Σ_{k<n} v(k, x))")
				moments := a.Have(
					"each v(j) is integrable, with the integral of ξ(j)²",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j < n",
						},
						Conclusion: "real_integrable(Ω, S, μ, v(j)) ∧ " +
							"measure_integral(Ω, S, μ, λx:A. ξ(j, x) * ξ(j, x)) = measure_integral(Ω, S, μ, v(j))",
					},
					Derive(func(b *Argument) {
						j := b.FixAs[Nat]("j")
						early := b.Assume()
						square := b.TermAs[Fun[A, Real]]("λx:A. ξ(j, x) * ξ(j, x)")
						variance := b.TermAs[Fun[A, Real]]("v(j)")
						b.Show(
							"a conditional expectation keeps the integral",
							By(
								conditional.At(j),
								early,
								conditional_expectation.IsCondExpDef.At(Ω, S, μ, F.Apply(j), square, variance),
								conditional_expectation.CondExpIntegral.At(Ω, S, μ, F.Apply(j), square, variance)))
					}))
				integrable := a.Have(
					"each v(j) is integrable",
					"∀j:num. j < n ⇒ real_integrable(Ω, S, μ, v(j))",
					By(moments))
				summed := a.Have(
					"the variances integrate term by term",
					"real_integrable(Ω, S, μ, λx:A. Σ_{k<n} v(k, x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. Σ_{k<n} v(k, x)) = Σ_{j<n} measure_integral(Ω, S, μ, v(j))",
					By(
						probability,
						integrable,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_integral.IntegralFiniteSum.At(Ω, S, μ, v, n)))
				pointwise := a.Have(
					"on the clock event the summed variance lies in [0, c]",
					"∀x:A. x ∈ Ω ∧ ((∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{k<n} v(k, x) ≤ c) ⇒ |Σ_{k<n} v(k, x)| ≤ c",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						onClock := b.Assume()
						rowNonnegative := b.Have(
							"the variances at x are nonnegative along the row",
							"∀k:num. k ∈ {k:num | k < n} ⇒ &0 ≤ v(k, x)",
							BySets(onClock))
						total := b.Have(
							"so is their sum",
							"&0 ≤ Σ_{k<n} v(k, x)",
							By(rowNonnegative, real_sum.Nonneg.At(rowSet, b.TermAs[Fun[Nat, Real]]("λk:num. v(k, x)"))))
						b.Show(
							"a nonnegative number below c",
							By(onClock, total, real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("Σ_{k<n} v(k, x)"))))
					}))
				bounded := a.Have(
					"almost everywhere |Σ v(k)| ≤ c",
					"measure_ae(Ω, S, μ, λx:A. |Σ_{k<n} v(k, x)| ≤ c)",
					By(
						clock,
						pointwise,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							a.TermAs[Set[A]]("λx:A. (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ Σ_{k<n} v(k, x) ≤ c"),
							a.TermAs[Set[A]]("λx:A. |Σ_{k<n} v(k, x)| ≤ c"))))
				constants := a.Have(
					"the summed variance is measurable, and c integrates to c",
					"real_measurable(Ω, S, λx:A. Σ_{k<n} v(k, x)) ∧ "+
						"measure_on(Ω, S, μ) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. c) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. c) = c",
					By(
						probability,
						summed,
						measure_integral.RealIntegrableDef.At(Ω, S, μ, summedVariance),
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						probability_space.ExpectationConstant.At(Ω, S, μ, c),
						probability_space.ExpectationDef.At(Ω, S, μ, constant)))
				meanBound := a.Have(
					"so its integral is at most c in absolute value",
					"|measure_integral(Ω, S, μ, λx:A. Σ_{k<n} v(k, x))| ≤ c",
					By(constants, bounded, measure_integral.AEBoundedIntegral.At(Ω, S, μ, summedVariance, constant)))
				sameMeans := a.Have(
					"the second moments are the means of the variances",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j ∈ {k:num | k < n}",
						},
						Conclusion: "measure_integral(Ω, S, μ, λx:A. ξ(j, x) * ξ(j, x)) = measure_integral(Ω, S, μ, v(j))",
					},
					BySets(moments))
				sums := a.Have(
					"so their sums agree",
					"Σ_{j<n} measure_integral(Ω, S, μ, λx:A. ξ(j, x) * ξ(j, x)) = "+
						"Σ_{j<n} measure_integral(Ω, S, μ, v(j))",
					By(
						sameMeans,
						real_sum.Congruence.At(
							rowSet,
							a.TermAs[Fun[Nat, Real]]("λj:num. measure_integral(Ω, S, μ, λx:A. ξ(j, x) * ξ(j, x))"),
							a.TermAs[Fun[Nat, Real]]("λj:num. measure_integral(Ω, S, μ, v(j))"))))
				a.Show(
					"c bounds the mean of the summed variance",
					ByArith(
						Normalized,
						sums,
						meanBound,
						summed,
						real_sgn_abs.AbsNonneg.At(meanOfSum),
						real_sgn_abs.AbsDominates.At(meanOfSum)))
			})
			// p + s·Y is Borel and square-integrable for Y standard normal: (p + s·y)² is
			// p² + 2ps·y + s²·y², and N(0, 1) has its first two moments.
			affineSquareIntegrable := ctx.Lemma("∀p s:real. "+
				"    real_measurable(𝕌, borel_sets(real_topology), λy:real. p + s * y) ∧ "+
				"    real_integrable(𝕌, "+
				"        borel_sets(real_topology), "+
				"        normal_distribution(&0, &1), "+
				"        λy:real. (p + s * y) * (p + s * y))",
				func(arg *Argument, p, s *Expr[Real]) {
					line := arg.TermAs[Set[Real]]("𝕌")
					borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
					standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
					identity := arg.TermAs[Fun[Real, Real]]("λy:real. y")
					square := arg.TermAs[Fun[Real, Real]]("λy:real. y * y")
					constant := arg.TermAs[Fun[Real, Real]]("λy:real. p * p")
					linear := arg.TermAs[Fun[Real, Real]]("λy:real. &2 * p * s * y")
					law := arg.Have(
						"N(0, 1) is a probability on the Borel σ-algebra, with |y| integrable",
						"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
							"measure_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
							"sigma_algebra_on(𝕌, borel_sets(real_topology)) ∧ "+
							"real_measurable(𝕌, borel_sets(real_topology), λy:real. y) ∧ "+
							"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. |y|)",
						By(
							standardNormalMoments,
							probability_space.ProbabilityOnDef.At(line, borel, standard),
							borel_function.LineBorelSigmaAlgebra))
					measurable := arg.Have(
						"y ↦ p + s·y is Borel",
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. p + s * y)",
						By(
							law,
							measurable_function.RealMeasurableConst.At(line, borel, p),
							measurable_function.RealMeasurableScale.At(line, borel, identity, s),
							measurable_function.RealMeasurableAdd.At(
								line,
								borel,
								arg.TermAs[Fun[Real, Real]]("λy:real. p"),
								arg.TermAs[Fun[Real, Real]]("λy:real. s * y"))))
					secondMoment := arg.Have(
						"y² is integrable under N(0, 1)",
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y)",
						ByArith(
							Normalized,
							normal_moments.NormalDistributionMoments.At(arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1"))))
					reflexive := arg.Have(
						"|y| ≤ |y|",
						"∀y:real. y ∈ 𝕌 ⇒ |y| ≤ |y|",
						ByArith())
					moments := arg.Have(
						"y and y² are integrable",
						"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y) ∧ "+
							"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. y * y)",
						By(
							law,
							reflexive,
							secondMoment,
							measure_integral.IntegrableDominated.At(
								line, borel, standard, identity, arg.TermAs[Fun[Real, Real]]("λy:real. |y|"))))
					expanded := arg.Have(
						"so is the expanded square p² + 2ps·y + s²·y²",
						"real_integrable(𝕌, "+
							"    borel_sets(real_topology), "+
							"    normal_distribution(&0, &1), "+
							"    λy:real. p * p + &2 * p * s * y + s * s * (y * y))",
						By(
							law,
							moments,
							probability_space.ExpectationConstant.At(line, borel, standard, arg.TermAs[Real]("p * p")),
							measure_integral.IntegrableScale.At(
								line, borel, standard, identity, arg.TermAs[Real]("&2 * p * s")),
							measure_integral.IntegrableScale.At(line, borel, standard, square, arg.TermAs[Real]("s * s")),
							measure_integral.IntegrableAdd.At(line, borel, standard, constant, linear),
							measure_integral.IntegrableAdd.At(
								line,
								borel,
								standard,
								arg.TermAs[Fun[Real, Real]]("λy:real. p * p + &2 * p * s * y"),
								arg.TermAs[Fun[Real, Real]]("λy:real. s * s * (y * y)"))))
					expansion := arg.Have(
						"which is (p + s·y)²",
						"(λy:real. (p + s * y) * (p + s * y)) = λy:real. p * p + &2 * p * s * y + s * s * (y * y)",
						Funext(),
						ByArith(Normalized))
					arg.Show(
						"both parts",
						By(measurable, expanded, expansion))
				})
			// conditionalVarianceExcess at every term of the row, and the measurability of ε² plus
			// the excesses.
			varianceExcessRow := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real). " +
					"∀ε:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"∀k:num. " +
						"    k < n ⇒ " +
						"    real_measurable(Ω, S, ξ(k)) ∧ is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k))",
				},
				Conclusion: "(∀k:num. " +
					"    k < n ⇒ " +
					"    real_integrable(Ω, S, μ, v(k)) ∧ " +
					"    real_integrable(Ω, S, μ, λx:A. max(v(k, x) - ε ^ 2, &0)) ∧ " +
					"    measure_integral(Ω, S, μ, λx:A. max(v(k, x) - ε ^ 2, &0)) ≤ " +
					"    event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))) ∧ " +
					"real_measurable(Ω, S, λx:A. ε ^ 2 + Σ_{k<n} max(v(k, x) - ε ^ 2, &0))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				ε *Expr[Real],
				probability, row Fact,
			) {
				finite := a.Have(
					"a probability is a finite measure",
					"finite_measure_on(Ω, S, μ)",
					By(
						Normalized,
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.FiniteMeasureDef.At(Ω, S, μ),
						extended_nonneg_real.OfRealNotInfinity.At(a.TermAs[Real]("&1"))))
				excess := a.Have(
					"each conditional variance is integrable, its excess over ε² bounded by the Lindeberg tail",
					Statement{
						Binders: "∀k:num.",
						Hypotheses: []string{
							"k < n",
						},
						Conclusion: "real_integrable(Ω, S, μ, v(k)) ∧ " +
							"real_integrable(Ω, S, μ, λx:A. max(v(k, x) - ε ^ 2, &0)) ∧ " +
							"measure_integral(Ω, S, μ, λx:A. max(v(k, x) - ε ^ 2, &0)) ≤ " +
							"event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))",
					},
					Derive(func(b *Argument) {
						k := b.FixAs[Nat]("k")
						early := b.Assume()
						increment := b.TermAs[Fun[A, Real]]("ξ(k)")
						variance := b.TermAs[Fun[A, Real]]("v(k)")
						b.Show(
							"v(k) is a conditional expectation, and the excess bound holds at the k-th term",
							By(
								finite,
								early,
								row,
								conditional_expectation.IsCondExpDef.At(
									Ω, S, μ, F.Apply(k), b.TermAs[Fun[A, Real]]("λx:A. ξ(k, x) * ξ(k, x)"), variance),
								conditionalVarianceExcess.At(Ω, S, μ, F.Apply(k), increment, variance, ε)))
					}))
				excessIntegrable := a.Have(
					"each excess over ε² is integrable",
					"∀k:num. k < n ⇒ real_integrable(Ω, S, μ, λx:A. max(v(k, x) - ε ^ 2, &0))",
					By(excess))
				excessSum := a.TermAs[Fun[A, Real]]("λx:A. Σ_{k<n} max(v(k, x) - ε ^ 2, &0)")
				summed := a.Have(
					"so is their sum",
					"real_integrable(Ω, S, μ, λx:A. Σ_{k<n} max(v(k, x) - ε ^ 2, &0))",
					By(
						probability,
						excessIntegrable,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_integral.IntegralFiniteSum.At(
							Ω, S, μ, a.TermAs[Fun2[Nat, A, Real]]("λk:num. λx:A. max(v(k, x) - ε ^ 2, &0)"), n)))
				measurable := a.Have(
					"ε² plus the integrable sum is measurable",
					"real_measurable(Ω, S, λx:A. ε ^ 2 + Σ_{k<n} max(v(k, x) - ε ^ 2, &0))",
					By(
						probability,
						summed,
						measure_integral.RealIntegrableDef.At(Ω, S, μ, excessSum),
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ),
						measurable_function.RealMeasurableConst.At(Ω, S, a.TermAs[Real]("ε ^ 2")),
						measurable_function.RealMeasurableAdd.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. ε ^ 2"), excessSum)))
				a.Show(
					"both parts",
					By(excess, measurable))
			})
			// Φ(0) is the normal integral of D(0) at √c, a constant: the empty row adds nothing
			// and spends nothing of the clock.
			smoothedStart := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀ξ v:(num → A → real). " +
					"∀D:(num → real → real). " +
					"∀c:real.",
				Hypotheses: []string{"probability_on(Ω, S, μ)"},
				Conclusion: "expectation(Ω, S, μ, λx:A. «smoothed»(0, x)) = " +
					"«gauss»(λy:real. D(0)(real_sqrt(c) * y))",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				ξ, v *Arrow2[Nat, A, Real],
				D *Arrow2[Nat, Real, Real],
				c *Expr[Real],
				probability Fact,
			) {
				constant := arg.Have(
					"Φ(0) does not depend on x",
					"(λx:A. «gauss»(λy:real. D(0)(Σ_{j<0} ξ(j, x) + real_sqrt(c - Σ_{j<0} v(j, x)) * y))) = "+
						"λx:A. «gauss»(λy:real. D(0)(real_sqrt(c) * y))",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						integrand := b.Have(
							"the integrands agree",
							"(λy:real. D(0)(Σ_{j<0} ξ(j, x) + real_sqrt(c - Σ_{j<0} v(j, x)) * y)) = "+
								"λy:real. D(0)(real_sqrt(c) * y)",
							Funext(),
							Derive(func(d *Argument) {
								d.FixAs[Real]("y")
								empty := d.Have(
									"the empty sums vanish",
									"Σ_{j<0} ξ(j, x) = &0 ∧ Σ_{j<0} v(j, x) = &0",
									By(
										real_sum.BelowClauses.At(d.TermAs[Fun[Nat, Real]]("λj:num. ξ(j, x)")),
										real_sum.BelowClauses.At(d.TermAs[Fun[Nat, Real]]("λj:num. v(j, x)"))))
								point := d.Have(
									"so the point is √c·y",
									"Σ_{j<0} ξ(j, x) + real_sqrt(c - Σ_{j<0} v(j, x)) * y = real_sqrt(c) * y",
									By(
										empty,
										real_ring.SubRightZero.At(c),
										real_construction.AddLeftId.At(d.TermAs[Real]("real_sqrt(c) * y"))))
								d.Show(
									"D(0) at the same point",
									By(point))
							}))
						b.Show(
							"so are their averages",
							By(integrand))
					}))
				arg.Show(
					"the expectation of a constant",
					By(
						probability,
						constant,
						probability_space.ExpectationConstant.At(
							Ω, S, μ, arg.TermAs[Real]("«gauss»(λy:real. D(0)(real_sqrt(c) * y))"))))
			})
			// The four normal averages gaussianTaylor reads are integrable, by the growth of D(0),
			// D(1) and D(2): each is quadraticGrowthAverage at its growth bound, and the doubly
			// smoothed one smoothedIntegrable at the constant spread t.
			gaussianTaylorIntegrable := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀K M₂ p s t h:real.",
				Hypotheses: []string{
					"∀j:num. j ≤ 2 ⇒ real_measurable(𝕌, borel_sets(real_topology), D(j))",
					"&0 ≤ K",
					"&0 ≤ M₂",
					"∀x:real. |D(0)(x)| ≤ K * (&1 + x * x) ∧ |D(1)(x)| ≤ K * (&1 + |x|) ∧ |D(2)(x)| ≤ M₂",
				},
				Conclusion: "real_integrable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    normal_distribution(&0, &1), " +
					"    λy:real. D(0)(p + s * y + h)) ∧ " +
					"real_integrable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    normal_distribution(&0, &1), " +
					"    λy:real. «gauss»(λz:real. D(0)(p + s * y + t * z))) ∧ " +
					"real_integrable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    normal_distribution(&0, &1), " +
					"    λy:real. D(1)(p + s * y)) ∧ " +
					"real_integrable(𝕌, " +
					"    borel_sets(real_topology), " +
					"    normal_distribution(&0, &1), " +
					"    λy:real. D(2)(p + s * y))",
			}, func(
				arg *Argument,
				D *Arrow2[Nat, Real, Real],
				K, M2, p, s, t, h *Expr[Real],
				measurable, kNonnegative, curvatureNonnegative, growth Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				zero := arg.TermAs[Real]("&0")
				value := arg.TermAs[Fun[Real, Real]]("D(0)")
				derivatives := arg.Have(
					"D(0), D(1) and D(2) are Borel",
					"real_measurable(𝕌, borel_sets(real_topology), D(0)) ∧ "+
						"real_measurable(𝕌, borel_sets(real_topology), D(1)) ∧ "+
						"real_measurable(𝕌, borel_sets(real_topology), D(2))",
					By(
						measurable.At(arg.TermAs[Nat]("0")),
						measurable.At(arg.TermAs[Nat]("1")),
						measurable.At(arg.TermAs[Nat]("2"))))
				valueGrowth := arg.Have(
					"D(0) grows like K + K·z²",
					"∀z:real. |D(0)(z)| ≤ K + &0 * |z| + K * z * z",
					Derive(func(b *Argument) {
						z := b.FixAs[Real]("z")
						b.Show(
							"expand K·(1 + z²)",
							ByArith(Normalized, growth.At(z)))
					}))
				slopeGrowth := arg.Have(
					"D(1) like K + K·|z|",
					"∀z:real. |D(1)(z)| ≤ K + K * |z| + &0 * z * z",
					Derive(func(b *Argument) {
						z := b.FixAs[Real]("z")
						b.Show(
							"expand K·(1 + |z|)",
							ByArith(Normalized, growth.At(z)))
					}))
				curvatureGrowth := arg.Have(
					"and D(2) is bounded by M₂",
					"∀z:real. |D(2)(z)| ≤ M₂ + &0 * |z| + &0 * z * z",
					Derive(func(b *Argument) {
						z := b.FixAs[Real]("z")
						b.Show(
							"the bound M₂",
							ByArith(Normalized, growth.At(z)))
					}))
				shifted := arg.Have(
					"D(0) is integrable at p + h + s·Y",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. D(0)(p + h + s * y))",
					By(
						kNonnegative,
						derivatives,
						valueGrowth,
						At(quadraticGrowthAverage, value, arg.TermAs[Real]("p + h"), s, K, zero, K)))
				slope := arg.Have(
					"D(1) is integrable at p + s·Y",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. D(1)(p + s * y))",
					By(
						kNonnegative,
						derivatives,
						slopeGrowth,
						At(quadraticGrowthAverage, arg.TermAs[Fun[Real, Real]]("D(1)"), p, s, K, K, zero)))
				curvature := arg.Have(
					"D(2) is integrable at p + s·Y",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. D(2)(p + s * y))",
					By(
						curvatureNonnegative,
						derivatives,
						curvatureGrowth,
						At(quadraticGrowthAverage, arg.TermAs[Fun[Real, Real]]("D(2)"), p, s, M2, zero, zero)))
				reordered := arg.Have(
					"the shift by h commutes with the spread",
					"(λy:real. D(0)(p + s * y + h)) = λy:real. D(0)(p + h + s * y)",
					Funext(),
					Derive(func(b *Argument) {
						b.FixAs[Real]("y")
						b.Show(
							"regroup the point",
							ByArith(Normalized))
					}))
				law := arg.Have(
					"N(0, 1) is a probability on the Borel σ-algebra",
					"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"measure_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
						"sigma_algebra_on(𝕌, borel_sets(real_topology))",
					By(
						standardNormalMoments,
						probability_space.ProbabilityOnDef.At(line, borel, standard),
						borel_function.LineBorelSigmaAlgebra))
				affine := arg.Have(
					"p + s·y is Borel and square-integrable, and the constant t Borel",
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. p + s * y) ∧ "+
						"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. (p + s * y) * (p + s * y)) ∧ "+
						"real_measurable(𝕌, borel_sets(real_topology), λy:real. t)",
					By(
						law,
						At(affineSquareIntegrable, p, s),
						measurable_function.RealMeasurableConst.At(line, borel, t)))
				reflexive := arg.Have(
					"t² ≤ t²",
					"∀y:real. y ∈ 𝕌 ⇒ t * t ≤ t * t",
					ByArith())
				constantSpread := arg.Have(
					"the spread t² ≤ t² holds almost everywhere",
					"measure_ae(𝕌, borel_sets(real_topology), normal_distribution(&0, &1), λy:real. t * t ≤ t * t)",
					By(
						law,
						reflexive,
						measure_space.AEOfEverywhere.At(
							line, borel, standard, arg.TermAs[Set[Real]]("λy:real. t * t ≤ t * t"))))
				valueQuadratic := arg.Have(
					"D(0) has quadratic growth",
					"∀z:real. |D(0)(z)| ≤ K * (&1 + z * z)",
					By(growth))
				smoothed := arg.Have(
					"the doubly smoothed average is integrable",
					"real_integrable(𝕌, "+
						"    borel_sets(real_topology), "+
						"    normal_distribution(&0, &1), "+
						"    λy:real. «gauss»(λz:real. D(0)(p + s * y + t * z)))",
					By(
						kNonnegative,
						derivatives,
						law,
						affine,
						valueQuadratic,
						constantSpread,
						At(smoothedIntegrable,
							line,
							borel,
							standard,
							arg.TermAs[Fun[Real, Real]]("λy:real. p + s * y"),
							arg.TermAs[Fun[Real, Real]]("λy:real. t"),
							value,
							K,
							arg.TermAs[Real]("t * t"))))
				arg.Show(
					"the four averages",
					By(reordered, shifted, smoothed, slope, curvature))
			})
			// Normal variables of variances r and v add to one of variance r + v, for h of
			// quadratic growth: StandardNormalSmoothingSemigroup, whose conditions for positive
			// variances the growth supplies.
			smoothingSemigroup := ctx.Lemma(Statement{
				Binders: "∀h:(real → real). ∀K a r v:real.",
				Hypotheses: []string{
					"&0 ≤ r",
					"&0 ≤ v",
					"real_measurable(𝕌, borel_sets(real_topology), h)",
					"∀x:real. |h(x)| ≤ K * (&1 + x * x)",
				},
				Conclusion: "«gauss»(λy:real. «gauss»(λz:real. h(a + real_sqrt(r) * y + real_sqrt(v) * z))) = " +
					"«gauss»(λy:real. h(a + real_sqrt(r + v) * y))",
			}, func(
				arg *Argument,
				h *Arrow[Real, Real],
				K, a, r, v *Expr[Real],
				rNonnegative, vNonnegative, hBorel, growth Fact,
			) {
				line := arg.TermAs[Set[Real]]("𝕌")
				borel := arg.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
				standard := arg.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				conditions := arg.Have(
					"for positive variances, h is integrable under N(a, r + v) and its N(0, v)-averages are Borel",
					Statement{
						Hypotheses: []string{"&0 < r", "&0 < v"},
						Conclusion: "real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a, r + v), h) ∧ " +
							"real_measurable(𝕌, " +
							"    borel_sets(real_topology), " +
							"    λx:real. " +
							"        expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y)))",
					},
					Derive(func(b *Argument) {
						positive := b.Assume()
						total := b.Have(
							"r + v is positive",
							"&0 < r + v",
							ByArith(positive))
						integrable := b.Have(
							"h is integrable under N(a, r + v), having quadratic growth",
							"real_integrable(𝕌, borel_sets(real_topology), normal_distribution(a, r + v), h)",
							By(
								hBorel,
								growth,
								total,
								normal_moments.NormalQuadraticGrowthIntegrable.At(a, b.TermAs[Real]("r + v"), K, h)))
						laws := b.Have(
							"N(0, 1) and N(0, v) are probabilities on the Borel σ-algebra",
							"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1)) ∧ "+
								"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, v)) ∧ "+
								"real_measurable(𝕌, borel_sets(real_topology), λx:real. x) ∧ "+
								"sigma_algebra_on(𝕌, borel_sets(real_topology))",
							By(
								positive,
								standardNormalMoments,
								normal_distribution.NormalDistributionProbability.At(b.TermAs[Real]("&0"), v),
								probability_space.ProbabilityOnDef.At(line, borel, standard),
								borel_function.LineBorelSigmaAlgebra))
						averages := b.Have(
							"x ↦ the N(0, v)-average of h(x + 1·y) is Borel",
							"real_measurable(𝕌, "+
								"    borel_sets(real_topology), "+
								"    λx:real. "+
								"        expectation(𝕌, "+
								"            borel_sets(real_topology), "+
								"            normal_distribution(&0, v), "+
								"            λy:real. h(x + &1 * y)))",
							By(
								hBorel,
								laws,
								At(gaussianAverageMeasurable,
									line,
									borel,
									standard,
									b.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, v)"),
									b.TermAs[Fun[Real, Real]]("λx:real. x"),
									b.TermAs[Fun[Real, Real]]("λx:real. &1"),
									h),
								measurable_function.RealMeasurableConst.At(line, borel, b.TermAs[Real]("&1"))))
						unitStep := b.Have(
							"the average does not see the factor 1",
							"(λx:real. "+
								"    expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + y))) = "+
								"λx:real. "+
								"    expectation(𝕌, borel_sets(real_topology), normal_distribution(&0, v), λy:real. h(x + &1 * y))",
							Funext(),
							Derive(func(c *Argument) {
								c.FixAs[Real]("x")
								unit := c.Have(
									"y ↦ h(x + y) is y ↦ h(x + 1·y)",
									"(λy:real. h(x + y)) = λy:real. h(x + &1 * y)",
									Funext(),
									ByArith(Normalized))
								c.Show(
									"so are their averages",
									By(unit))
							}))
						b.Show(
							"both conditions",
							By(unitStep, integrable, averages))
					}))
				arg.Show(
					"the convolution of the two normal variables",
					By(
						rNonnegative,
						vNonnegative,
						hBorel,
						growth,
						conditions,
						normal_convolution.StandardNormalSmoothingSemigroup.At(h, a, r, v)))
			})
			// The integral of a·f + b·g + c·h, by linearity.
			linearIntegral := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀f g h:(A → real). " +
					"∀a b c:real.",
				Hypotheses: []string{
					"measure_on(Ω, S, μ)",
					"real_integrable(Ω, S, μ, f)",
					"real_integrable(Ω, S, μ, g)",
					"real_integrable(Ω, S, μ, h)",
				},
				Conclusion: "real_integrable(Ω, S, μ, λx:A. a * f(x) + b * g(x) + c * h(x)) ∧ " +
					"measure_integral(Ω, S, μ, λx:A. a * f(x) + b * g(x) + c * h(x)) = " +
					"a * measure_integral(Ω, S, μ, f) + " +
					"b * measure_integral(Ω, S, μ, g) + " +
					"c * measure_integral(Ω, S, μ, h)",
			}, func(
				arg *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				f, g, h *Arrow[A, Real],
				a, b, c *Expr[Real],
				measure, fIntegrable, gIntegrable, hIntegrable Fact,
			) {
				scaledF := arg.TermAs[Fun[A, Real]]("λx:A. a * f(x)")
				scaledG := arg.TermAs[Fun[A, Real]]("λx:A. b * g(x)")
				scaledH := arg.TermAs[Fun[A, Real]]("λx:A. c * h(x)")
				front := arg.TermAs[Fun[A, Real]]("λx:A. a * f(x) + b * g(x)")
				scaled := arg.Have(
					"each scaled function is integrable, with the scalar pulled out",
					"real_integrable(Ω, S, μ, λx:A. a * f(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. a * f(x)) = a * measure_integral(Ω, S, μ, f) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. b * g(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. b * g(x)) = b * measure_integral(Ω, S, μ, g) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. c * h(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. c * h(x)) = c * measure_integral(Ω, S, μ, h)",
					By(
						measure,
						fIntegrable,
						gIntegrable,
						hIntegrable,
						measure_integral.IntegrableScale.At(Ω, S, μ, f, a),
						measure_integral.IntegralScale.At(Ω, S, μ, f, a),
						measure_integral.IntegrableScale.At(Ω, S, μ, g, b),
						measure_integral.IntegralScale.At(Ω, S, μ, g, b),
						measure_integral.IntegrableScale.At(Ω, S, μ, h, c),
						measure_integral.IntegralScale.At(Ω, S, μ, h, c)))
				pair := arg.Have(
					"a·f + b·g integrates term by term",
					"real_integrable(Ω, S, μ, λx:A. a * f(x) + b * g(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. a * f(x) + b * g(x)) = "+
						"a * measure_integral(Ω, S, μ, f) + b * measure_integral(Ω, S, μ, g)",
					By(
						measure,
						scaled,
						measure_integral.IntegrableAdd.At(Ω, S, μ, scaledF, scaledG),
						measure_integral.IntegralAdd.At(Ω, S, μ, scaledF, scaledG)))
				arg.Show(
					"and so does the last term",
					By(
						measure,
						scaled,
						pair,
						measure_integral.IntegrableAdd.At(Ω, S, μ, front, scaledH),
						measure_integral.IntegralAdd.At(Ω, S, μ, front, scaledH)))
			})
			// One replacement at a point: D(0) at p + h smoothed by a normal variable of variance
			// r,
			// against D(0) at p smoothed by one of variance r + w, less the first two Taylor terms
			// in h
			// and the variance w they trade for, is at most the cubic and the Lindeberg remainders.
			scalarStep := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀M₂ M₃ p h r w ε:real.",
				Hypotheses: []string{
					"∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
					"&0 ≤ r",
					"&0 ≤ w",
					"&0 < ε",
				},
				Conclusion: "|«gauss»(λy:real. D(0)(p + h + real_sqrt(r) * y)) - " +
					"«gauss»(λy:real. D(0)(p + real_sqrt(r + w) * y)) - " +
					"«gauss»(λy:real. D(1)(p + real_sqrt(r) * y)) * h - " +
					"&1 / &2 * («gauss»(λy:real. D(2)(p + real_sqrt(r) * y)) * (h * h - w))| ≤ " +
					"M₃ * ε / &6 * (h * h) + M₂ * COND(ε < |h|, h * h, &0) + M₃ / &3 * (w * real_sqrt(w))",
			}, func(
				a *Argument,
				D *Arrow2[Nat, Real, Real],
				M2, M3, p, h, r, w, ε *Expr[Real],
				tower, bounds, rNonnegative, wNonnegative, positive Fact,
			) {
				value := a.TermAs[Fun[Real, Real]]("D(0)")
				K, growth := a.ObtainAs[Real](
					"D(0) grows at most quadratically and D(1) at most linearly",
					"∃K:real. &0 ≤ K ∧ (∀x:real. |D(0)(x)| ≤ K * (&1 + x * x) ∧ |D(1)(x)| ≤ K * (&1 + |x|))",
					By(
						tower,
						bounds,
						At(real_derivative.BoundedSecondDerivativeGrowth,
							value,
							a.TermAs[Fun[Real, Real]]("D(1)"),
							a.TermAs[Fun[Real, Real]]("D(2)"),
							M2)))
				borel := a.Have(
					"D(0), D(1) and D(2) are differentiable, hence Borel",
					"∀j:num. j ≤ 2 ⇒ real_measurable(𝕌, borel_sets(real_topology), D(j))",
					By(tower, At(derivativesBorel, D)))
				curvatureBound := a.Have(
					"M₂ bounds |D(2)(0)|, so it is nonnegative",
					"&0 ≤ M₂",
					ByArith(bounds.At(a.TermAs[Real]("&0"))))
				spread := a.TermAs[Real]("real_sqrt(r)")
				taylor := a.Have(
					"Taylor's formula at p + √r·y in h, the variance w spent on a second normal variable",
					"|«gauss»(λy:real. D(0)(p + real_sqrt(r) * y + h)) - "+
						"«gauss»(λy:real. «gauss»(λz:real. D(0)(p + real_sqrt(r) * y + real_sqrt(w) * z))) - "+
						"h * «gauss»(λy:real. D(1)(p + real_sqrt(r) * y)) - "+
						"(h * h - w) / &2 * «gauss»(λy:real. D(2)(p + real_sqrt(r) * y))| ≤ "+
						"M₃ * ε / &6 * h * h + M₂ * COND(ε < |h|, h * h, &0) + M₃ / &3 * w * real_sqrt(w)",
					By(
						tower,
						borel,
						bounds,
						curvatureBound,
						wNonnegative,
						positive,
						growth,
						At(gaussianTaylorIntegrable, D, K, M2, p, spread, a.TermAs[Real]("real_sqrt(w)"), h),
						At(gaussianTaylor, D, M2, M3, p, spread, w, h, ε)))
				semigroup := a.Have(
					"normal variables of variances r and w add to one of variance r + w",
					"«gauss»(λy:real. «gauss»(λz:real. D(0)(p + real_sqrt(r) * y + real_sqrt(w) * z))) = "+
						"«gauss»(λy:real. D(0)(p + real_sqrt(r + w) * y))",
					By(borel, rNonnegative, wNonnegative, growth, At(smoothingSemigroup, value, K, p, r, w)))
				shift := a.Have(
					"the shift by h moves past the normal variable",
					"(λy:real. D(0)(p + h + real_sqrt(r) * y)) = (λy:real. D(0)(p + real_sqrt(r) * y + h))",
					Funext(),
					ByArith())
				a.Show(
					"the averaged Taylor estimate is the step, rearranged",
					ByArith(shift, semigroup, taylor))
			})

			// One step of the replacement along the row. On the clock event, scalarStep at p =
			// S(k),
			// h = ξ(k), r = c − V(k + 1), w = v(k) bounds Φ(k + 1) − Φ(k) pointwise by the step's
			// cost,
			// up to A·ξ(k) and B·(ξ(k)² − v(k))/2, A and B the normal averages of D(1) and D(2) at
			// S(k) + √(c − V(k + 1))·y; both are known at F(k), and conditionalCancellation removes
			// them
			// in expectation.
			stepBound := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real). " +
					"∀D:(num → real → real). " +
					"∀c M₂ M₃ ε:real. " +
					"∀k:num.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"filtration_on(Ω, S, F)",
					"∀j:num. " +
						"    j < n ⇒ " +
						"    real_measurable(Ω, F(j + 1), ξ(j)) ∧ " +
						"    is_cond_exp(Ω, S, μ, F(j), ξ(j), λx:A. &0) ∧ " +
						"    is_cond_exp(Ω, S, μ, F(j), λx:A. ξ(j, x) * ξ(j, x), v(j))",
					"measure_ae(Ω, S, μ, λx:A. «rowVariance»(n, x) ≤ c)",
					"∀j:num. ∀y:real. j ≤ 2 ⇒ real_derivative_at(D(j), y, D(j + 1)(y))",
					"∀y:real. |D(2)(y)| ≤ M₂ ∧ |D(3)(y)| ≤ M₃",
					"&0 < ε",
					"k < n",
					"real_integrable(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))",
				},
				Conclusion: "|expectation(Ω, S, μ, «smoothed»(k + 1)) - expectation(Ω, S, μ, «smoothed»(k))| ≤ " +
					"«stepBudget»(k)",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				D *Arrow2[Nat, Real, Real],
				c, M2, M3, ε *Expr[Real],
				k *Expr[Nat],
				probability, isFiltration, row, budget, tower, bounds, positive, early, remainder Fact,
			) {
				next := a.TermAs[Nat]("k + 1")
				fieldK := a.TermAs[Set[Set[A]]]("F(k)")
				fieldNext := a.TermAs[Set[Set[A]]]("F(k + 1)")
				partialK := a.TermAs[Fun[A, Real]]("«rowSum»(k)")
				partialNext := a.TermAs[Fun[A, Real]]("«rowSum»(k + 1)")
				squareK := a.TermAs[Fun[A, Real]]("λx:A. «rowSum»(k, x) * «rowSum»(k, x)")
				squareNext := a.TermAs[Fun[A, Real]]("λx:A. «rowSum»(k + 1, x) * «rowSum»(k + 1, x)")
				leftK := a.TermAs[Fun[A, Real]]("λx:A. c - «rowVariance»(k, x)")
				leftNext := a.TermAs[Fun[A, Real]]("λx:A. c - «rowVariance»(k + 1, x)")
				rootK := a.TermAs[Fun[A, Real]]("λx:A. real_sqrt(c - «rowVariance»(k, x))")
				rootNext := a.TermAs[Fun[A, Real]]("λx:A. real_sqrt(c - «rowVariance»(k + 1, x))")
				constant := a.TermAs[Fun[A, Real]]("λx:A. c")
				slope := a.TermAs[Fun[A, Real]]("«derivativeAverage»(1, k)")
				curvature := a.TermAs[Fun[A, Real]]("«derivativeAverage»(2, k)")
				clock := a.TermAs[Fun[A, Bool]]("«withinClock»")
				gaussian := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("normal_distribution(&0, &1)")
				value := a.TermAs[Fun[Real, Real]]("D(0)")
				increment := a.TermAs[Fun[A, Real]]("ξ(k)")
				variance := a.TermAs[Fun[A, Real]]("v(k)")
				incrementSquare := a.TermAs[Fun[A, Real]]("λx:A. ξ(k, x) * ξ(k, x)")
				tail := a.TermAs[Fun[A, Real]]("λx:A. COND(ε < |ξ(k, x)|, ξ(k, x) * ξ(k, x), &0)")
				threeHalves := a.TermAs[Fun[A, Real]]("λx:A. v(k, x) * real_sqrt(v(k, x))")

				order := a.Have(
					"k and k + 1 lie in the row",
					"k ≤ n ∧ k + 1 ≤ n",
					ByArith(early))
				fields := a.Have(
					"each field of the filtration is a σ-algebra inside S",
					"∀i:num. sigma_algebra_on(Ω, F(i)) ∧ F(i) ⊆ S",
					By(isFiltration, filtration.FiltrationDef.At(Ω, S, F)))
				onClock := a.Have(
					"almost everywhere the variances are nonnegative and every prefix of them lies in [0, c]",
					"measure_ae(Ω, S, μ, «withinClock»)",
					By(
						probability,
						row,
						budget,
						At(varianceNonnegative, Ω, S, μ, F, n, ξ, v),
						At(clockEvent, Ω, S, μ, n, v, c)))
				atK := a.Have(
					"the first k terms of the row, read in F(k)",
					"probability_on(Ω, F(k), μ) ∧ "+
						"(∀j:num. "+
						"    j < k ⇒ "+
						"    real_measurable(Ω, F(k), ξ(j)) ∧ real_integrable(Ω, F(k), μ, λx:A. ξ(j, x) * ξ(j, x))) ∧ "+
						"(∀j:num. j < k + 1 ∧ j < n ⇒ real_integrable(Ω, F(k), μ, v(j)))",
					By(probability, isFiltration, row, order, At(rowAtField, Ω, S, μ, F, n, ξ, v, k)))
				atNext := a.Have(
					"the first k + 1 terms of the row, read in F(k + 1)",
					"probability_on(Ω, F(k + 1), μ) ∧ "+
						"(∀j:num. "+
						"    j < k + 1 ⇒ "+
						"    real_measurable(Ω, F(k + 1), ξ(j)) ∧ "+
						"    real_integrable(Ω, F(k + 1), μ, λx:A. ξ(j, x) * ξ(j, x)))",
					By(probability, isFiltration, row, order, At(rowAtField, Ω, S, μ, F, n, ξ, v, next)))
				inside := a.Have(
					"F(k) and F(k + 1) are σ-algebras inside S",
					"measure_on(Ω, S, μ) ∧ "+
						"sigma_algebra_on(Ω, S) ∧ "+
						"sigma_algebra_on(Ω, F(k)) ∧ "+
						"F(k) ⊆ S ∧ "+
						"sigma_algebra_on(Ω, F(k + 1)) ∧ "+
						"F(k + 1) ⊆ S",
					By(
						probability,
						fields.At(k),
						fields.At(next),
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ)))
				partialAtK := a.Have(
					"S(k) is F(k)-measurable and square-integrable",
					"real_measurable(Ω, F(k), «rowSum»(k)) ∧ "+
						"real_integrable(Ω, F(k), μ, λx:A. «rowSum»(k, x) * «rowSum»(k, x))",
					By(
						atK,
						probability_space.ProbabilityOnDef.At(Ω, fieldK, μ),
						measure_integral.SquareIntegrableSum.At(Ω, fieldK, μ, ξ, k)))
				partialAtNext := a.Have(
					"S(k + 1) is F(k + 1)-measurable and square-integrable",
					"real_measurable(Ω, F(k + 1), «rowSum»(k + 1)) ∧ "+
						"real_integrable(Ω, F(k + 1), μ, λx:A. «rowSum»(k + 1, x) * «rowSum»(k + 1, x))",
					By(
						atNext,
						probability_space.ProbabilityOnDef.At(Ω, fieldNext, μ),
						measure_integral.SquareIntegrableSum.At(Ω, fieldNext, μ, ξ, next)))
				partialInS := a.Have(
					"S(k) keeps both for S",
					"real_measurable(Ω, S, «rowSum»(k)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. «rowSum»(k, x) * «rowSum»(k, x))",
					By(
						inside,
						partialAtK,
						measurable_function.RealMeasurableSourceMono.At(Ω, fieldK, S, partialK),
						measurable_function.RealMeasurableMul.At(Ω, fieldK, partialK, partialK),
						measure_integral.SubSigmaRealIntegral.At(Ω, S, μ, fieldK, squareK)))
				partialNextInS := a.Have(
					"S(k + 1) keeps both for S",
					"real_measurable(Ω, S, «rowSum»(k + 1)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. «rowSum»(k + 1, x) * «rowSum»(k + 1, x))",
					By(
						inside,
						partialAtNext,
						measurable_function.RealMeasurableSourceMono.At(Ω, fieldNext, S, partialNext),
						measurable_function.RealMeasurableMul.At(Ω, fieldNext, partialNext, partialNext),
						measure_integral.SubSigmaRealIntegral.At(Ω, S, μ, fieldNext, squareNext)))
				term := a.Have(
					"ξ(k) is S-measurable, centred and square-integrable given F(k), with v(k) known at F(k)",
					"real_measurable(Ω, S, ξ(k)) ∧ "+
						"is_cond_exp(Ω, S, μ, F(k), ξ(k), λx:A. &0) ∧ "+
						"is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) ∧ "+
						"real_integrable(Ω, S, μ, v(k)) ∧ "+
						"real_measurable(Ω, F(k), v(k))",
					By(
						row.At(k),
						early,
						inside,
						measurable_function.RealMeasurableSourceMono.At(Ω, fieldNext, S, increment),
						conditional_expectation.IsCondExpDef.At(Ω, S, μ, fieldK, incrementSquare, variance)))
				variancesThrough := a.Have(
					"v(0), …, v(k) are integrable in F(k)",
					"∀i:num. i < k + 1 ⇒ real_integrable(Ω, F(k), μ, v(i))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]()
						below := b.Assume()
						b.Show(
							"i lies in the row",
							ByArith(atK, early, below))
					}))
				variancesBefore := a.Have(
					"so are v(0), …, v(k − 1)",
					"∀i:num. i < k ⇒ real_integrable(Ω, F(k), μ, v(i))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]()
						below := b.Assume()
						b.Show(
							"i lies in the row",
							ByArith(atK, early, below))
					}))
				clockNext := a.Have(
					"V(k + 1) is integrable in F(k)",
					"real_integrable(Ω, F(k), μ, «rowVariance»(k + 1))",
					By(
						atK,
						variancesThrough,
						probability_space.ProbabilityOnDef.At(Ω, fieldK, μ),
						measure_integral.IntegralFiniteSum.At(Ω, fieldK, μ, v, next)))
				clockK := a.Have(
					"V(k) is integrable in F(k)",
					"real_integrable(Ω, F(k), μ, «rowVariance»(k))",
					By(
						atK,
						variancesBefore,
						probability_space.ProbabilityOnDef.At(Ω, fieldK, μ),
						measure_integral.IntegralFiniteSum.At(Ω, fieldK, μ, v, k)))
				measureK := a.Have(
					"μ is a measure on F(k), under which the clock c is integrable",
					"measure_on(Ω, F(k), μ) ∧ real_integrable(Ω, F(k), μ, λx:A. c)",
					By(
						atK,
						probability_space.ProbabilityOnDef.At(Ω, fieldK, μ),
						probability_space.ExpectationConstant.At(Ω, fieldK, μ, c)))
				rootNextAtK := a.Have(
					"√(c − V(k + 1)) is F(k)-measurable",
					"real_measurable(Ω, F(k), λx:A. real_sqrt(c - «rowVariance»(k + 1, x)))",
					By(
						measureK,
						clockNext,
						inside,
						measure_integral.IntegrableSub.At(
							Ω, fieldK, μ, constant, a.TermAs[Fun[A, Real]]("«rowVariance»(k + 1)")),
						measure_integral.RealIntegrableDef.At(Ω, fieldK, μ, leftNext),
						At(sqrtMeasurable, Ω, fieldK, leftNext)))
				rootKAtK := a.Have(
					"√(c − V(k)) is F(k)-measurable",
					"real_measurable(Ω, F(k), λx:A. real_sqrt(c - «rowVariance»(k, x)))",
					By(
						measureK,
						clockK,
						inside,
						measure_integral.IntegrableSub.At(
							Ω, fieldK, μ, constant, a.TermAs[Fun[A, Real]]("«rowVariance»(k)")),
						measure_integral.RealIntegrableDef.At(Ω, fieldK, μ, leftK),
						At(sqrtMeasurable, Ω, fieldK, leftK)))
				roots := a.Have(
					"both square roots are S-measurable",
					"real_measurable(Ω, S, λx:A. real_sqrt(c - «rowVariance»(k, x))) ∧ "+
						"real_measurable(Ω, S, λx:A. real_sqrt(c - «rowVariance»(k + 1, x)))",
					By(
						inside,
						rootKAtK,
						rootNextAtK,
						measurable_function.RealMeasurableSourceMono.At(Ω, fieldK, S, rootK),
						measurable_function.RealMeasurableSourceMono.At(Ω, fieldK, S, rootNext)))
				K, growth := a.ObtainAs[Real](
					"D(0) grows at most quadratically and D(1) at most linearly",
					"∃K:real. &0 ≤ K ∧ (∀x:real. |D(0)(x)| ≤ K * (&1 + x * x) ∧ |D(1)(x)| ≤ K * (&1 + |x|))",
					By(
						tower,
						bounds,
						At(real_derivative.BoundedSecondDerivativeGrowth,
							value,
							a.TermAs[Fun[Real, Real]]("D(1)"),
							a.TermAs[Fun[Real, Real]]("D(2)"),
							M2)))
				borel := a.Have(
					"D(0), D(1) and D(2) are differentiable, hence Borel",
					"∀j:num. j ≤ 2 ⇒ real_measurable(𝕌, borel_sets(real_topology), D(j))",
					By(tower, At(derivativesBorel, D)))
				curvatureBound := a.Have(
					"M₂ bounds |D(2)(0)|, so it is nonnegative",
					"&0 ≤ M₂",
					ByArith(bounds.At(a.TermAs[Real]("&0"))))
				normal := a.Have(
					"the standard normal law is a probability",
					"probability_on(𝕌, borel_sets(real_topology), normal_distribution(&0, &1))",
					By(standardNormalMoments))
				onClockAt := a.Have(
					"on the clock event v(k) and c − V(k + 1) are "+
						"nonnegative, and both square roots square to at most c",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ Ω ∧ «withinClock»(x)"},
						Conclusion: "&0 ≤ v(k, x) ∧ " +
							"&0 ≤ c - «rowVariance»(k + 1, x) ∧ " +
							"real_sqrt(c - «rowVariance»(k, x)) * real_sqrt(c - «rowVariance»(k, x)) ≤ c ∧ " +
							"real_sqrt(c - «rowVariance»(k + 1, x)) * real_sqrt(c - «rowVariance»(k + 1, x)) ≤ c",
					},
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						parts := b.Conjuncts(
							b.Assume(),
							"x lies in Ω",
							"every variance is nonnegative at x",
							"every prefix of the variances lies in [0, c] at x")
						signs := b.Have(
							"v(k) and both prefixes are nonnegative at x, and both prefixes are at most c",
							"&0 ≤ v(k, x) ∧ "+
								"&0 ≤ «rowVariance»(k, x) ∧ "+
								"&0 ≤ c - «rowVariance»(k, x) ∧ "+
								"&0 ≤ «rowVariance»(k + 1, x) ∧ "+
								"&0 ≤ c - «rowVariance»(k + 1, x)",
							ByArith(parts[1].At(k), parts[2].At(k), parts[2].At(next), early, order))
						b.Show(
							"a square root of a nonnegative number squares back to it",
							ByArith(
								signs,
								real_sqrt.SqrtPowTwo.At(b.TermAs[Real]("c - «rowVariance»(k, x)")),
								real_sqrt.SqrtPowTwo.At(b.TermAs[Real]("c - «rowVariance»(k + 1, x)"))))
					}))
				rootSquares := a.Have(
					"so almost everywhere both square roots square to at most c",
					"measure_ae(Ω, "+
						"    S, "+
						"    μ, "+
						"    λx:A. real_sqrt(c - «rowVariance»(k, x)) * real_sqrt(c - «rowVariance»(k, x)) ≤ c) ∧ "+
						"measure_ae(Ω, "+
						"    S, "+
						"    μ, "+
						"    λx:A. real_sqrt(c - «rowVariance»(k + 1, x)) * real_sqrt(c - «rowVariance»(k + 1, x)) ≤ c)",
					By(
						onClock,
						onClockAt,
						measure_space.AEMono.At(Ω, S, μ, clock,
							a.TermAs[Fun[A, Bool]](
								"λx:A. real_sqrt(c - «rowVariance»(k, x)) * real_sqrt(c - «rowVariance»(k, x)) ≤ c")),
						measure_space.AEMono.At(Ω, S, μ, clock,
							a.TermAs[Fun[A, Bool]](
								"λx:A. real_sqrt(c - «rowVariance»(k + 1, x)) * real_sqrt(c - «rowVariance»(k + 1, x)) ≤ c"))))
				smoothedK := a.Have(
					"Φ(k) is integrable",
					"real_integrable(Ω, S, μ, «smoothed»(k))",
					By(
						probability,
						partialInS,
						roots,
						borel,
						growth,
						rootSquares,
						At(smoothedIntegrable, Ω, S, μ, partialK, rootK, value, K, c)))
				smoothedNext := a.Have(
					"so is Φ(k + 1)",
					"real_integrable(Ω, S, μ, «smoothed»(k + 1))",
					By(
						probability,
						partialNextInS,
						roots,
						borel,
						growth,
						rootSquares,
						At(smoothedIntegrable, Ω, S, μ, partialNext, rootNext, value, K, c)))
				slopeKnown := a.Have(
					"A is known at F(k)",
					"real_measurable(Ω, F(k), «derivativeAverage»(1, k))",
					By(
						atK,
						normal,
						partialAtK,
						rootNextAtK,
						borel.At(a.TermAs[Nat]("1")),
						At(gaussianAverageMeasurable,
							Ω, fieldK, μ, gaussian, partialK, rootNext, a.TermAs[Fun[Real, Real]]("D(1)"))))
				curvatureKnown := a.Have(
					"so is B",
					"real_measurable(Ω, F(k), «derivativeAverage»(2, k))",
					By(
						atK,
						normal,
						partialAtK,
						rootNextAtK,
						borel.At(a.TermAs[Nat]("2")),
						At(gaussianAverageMeasurable,
							Ω, fieldK, μ, gaussian, partialK, rootNext, a.TermAs[Fun[Real, Real]]("D(2)"))))
				slopeInS := a.Have(
					"A is S-measurable",
					"real_measurable(Ω, S, «derivativeAverage»(1, k))",
					By(inside, slopeKnown, measurable_function.RealMeasurableSourceMono.At(Ω, fieldK, S, slope)))
				slopeSquare := a.Have(
					"A is square-integrable, D(1) growing at most linearly",
					"real_integrable(Ω, S, μ, λx:A. «derivativeAverage»(1, k, x) * «derivativeAverage»(1, k, x))",
					By(
						probability,
						partialInS,
						roots,
						borel.At(a.TermAs[Nat]("1")),
						growth,
						rootSquares,
						At(smoothedSquareIntegrable,
							Ω, S, μ, partialK, rootNext, a.TermAs[Fun[Real, Real]]("D(1)"), K, c)))
				slopeTerm := a.Have(
					"so A·ξ(k) is integrable",
					"real_integrable(Ω, S, μ, λx:A. «derivativeAverage»(1, k, x) * ξ(k, x))",
					By(
						probability,
						slopeInS,
						term,
						slopeSquare,
						At(productSquareIntegrable, Ω, S, μ, slope, increment)))
				flat := a.Have(
					"|D(2)| ≤ M₂ read as a quadratic growth bound",
					"∀z:real. |D(2)(z)| ≤ M₂ + &0 * |z| + &0 * z * z",
					ByArith(bounds))
				curvaturePointwise := a.Have(
					"B averages D(2), so |B| ≤ M₂ everywhere",
					"∀x:A. x ∈ Ω ⇒ |«derivativeAverage»(2, k, x)| ≤ M₂",
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						b.Assume()
						b.Show(
							"average |D(2)| ≤ M₂ against the normal law",
							ByArith(
								borel.At(b.TermAs[Nat]("2")),
								curvatureBound,
								flat,
								At(quadraticGrowthAverage,
									b.TermAs[Fun[Real, Real]]("D(2)"),
									b.TermAs[Real]("«rowSum»(k, x)"),
									b.TermAs[Real]("real_sqrt(c - «rowVariance»(k + 1, x))"),
									M2,
									b.TermAs[Real]("&0"),
									b.TermAs[Real]("&0"))))
					}))
				curvatureBounded := a.Have(
					"so |B| ≤ M₂ almost everywhere",
					"measure_ae(Ω, S, μ, λx:A. |«derivativeAverage»(2, k, x)| ≤ M₂)",
					By(
						inside,
						curvaturePointwise,
						measure_space.AEOfEverywhere.At(
							Ω, S, μ, a.TermAs[Fun[A, Bool]]("λx:A. |«derivativeAverage»(2, k, x)| ≤ M₂"))))
				tailMoment := a.Have(
					"the tail of ξ(k)² is integrable, with integral the event integral over {ε < |ξ(k)|}",
					"real_integrable(Ω, S, μ, λx:A. COND(ε < |ξ(k, x)|, ξ(k, x) * ξ(k, x), &0)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. COND(ε < |ξ(k, x)|, ξ(k, x) * ξ(k, x), &0)) = "+
						"event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))",
					By(probability, term, At(tailIntegral, Ω, S, μ, increment, ε)))
				cost := a.Have(
					"the step's cost is integrable, its integral the step's budget",
					"real_integrable(Ω, S, μ, «stepCost»(k)) ∧ "+
						"measure_integral(Ω, S, μ, «stepCost»(k)) = "+
						"M₃ * ε / &6 * measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) + "+
						"M₂ * measure_integral(Ω, S, μ, λx:A. COND(ε < |ξ(k, x)|, ξ(k, x) * ξ(k, x), &0)) + "+
						"M₃ / &3 * measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))",
					By(
						inside,
						term,
						tailMoment,
						remainder,
						At(linearIntegral,
							Ω,
							S,
							μ,
							incrementSquare,
							tail,
							threeHalves,
							a.TermAs[Real]("M₃ * ε / &6"),
							M2,
							a.TermAs[Real]("M₃ / &3"))))
				pointwise := a.Have(
					"at a point of the clock event Φ(k + 1) − Φ(k) is its two Taylor terms up to the step's cost",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ Ω ∧ «withinClock»(x)"},
						Conclusion: "|«smoothed»(k + 1, x) - " +
							"«smoothed»(k, x) - " +
							"«derivativeAverage»(1, k, x) * ξ(k, x) - " +
							"&1 / &2 * («derivativeAverage»(2, k, x) * (ξ(k, x) * ξ(k, x) - v(k, x)))| ≤ " +
							"«stepCost»(k, x)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[A]("x")
						inClock := b.Assume()
						succ := b.Have(
							"suc(k) is k + 1",
							"suc(k) = k + 1",
							ByArith())
						extended := b.Have(
							"S(k + 1) adds ξ(k) to S(k)",
							"«rowSum»(k + 1, x) = «rowSum»(k, x) + ξ(k, x)",
							By(succ, real_sum.BelowClauses.At(b.TermAs[Fun[Nat, Real]]("λj:num. ξ(j, x)"))))
						spent := b.Have(
							"the variance left after k terms is that left after k + 1, plus v(k)",
							"c - «rowVariance»(k, x) = c - «rowVariance»(k + 1, x) + v(k, x)",
							ByArith(succ, real_sum.BelowClauses.At(b.TermAs[Fun[Nat, Real]]("λj:num. v(j, x)"))))
						signs := b.Have(
							"v(k) and the variance left after k + 1 terms are nonnegative at x",
							"&0 ≤ v(k, x) ∧ &0 ≤ c - «rowVariance»(k + 1, x)",
							By(onClockAt.At(x), inClock))
						b.Do(extended.Rw(), spent.Rw())
						b.Show(
							"scalarStep at p = S(k), h = ξ(k), r = c − V(k + 1), w = v(k)",
							By(
								tower,
								bounds,
								signs,
								positive,
								At(scalarStep,
									D,
									M2,
									M3,
									b.TermAs[Real]("«rowSum»(k, x)"),
									b.TermAs[Real]("ξ(k, x)"),
									b.TermAs[Real]("c - «rowVariance»(k + 1, x)"),
									b.TermAs[Real]("v(k, x)"),
									ε)))
					}))
				pointwiseAE := a.Have(
					"so the pointwise bound holds almost everywhere",
					"measure_ae(Ω, "+
						"    S, "+
						"    μ, "+
						"    λx:A. "+
						"        |«smoothed»(k + 1, x) - "+
						"        «smoothed»(k, x) - "+
						"        «derivativeAverage»(1, k, x) * ξ(k, x) - "+
						"        &1 / &2 * («derivativeAverage»(2, k, x) * (ξ(k, x) * ξ(k, x) - v(k, x)))| ≤ "+
						"        «stepCost»(k, x))",
					By(
						onClock,
						pointwise,
						measure_space.AEMono.At(Ω, S, μ, clock,
							a.TermAs[Fun[A, Bool]]("λx:A. "+
								"    |«smoothed»(k + 1, x) - "+
								"    «smoothed»(k, x) - "+
								"    «derivativeAverage»(1, k, x) * ξ(k, x) - "+
								"    &1 / &2 * («derivativeAverage»(2, k, x) * (ξ(k, x) * ξ(k, x) - v(k, x)))| ≤ "+
								"    «stepCost»(k, x)"))))
				cancel := a.Have(
					"A·ξ(k) and B·(ξ(k)² − v(k)) have expectation zero, leaving the integral of the cost",
					"|expectation(Ω, S, μ, «smoothed»(k + 1)) - expectation(Ω, S, μ, «smoothed»(k))| ≤ "+
						"measure_integral(Ω, S, μ, «stepCost»(k))",
					By(
						probability,
						term,
						slopeKnown,
						curvatureKnown,
						curvatureBounded,
						slopeTerm,
						smoothedK,
						smoothedNext,
						cost,
						pointwiseAE,
						At(conditionalCancellation,
							Ω,
							S,
							μ,
							fieldK,
							increment,
							variance,
							slope,
							curvature,
							a.TermAs[Fun[A, Real]]("«smoothed»(k)"),
							a.TermAs[Fun[A, Real]]("«smoothed»(k + 1)"),
							a.TermAs[Fun[A, Real]]("«stepCost»(k)"),
							M2)))
				a.Show(
					"the cost integrates to the step's budget",
					ByArith(cancel, cost, tailMoment))
			})

			// The steps telescope: |H(n) − H(0)| is at most the sum of the step bounds, by
			// induction on
			// n with the triangle inequality.
			telescope := ctx.Lemma(Statement{
				Binders: "∀H B:(num → real). ∀n:num.",
				Hypotheses: []string{
					"∀k:num. k < n ⇒ |H(k + 1) - H(k)| ≤ B(k)",
				},
				Conclusion: "|H(n) - H(0)| ≤ real_sum({k:num | k < n}, B)",
			}, func(a *Argument) {
				a.Induct("n")
				a.Base(
					"with no step the two ends agree and the sum is empty",
					func(b *Argument) {
						b.FixAs[Fun[Nat, Real]]("H")
						B := b.FixAs[Fun[Nat, Real]]("B")
						b.Assume()
						b.Show(
							"|H(0) − H(0)| = 0",
							ByArith(real_sum.BelowClauses.At(B)))
					})
				a.Step(
					"one more step adds its bound by the triangle inequality",
					func(b *Argument, below Fact) {
						H := b.FixAs[Fun[Nat, Real]]("H")
						B := b.FixAs[Fun[Nat, Real]]("B")
						steps := b.Assume()
						earlier := b.Have(
							"the first n steps keep their bounds",
							"∀k:num. k < n ⇒ |H(k + 1) - H(k)| ≤ B(k)",
							Derive(func(c *Argument) {
								k := c.FixAs[Nat]("k")
								kBelow := c.Assume()
								c.Show(
									"k < n < suc(n)",
									ByArith(steps.At(k), kBelow))
							}))
						upTo := b.Have(
							"the induction hypothesis at H and B",
							"|H(n) - H(0)| ≤ real_sum({k:num | k < n}, B)",
							By(below.At(H, B), earlier))
						last := b.Have(
							"the last step",
							"|H(n + 1) - H(n)| ≤ B(n) ∧ suc(n) = n + 1",
							ByArith(steps.At(b.TermAs[Nat]("n"))))
						b.Show(
							"the triangle inequality across H(n)",
							ByArith(upTo, last, real_sum.BelowClauses.At(B)))
					})
			})

			// The row's moment budget: the clock is nonnegative, the second moments sum to at most
			// c,
			// and the variance remainders v(k)·√v(k) are integrable and sum to at most c·√(ε² + L),
			// threeHalvesPowerSumBound with conditionalVarianceExcess at each k.
			rowMoments := ctx.Lemma(Statement{
				Binders: "∀Ω:set(A). " +
					"∀S:set(set(A)). " +
					"∀μ:(set(A) → extended_nonneg_real). " +
					"∀F:(num → set(set(A))). " +
					"∀n:num. " +
					"∀ξ v:(num → A → real). " +
					"∀c ε:real.",
				Hypotheses: []string{
					"probability_on(Ω, S, μ)",
					"filtration_on(Ω, S, F)",
					"∀k:num. " +
						"    k < n ⇒ " +
						"    real_measurable(Ω, F(k + 1), ξ(k)) ∧ " +
						"    is_cond_exp(Ω, S, μ, F(k), ξ(k), λx:A. &0) ∧ " +
						"    is_cond_exp(Ω, S, μ, F(k), λx:A. ξ(k, x) * ξ(k, x), v(k))",
					"measure_ae(Ω, S, μ, λx:A. «rowVariance»(n, x) ≤ c)",
				},
				Conclusion: "&0 ≤ c ∧ " +
					"real_sum({k:num | k < n}, λk:num. measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))) ≤ c ∧ " +
					"(∀k:num. k < n ⇒ real_integrable(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))) ∧ " +
					"real_sum({k:num | k < n}, " +
					"    λk:num. measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))) ≤ " +
					"c * real_sqrt(real_pow(ε, 2) + lindeberg_sum(Ω, S, μ, n, ξ, ε))",
			}, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				c, ε *Expr[Real],
				probability, isFiltration, row, budget Fact,
			) {
				nonnegative := a.Have(
					"every conditional variance is nonnegative almost everywhere",
					"measure_ae(Ω, S, μ, λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x))",
					By(probability, row, At(varianceNonnegative, Ω, S, μ, F, n, ξ, v)))
				clock := a.Have(
					"almost everywhere the variances are nonnegative and sum to at most c",
					"measure_ae(Ω, S, μ, λx:A. (∀k:num. k < n ⇒ &0 ≤ v(k, x)) ∧ «rowVariance»(n, x) ≤ c)",
					By(
						probability,
						nonnegative,
						budget,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.AEConjunction.At(Ω, S, μ,
							a.TermAs[Fun[A, Bool]]("λx:A. ∀k:num. k < n ⇒ &0 ≤ v(k, x)"),
							a.TermAs[Fun[A, Bool]]("λx:A. «rowVariance»(n, x) ≤ c"))))
				secondMoments := a.Have(
					"c is nonnegative and the second moments sum to at most c",
					"&0 ≤ c ∧ "+
						"real_sum({k:num | k < n}, λk:num. measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))) ≤ c",
					By(probability, row, clock, At(secondMomentsBudget, Ω, S, μ, F, n, ξ, v, c)))
				measurable := a.Have(
					"each ξ(k) is S-measurable",
					"∀k:num. k < n ⇒ real_measurable(Ω, S, ξ(k))",
					Derive(func(b *Argument) {
						k := b.FixAs[Nat]("k")
						below := b.Assume()
						b.Show(
							"F(k + 1) lies inside S",
							By(
								row.At(k),
								below,
								isFiltration,
								filtration.FiltrationDef.At(Ω, S, F),
								measurable_function.RealMeasurableSourceMono.At(
									Ω, b.TermAs[Set[Set[A]]]("F(k + 1)"), S, b.TermAs[Fun[A, Real]]("ξ(k)"))))
					}))
				field := a.Have(
					"S is a σ-algebra and μ a measure on it",
					"sigma_algebra_on(Ω, S) ∧ measure_on(Ω, S, μ)",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ)))
				excess := a.Conjuncts(
					a.Have(
						"each conditional variance is integrable, with its excess over ε² bounded by the Lindeberg tail",
						"(∀k:num. "+
							"    k < n ⇒ "+
							"    real_integrable(Ω, S, μ, v(k)) ∧ "+
							"    real_integrable(Ω, S, μ, λx:A. max(v(k, x) - real_pow(ε, 2), &0)) ∧ "+
							"    measure_integral(Ω, S, μ, λx:A. max(v(k, x) - real_pow(ε, 2), &0)) ≤ "+
							"    event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))) ∧ "+
							"real_measurable(Ω, "+
							"    S, "+
							"    λx:A. real_pow(ε, 2) + real_sum({k:num | k < n}, λk:num. max(v(k, x) - real_pow(ε, 2), &0)))",
						By(probability, row, measurable, At(varianceExcessRow, Ω, S, μ, F, n, ξ, v, ε))),
					"each variance and its excess are integrable, the excess below the Lindeberg tail",
					"ε² plus the summed excesses is measurable")
				variances := a.Have(
					"each v(k) is integrable, hence S-measurable",
					"∀k:num. k < n ⇒ real_measurable(Ω, S, v(k))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						below := b.Assume()
						b.Show(
							"an integrable function is measurable",
							By(
								excess[0],
								below,
								measure_integral.RealIntegrableDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("v(k)"))))
					}))
				roots := a.Have(
					"each √v(k) is S-measurable",
					"∀k:num. k < n ⇒ real_measurable(Ω, S, λx:A. real_sqrt(v(k, x)))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("k")
						below := b.Assume()
						b.Show(
							"the square root of a measurable function",
							By(field, variances, below, At(sqrtMeasurable, Ω, S, b.TermAs[Fun[A, Real]]("v(k)"))))
					}))
				excessRoot := a.Have(
					"√(ε² + Σ (v(k) − ε²)⁺) is S-measurable",
					"real_measurable(Ω, "+
						"    S, "+
						"    λx:A. "+
						"        real_sqrt(real_pow(ε, 2) + "+
						"            real_sum({k:num | k < n}, λk:num. max(v(k, x) - real_pow(ε, 2), &0))))",
					By(
						field,
						excess[1],
						At(sqrtMeasurable, Ω, S,
							a.TermAs[Fun[A, Real]](
								"λx:A. real_pow(ε, 2) + real_sum({k:num | k < n}, λk:num. max(v(k, x) - real_pow(ε, 2), &0))"))))
				square := a.Have(
					"ε² is nonnegative",
					"&0 ≤ real_pow(ε, 2)",
					ByArith())
				remainders := a.Have(
					"threeHalvesPowerSumBound at d = ε² and the Lindeberg tails",
					"(∀j:num. j < n ⇒ real_integrable(Ω, S, μ, λx:A. v(j, x) * real_sqrt(v(j, x)))) ∧ "+
						"real_sum({j:num | j < n}, "+
						"    λj:num. measure_integral(Ω, S, μ, λx:A. v(j, x) * real_sqrt(v(j, x)))) ≤ "+
						"c * "+
						"real_sqrt(real_pow(ε, 2) + "+
						"    real_sum({j:num | j < n}, "+
						"        λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))))",
					By(
						probability,
						square,
						secondMoments,
						variances,
						excess[0],
						roots,
						clock,
						excessRoot,
						At(threeHalvesPowerSumBound,
							Ω,
							S,
							μ,
							n,
							a.TermAs[Real]("real_pow(ε, 2)"),
							c,
							v,
							a.TermAs[Fun[Nat, Real]](
								"λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))"))))
				a.Show(
					"the tails sum to the Lindeberg sum",
					By(secondMoments, remainders, LindebergSumDef.At(Ω, S, μ, n, ξ, ε)))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				F *Arrow[Nat, Set[Set[A]]],
				n *Expr[Nat],
				ξ, v *Arrow2[Nat, A, Real],
				D *Arrow2[Nat, Real, Real],
				c, M2, M3, ε *Expr[Real],
				probability, rows, budget, tower, bounds, positive Fact,
			) {
				conditions := a.Conjuncts(
					a.Unfolded(rows, martingale.MartingaleDifferenceRowDef),
					"F is a filtration",
					"below n each increment is a martingale difference with conditional variance v")
				isFiltration, row := conditions[0], conditions[1]
				moments := a.Conjuncts(
					a.Have(
						"the row's moment budget",
						"&0 ≤ c ∧ "+
							"real_sum({k:num | k < n}, λk:num. measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))) ≤ c ∧ "+
							"(∀k:num. k < n ⇒ real_integrable(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))) ∧ "+
							"real_sum({k:num | k < n}, "+
							"    λk:num. measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))) ≤ "+
							"c * real_sqrt(real_pow(ε, 2) + lindeberg_sum(Ω, S, μ, n, ξ, ε))",
						By(probability, isFiltration, row, budget, At(rowMoments, Ω, S, μ, F, n, ξ, v, c, ε))),
					"c is nonnegative",
					"the second moments sum to at most c",
					"each variance remainder is integrable",
					"the variance remainders sum to at most c·√(ε² + L)")
				steps := a.Have(
					"each step of the replacement costs at most its budget",
					Statement{
						Binders:    "∀k:num.",
						Hypotheses: []string{"k < n"},
						Conclusion: "|expectation(Ω, S, μ, «smoothed»(k + 1)) - expectation(Ω, S, μ, «smoothed»(k))| ≤ " +
							"«stepBudget»(k)",
					},
					Derive(func(b *Argument) {
						k := b.FixAs[Nat]("k")
						below := b.Assume()
						b.Show(
							"stepBound at k",
							By(
								probability,
								isFiltration,
								row,
								budget,
								tower,
								bounds,
								positive,
								below,
								moments[2].At(k),
								At(stepBound, Ω, S, μ, F, n, ξ, v, D, c, M2, M3, ε, k)))
					}))
				telescoped := a.Have(
					"the steps telescope from Φ(0) to Φ(n)",
					"|expectation(Ω, S, μ, «smoothed»(n)) - expectation(Ω, S, μ, «smoothed»(0))| ≤ "+
						"real_sum({k:num | k < n}, «stepBudget»)",
					By(
						steps,
						At(telescope,
							a.TermAs[Fun[Nat, Real]]("λk:num. expectation(Ω, S, μ, «smoothed»(k))"),
							a.TermAs[Fun[Nat, Real]]("«stepBudget»"),
							n)))
				below := a.TermAs[Set[Nat]]("{k:num | k < n}")
				secondMoment := a.TermAs[Fun[Nat, Real]](
					"λk:num. measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))")
				tailMoment := a.TermAs[Fun[Nat, Real]](
					"λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))")
				remainder := a.TermAs[Fun[Nat, Real]](
					"λk:num. measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))")
				shares := a.Have(
					"the budgets sum to the three moment sums, each with its weight",
					"real_sum({k:num | k < n}, «stepBudget») = "+
						"M₃ * "+
						"ε / "+
						"&6 * "+
						"real_sum({k:num | k < n}, λk:num. measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))) + "+
						"M₂ * "+
						"real_sum({k:num | k < n}, "+
						"    λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))) + "+
						"M₃ / "+
						"&3 * "+
						"real_sum({k:num | k < n}, λk:num. measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x))))",
					ByArith(
						num_segment.FiniteBelowStrict.At(n),
						real_sum.ScalarLeft.At(a.TermAs[Real]("M₃ * ε / &6"), secondMoment, below),
						real_sum.ScalarLeft.At(M2, tailMoment, below),
						real_sum.ScalarLeft.At(a.TermAs[Real]("M₃ / &3"), remainder, below),
						real_sum.Add.At(
							a.TermAs[Fun[Nat, Real]](
								"λk:num. M₃ * ε / &6 * measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x))"),
							a.TermAs[Fun[Nat, Real]](
								"λk:num. M₂ * event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))"),
							below),
						real_sum.Add.At(
							a.TermAs[Fun[Nat, Real]](
								"λk:num. "+
									"    M₃ * ε / &6 * measure_integral(Ω, S, μ, λx:A. ξ(k, x) * ξ(k, x)) + "+
									"    M₂ * event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))"),
							a.TermAs[Fun[Nat, Real]](
								"λk:num. M₃ / &3 * measure_integral(Ω, S, μ, λx:A. v(k, x) * real_sqrt(v(k, x)))"),
							below)))
				lindeberg := a.Have(
					"the tail moments sum to the Lindeberg sum",
					"real_sum({k:num | k < n}, "+
						"    λk:num. event_integral(Ω, S, μ, {x:A | ε < |ξ(k, x)|}, λx:A. ξ(k, x) * ξ(k, x))) = "+
						"lindeberg_sum(Ω, S, μ, n, ξ, ε)",
					By(LindebergSumDef.At(Ω, S, μ, n, ξ, ε)))
				start := a.Have(
					"Φ(0) is the normal integral at √c, constant in x",
					"expectation(Ω, S, μ, «smoothed»(0)) = «gauss»(λy:real. D(0)(real_sqrt(c) * y))",
					By(probability, At(smoothedStart, Ω, S, μ, ξ, v, D, c)))
				weights := a.Have(
					"M₂ and M₃ bound absolute values at 0",
					"&0 ≤ M₂ ∧ &0 ≤ M₃",
					ByArith(bounds.At(a.TermAs[Real]("&0"))))
				cubic := a.Have(
					"so M₃·ε is nonnegative",
					"&0 ≤ M₃ * ε",
					ByArith(weights, positive))
				a.Show(
					"weight the three sums by their bounds",
					ByArith(telescoped, shares, lindeberg, start, moments[1], moments[3], weights, cubic))
			})
		}),
})}
