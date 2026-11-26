package central_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/probability/filtration"
	"github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	"github.com/euc-ai/xugo/library/proofs/probability/martingale/martingale"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/probability/variance_stopping"
	"github.com/euc-ai/xugo/library/proofs/probability/weak_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// rowErrorLimit — a triangular-array bound with a variance tail and a
// Lindeberg term tending to zero implies convergence against the test: at a
// common scale r the four errors add to at most B·(2C + 7)·r (smallRowError).
func rowErrorLimit(ctx *Script) *GoalStackNode {
	// smallRowError — a common small parameter controls the variance correction,
	// the exceptional probability, and the Lindeberg error.
	smallRowError := ctx.Lemma(Statement{
		Binders:    "∀B C r L p:real.",
		Hypotheses: []string{"&0 ≤ B", "&0 ≤ C", "&0 < r", "r ≤ &1", "&0 ≤ L", "L ≤ r ^ 2", "p ≤ r"},
		Conclusion: "B * (real_sqrt(&2 * «smallVarianceTolerance») + «smallVarianceTolerance») * C + " +
			"&4 * B * p + " +
			"B * r / &6 * «smallCap» + " +
			"B * L + " +
			"B / &3 * «smallCap» * «smallNoise» ≤ " +
			"B * (&2 * C + &7) * r",
		Abbrev: Abbrev{
			{Name: "smallCap", Text: "&1 + r ^ 2 / &2"},
			{Name: "smallNoise", Text: "real_sqrt(r ^ 2 + L)"},
			{Name: "smallVarianceTolerance", Text: "r ^ 2 / &2"},
		},
	}, func(a *Argument, B, C, r, L, p *Expr[Real], estimates Fact) {
		twiceVariance := a.TermAs[Real]("&2 * «smallVarianceTolerance»")
		smoothingVariance := a.TermAs[Real]("r ^ 2 + L")
		cap := a.TermAs[Real]("«smallCap»")
		noise := a.TermAs[Real]("«smallNoise»")
		twice := a.TermAs[Real]("&2 * r")
		two := a.TermAs[Real]("&2")
		root := a.Have(
			"the variance tolerance has square root r after doubling",
			"real_sqrt(&2 * «smallVarianceTolerance») = r",
			ByArith(estimates, real_sqrt.SqrtUnique.At(twiceVariance, r)))
		capBounds := a.Have(
			"the variance tolerance is at most r and the cap is at most two",
			"&0 ≤ «smallVarianceTolerance» ∧ «smallVarianceTolerance» ≤ r ∧ &0 ≤ «smallCap» ∧ «smallCap» ≤ &2",
			ByArith(estimates))
		noiseBounds := a.Have(
			"the noise term is at most twice r",
			"&0 ≤ «smallNoise» ∧ «smallNoise» ≤ &2 * r",
			ByArith(
				estimates,
				real_sqrt.SqrtNonneg.At(smoothingVariance),
				real_sqrt.SqrtPowTwo.At(smoothingVariance)))
		coefficients := a.Have(
			"the two comparison coefficients are nonnegative",
			"&0 ≤ B * C ∧ &0 ≤ B * r",
			ByArith(estimates))
		lindeberg := a.Have(
			"the Lindeberg mass is at most r",
			"L ≤ r",
			ByArith(estimates))
		cappedNoise := a.Have(
			"the capped noise is at most four times r",
			"«smallCap» * «smallNoise» ≤ &4 * r",
			ByArith(noiseBounds, capBounds, real_order_ring.LessEqMul2.At(cap, two, noise, twice)))
		gaussian := a.Have(
			"the Gaussian correction costs at most twice B C r",
			"(B * C) * (r + «smallVarianceTolerance») ≤ (B * C) * (&2 * r)",
			ByArith(coefficients, capBounds))
		smallTerms := a.Have(
			"the cap at most doubles the small-summand error",
			"B * r / &6 * «smallCap» ≤ B * r / &3",
			ByArith(coefficients, capBounds))
		largeTerms := a.Have(
			"the capped noise determines the remaining smoothing error",
			"B / &3 * «smallCap» * «smallNoise» ≤ &4 * B * r / &3",
			ByArith(cappedNoise, estimates))
		a.Show(
			"the total is bounded by B(2C + 7)r",
			ByArith(
				root,
				lindeberg,
				cappedNoise,
				smallTerms,
				gaussian,
				largeTerms,
				noiseBounds,
				coefficients,
				capBounds,
				estimates))
	})
	return ctx.Lemma(Statement{
		Binders: "∀a:(num → real). ∀l B C:real. ∀L P:(real → num → real).",
		Hypotheses: []string{
			"&0 ≤ B",
			"&0 ≤ C",
			"∀ε:real. &0 < ε ⇒ (λn:num. L(ε, n)) ⟶ &0",
			"∀δ ρ:real. &0 < δ ∧ &0 < ρ ⇒ ∃N:num. ∀n:num. N ≤ n ⇒ P(δ, n) ≤ ρ",
			"∀n:num. ∀δ ε:real. &0 < δ ∧ &0 < ε ⇒ &0 ≤ L(ε, n) ∧ |a(n) - l| ≤ «rowError»(n, δ, ε)",
		},
		Conclusion: "a ⟶ l",
		Abbrev: Abbrev{
			{Name: "rowError", Text: "λn:num. λδ:real. λε:real. " +
				"    B * (real_sqrt(&2 * δ) + δ) * C + " +
				"    &4 * B * P(δ, n) + " +
				"    B * ε / &6 * (&1 + δ) + " +
				"    B * L(ε, n) + " +
				"    B / &3 * (&1 + δ) * real_sqrt(ε ^ 2 + L(ε, n))"},
		},
	}, func(
		arg *Argument,
		a *Arrow[Nat, Real],
		l, B, C *Expr[Real],
		L, P *Arrow2[Real, Nat, Real],
		hypotheses Fact,
	) {
		arg.Do(Simp(Fwd(real_sequences.RealConvergesToDef)))
		target := arg.FixAs[Real]("η")
		positive := arg.Assume()
		_, totalCoefficient := arg.LetAs[Real]("Q", "&1 + B * (&2 * C + &7)")
		r, tolerance := arg.LetAs[Real]("r", "min(&1, η / (&2 * Q))")
		twiceCoefficient := arg.TermAs[Real]("&2 * Q")
		denominatorPositive := arg.Have(
			"the chosen denominator is positive",
			"&0 < &2 * Q",
			ByArith(totalCoefficient, hypotheses))
		positiveQuotient := arg.Have(
			"the target tolerance gives a positive quotient",
			"&0 < η / (&2 * Q)",
			By(positive, denominatorPositive, real_order_field.DivPos.At(target, twiceCoefficient)))
		radius := arg.Have(
			"the common scale is positive and at most one",
			"&0 < r ∧ r ≤ &1 ∧ r ≤ η / (&2 * Q)",
			ByArith(tolerance, positiveQuotient))
		scaled := arg.Have(
			"the common scale times the denominator is within the target",
			"r * (&2 * Q) ≤ η",
			By(denominatorPositive, radius, real_order_field.LessEqDivMulLeft.At(r, target, twiceCoefficient)))
		choices := arg.Have(
			"the scaled error is small and both thresholds are positive",
			"B * (&2 * C + &7) * r < η ∧ &0 < r ^ 2 / &2 ∧ &0 < r ^ 2",
			ByArith(totalCoefficient, scaled, positive, radius, real_order_ring.MulPos.At(r, r)))
		_, massTail := arg.ObtainAs[Nat](
			"the variance tail is eventually within the common scale",
			"∃N₁:num. ∀n:num. N₁ ≤ n ⇒ P(r ^ 2 / &2, n) ≤ r",
			By(choices, radius, hypotheses))
		_, lindebergTail := arg.ObtainAs[Nat](
			"the Lindeberg mass is eventually within the squared scale",
			"∃N₂:num. ∀n:num. N₂ ≤ n ⇒ |L(r, n) - &0| < r ^ 2",
			By(
				choices,
				radius,
				hypotheses,
				real_sequences.RealConvergesToDef.At(
					arg.TermAs[Fun[Nat, Real]]("λn:num. L(r, n)"), arg.TermAs[Real]("&0"))))
		arg.Take(arg.TermAs[Nat]("max(N₁, N₂)"))
		n := arg.FixAs[Nat]()
		beyond := arg.Assume()
		both := arg.Have(
			"either tail estimate now applies",
			"N₁ ≤ n ∧ N₂ ≤ n",
			ByArith(beyond))
		tails := arg.Have(
			"the variance and Lindeberg tails meet their respective tolerances",
			"L(r, n) ≤ r ^ 2 ∧ P(r ^ 2 / &2, n) ≤ r",
			ByArith(both, massTail.At(n), lindebergTail.At(n)))
		distance := arg.Have(
			"use the trial scales in the row bound",
			"&0 ≤ L(r, n) ∧ |a(n) - l| ≤ «rowError»(n, r ^ 2 / &2, r)",
			By(radius, choices, hypotheses))
		bound := arg.Have(
			"sum the bounds on the four error sources",
			"«rowError»(n, r ^ 2 / &2, r) ≤ B * (&2 * C + &7) * r",
			By(
				radius,
				hypotheses,
				tails,
				distance,
				At(smallRowError, B, C, r,
					arg.TermAs[Real]("L(r, n)"), arg.TermAs[Real]("P(r ^ 2 / &2, n)"))))
		arg.Show(
			"the test expectation is within the requested tolerance",
			ByArith(bound, distance, choices))
	})
}

// measurableRowSum — the sum of a row adapted to a filtration on S is
// S-measurable: each increment is measurable at a level inside S.
func measurableRowSum(ctx *Script) *GoalStackNode {
	return ctx.Lemma(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀F:(num → set(set(A))). ∀n:num. ∀ξ:(num → A → real).",
		Hypotheses: []string{
			"filtration_on(Ω, S, F)",
			"∀k:num. k < n ⇒ real_measurable(Ω, F(k + 1), ξ(k))",
		},
		Conclusion: "real_measurable(Ω, S, «rowTotal»(ξ, n))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		F *Arrow[Nat, Set[Set[A]]],
		n *Expr[Nat],
		ξ *Arrow2[Nat, A, Real],
		isFiltration, adapted Fact,
	) {
		levels := a.Have(
			"S is a σ-algebra containing every level of the filtration",
			"sigma_algebra_on(Ω, S) ∧ (∀k:num. F(k) ⊆ S)",
			By(isFiltration, filtration.FiltrationDef.At(Ω, S, F)))
		increments := a.Have(
			"each increment is S-measurable",
			"∀k:num. k < n ⇒ real_measurable(Ω, S, ξ(k))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]()
				inRow := b.Assume()
				b.Show(
					"measurability passes up from F(k + 1) to S",
					By(
						inRow,
						adapted,
						levels,
						measurable_function.RealMeasurableSourceMono.At(
							Ω,
							b.TermAs[Set[Set[A]]]("F(k + 1)"),
							S,
							b.TermAs[Fun[A, Real]]("ξ(k)"))))
			}))
		a.Show(
			"a finite sum of measurable functions is measurable",
			By(levels, increments, measurable_function.RealMeasurableSum.At(Ω, S, ξ, n)))
	})
}

// MartingaleCentralLimit — the martingale central limit theorem: the row sums
// of a triangular array of martingale differences, whose conditional variances
// sum to one in measure and whose Lindeberg sums vanish, converge weakly to the
// standard normal. Against a bounded test with three bounded derivatives, each
// row is within variance_stopping.MartingaleLindebergApproximateBound of the standard normal; the
// bound vanishes as δ and the Lindeberg level shrink (rowErrorLimit), and such
// tests decide weak convergence (WeakConvergenceSmoothTests).
var MartingaleCentralLimit = martingaleCentralLimitThm{family.Add(registry.ProofEntry{
	Name: "MartingaleCentralLimit",
	Key:  "prop_444d55ff48d7bf9f",
	Reading: "This is the Brown–Billingsley form: the conditional variances sum to 1 in " +
		"measure, and the Lindeberg condition is on expectations, not conditional ones. The " +
		"form with the conditional Lindeberg condition in measure (Hall–Heyde, McLeish) is " +
		"MartingaleCentralLimitConditional. Row n has its own filtration F(n) and its own " +
		"length K(n); the filtrations of different rows are not asked to be nested, the limit " +
		"of the conditional variances being a constant. A row of independent centred variables " +
		"with the σ-algebras of the earlier ones as filtration is the classical triangular array.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀F:(num → num → set(set(A))). " +
			"∀K:(num → num). " +
			"∀ξ v:(num → num → A → real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"∀n:num. martingale_difference_row(Ω, S, μ, F(n), K(n), ξ(n), v(n))",
			"converges_in_measure(Ω, " +
				"    μ, " +
				"    λn:num. λx:A. real_sum({k:num | k < K(n)}, λk:num. v(n, k, x)), " +
				"    λx:A. &1)",
			"∀ε:real. &0 < ε ⇒ (λn:num. lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε)) ⟶ &0",
		},
		Conclusion: "weakly_converges(real_topology, " +
			"    λn:num. pushforward_measure(Ω, μ, λx:A. real_sum({k:num | k < K(n)}, λk:num. ξ(n, k, x))), " +
			"    normal_distribution(&0, &1))",
		Abbrev: Abbrev{
			{Name: "rowTotal", Text: "λξ:(num → A → real). λn:num. λx:A. Σ_{k<n} ξ(k, x)"},
			{Name: "standardNormal", Text: "normal_distribution(&0, &1)"},
			{Name: "normalAbsMoment", Text: "expectation(𝕌, " +
				"    borel_sets(real_topology), " +
				"    «standardNormal», " +
				"    λy:real. |y|)"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		rowSumMeasurable := measurableRowSum(ctx)
		rowErrorTends := rowErrorLimit(ctx)
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			F *Arrow2[Nat, Nat, Set[Set[A]]],
			K *Arrow[Nat, Nat],
			ξ, v *Arrow2[Nat, Nat, Fun[A, Real]],
			probability, rows, variances, lindeberg Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			borel := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			normal := a.TermAs[Fun[Set[Real], ExtendedNonnegReal]]("«standardNormal»")
			absolute := a.TermAs[Fun[Real, Real]]("λy:real. |y|")
			rowConditions := a.Unfolded(rows, martingale.MartingaleDifferenceRowDef)
			measurableRowSums := a.Have(
				"every row sum is measurable",
				"∀n:num. real_measurable(Ω, S, λx:A. Σ_{k<K(n)} ξ(n, k, x))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Show(
						"each row is adapted to its own filtration",
						By(
							rowConditions.At(n),
							At(
								rowSumMeasurable,
								Ω,
								S,
								b.TermAs[Fun[Nat, Set[Set[A]]]]("F(n)"),
								b.TermAs[Nat]("K(n)"),
								b.TermAs[Fun2[Nat, A, Real]]("ξ(n)"))))
				}))
			normalProbability := a.Have(
				"the standard normal is a Borel probability",
				"probability_on(𝕌, borel_sets(real_topology), «standardNormal»)",
				ByArith(normal_distribution.NormalDistributionProbability))
			normalMeasure := a.Have(
				"the standard normal is a measure on the Borel σ-algebra",
				"measure_on(𝕌, borel_sets(real_topology), «standardNormal») ∧ "+
					"sigma_algebra_on(𝕌, borel_sets(real_topology))",
				By(
					normalProbability,
					probability_space.ProbabilityOnDef.At(line, borel, normal),
					borel_function.LineBorelSigmaAlgebra))
			rowDistributions := a.Have(
				"the law of each row sum is a Borel probability",
				"∀n:num. "+
					"    probability_on(𝕌, "+
					"        borel_sets(real_topology), "+
					"        pushforward_measure(Ω, μ, λx:A. Σ_{k<K(n)} ξ(n, k, x)))",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					rowSum := b.TermAs[Fun[A, Real]]("λx:A. Σ_{k<K(n)} ξ(n, k, x)")
					b.Show(
						"a measurable map pushes a probability forward to a probability",
						By(
							measurableRowSums.At(n),
							probability,
							normalMeasure,
							random_variable.DistributionProbability.At(Ω, S, μ, line, borel, rowSum),
							measurable_function.RealMeasurableDef.At(Ω, S, rowSum)))
				}))
			testConvergence := a.Have(
				"the row laws converge against every bounded test with three derivatives",
				Statement{
					Binders: "∀D:(num → real → real).",
					Hypotheses: []string{
						"(∀k:num. ∀y:real. k ≤ 2 ⇒ real_derivative_at(D(k), y, D(k + 1)(y)))",
						"(∃B:real. ∀k:num. ∀y:real. k ≤ 3 ⇒ |D(k)(y)| ≤ B)",
					},
					Conclusion: "(λn:num. " +
						"    expectation(𝕌, " +
						"        borel_sets(real_topology), " +
						"        pushforward_measure(Ω, μ, λx:A. Σ_{k<K(n)} ξ(n, k, x)), " +
						"        D(0))) ⟶ " +
						"expectation(𝕌, borel_sets(real_topology), «standardNormal», D(0))",
				},
				Derive(func(b *Argument) {
					D := b.FixAs[Fun2[Nat, Real, Real]]()
					smooth := b.Assume()
					test := b.Conjuncts(
						smooth,
						"the test carries a tower of three derivatives",
						"the test and its derivatives are uniformly bounded")
					test0 := b.TermAs[Fun[Real, Real]]("D(0)")
					testContinuous := b.Have(
						"the first derivative makes the test continuous",
						"∀y:real. real_continuous_at(D(0), y)",
						Derive(func(c *Argument) {
							y := c.FixAs[Real]()
							c.Show(
								"a differentiable function is continuous",
								By(test[0], real_derivative.DerivativeContinuous.At(test0, y, c.TermAs[Real]("D(1)(y)"))))
						}))
					testBorel := b.Have(
						"continuous on the line, the test is Borel",
						"real_measurable(𝕌, borel_sets(real_topology), D(0))",
						By(
							testContinuous,
							real_continuous.ContinuousAtOn.At(test0, line),
							borel_function.ContinuousBorelMeasurable.At(test0)))
					arrayMeasure := b.Have(
						"the array's probability law is a measure",
						"measure_on(Ω, S, μ)",
						By(probability, probability_space.ProbabilityOnDef.At(Ω, S, μ)))
					pushforwardScores := b.Have(
						"the expectation under each row law is the expectation of the test at the row sum",
						"∀n:num. "+
							"    expectation(𝕌, "+
							"        borel_sets(real_topology), "+
							"        pushforward_measure(Ω, μ, λx:A. Σ_{k<K(n)} ξ(n, k, x)), "+
							"        D(0)) = "+
							"    expectation(Ω, S, μ, λx:A. D(0)(Σ_{k<K(n)} ξ(n, k, x)))",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]()
							rowSum := c.TermAs[Fun[A, Real]]("λx:A. Σ_{k<K(n)} ξ(n, k, x)")
							c.Show(
								"change variables along the row sum",
								By(
									measurableRowSums.At(n),
									normalMeasure,
									arrayMeasure,
									testBorel,
									random_variable.ExpectationPushforward.At(Ω, S, μ, line, borel, rowSum, test0),
									measurable_function.RealMeasurableDef.At(Ω, S, rowSum),
									functions.ComposeApply.At(test0, rowSum)))
						}))
					B, bounded := b.UnpackAs[Real](test[1], "B")
					testBoundNonnegative := b.Have(
						"the uniform bound is nonnegative",
						"&0 ≤ B",
						ByArith(Normalized, bounded.At(b.TermAs[Nat]("0"), b.TermAs[Real]("&0"))))
					normalMomentNonnegative := b.Have(
						"the first absolute normal moment is nonnegative",
						"&0 ≤ «normalAbsMoment»",
						ByArith(
							Normalized,
							probability_space.ExpectationDef.At(line, borel, normal, absolute),
							measure_integral.IntegralNonneg.At(line, borel, normal, absolute)))
					varianceTail := b.Have(
						"the probability that a row's clock misses one by more than δ tends to zero",
						Statement{
							Binders:    "∀δ ρ:real.",
							Hypotheses: []string{"&0 < δ", "&0 < ρ"},
							Conclusion: "∃N:num. ∀n:num. " +
								"    N ≤ n ⇒ extended_to_real(μ({x:A | x ∈ Ω ∧ δ < |Σ_{k<K(n)} v(n, k, x) - &1|})) ≤ ρ",
						},
						Derive(func(c *Argument) {
							δ := c.FixAs[Real]()
							ρ := c.FixAs[Real]()
							positive := c.Assume()
							c.Show(
								"convergence in measure bounds the deviation masses",
								By(
									positive,
									variances,
									integral_convergence.ConvergesInMeasureDeviationMass.At(
										Ω,
										μ,
										c.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. Σ_{k<K(n)} v(n, k, x)"),
										c.TermAs[Fun[A, Real]]("λx:A. &1"),
										δ,
										ρ)))
						}))
					rowError := b.Have(
						"each row error is controlled by the bad clock event and the Lindeberg sum",
						Statement{
							Binders:    "∀n:num. ∀δ ε:real.",
							Hypotheses: []string{"&0 < δ", "&0 < ε"},
							Conclusion: "&0 ≤ lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε) ∧ " +
								"|expectation(Ω, S, μ, λx:A. D(0)(Σ_{k<K(n)} ξ(n, k, x))) - " +
								"expectation(𝕌, borel_sets(real_topology), «standardNormal», D(0))| ≤ " +
								"B * (real_sqrt(&2 * δ) + δ) * «normalAbsMoment» + " +
								"&4 * B * extended_to_real(μ({x:A | x ∈ Ω ∧ δ < |Σ_{k<K(n)} v(n, k, x) - &1|})) + " +
								"B * ε / &6 * (&1 + δ) + " +
								"B * lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε) + " +
								"B / &3 * (&1 + δ) * real_sqrt(ε ^ 2 + lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε))",
						},
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]()
							δ := c.FixAs[Real]()
							ε := c.FixAs[Real]()
							positive := c.Assume()
							rowLength := c.TermAs[Nat]("K(n)")
							increments := c.TermAs[Fun2[Nat, A, Real]]("ξ(n)")
							c.Show(
								"the approximate-variance bound for the row, whose Lindeberg sum is nonnegative",
								ByArith(
									Normalized,
									probability,
									rows.At(n),
									test[0],
									bounded,
									positive,
									lindeberg_bound.LindebergSumNonnegative.At(Ω, S, μ, rowLength, increments, ε),
									variance_stopping.MartingaleLindebergApproximateBound.At(
										Ω,
										S,
										μ,
										c.TermAs[Fun[Nat, Set[Set[A]]]]("F(n)"),
										rowLength,
										increments,
										c.TermAs[Fun2[Nat, A, Real]]("v(n)"),
										D,
										B,
										δ,
										ε)))
						}))
					b.Show(
						"the row errors vanish as δ and the Lindeberg level shrink",
						Simp(Fwd(pushforwardScores)),
						By(
							lindeberg,
							testBoundNonnegative,
							normalMomentNonnegative,
							varianceTail,
							rowError,
							At(
								rowErrorTends,
								b.TermAs[Fun[Nat, Real]]("λn:num. expectation(Ω, S, μ, λx:A. D(0)(Σ_{k<K(n)} ξ(n, k, x)))"),
								b.TermAs[Real]("expectation(𝕌, borel_sets(real_topology), «standardNormal», D(0))"),
								B,
								b.TermAs[Real]("«normalAbsMoment»"),
								b.TermAs[Fun2[Real, Nat, Real]]("λε:real. λn:num. lindeberg_sum(Ω, S, μ, K(n), ξ(n), ε)"),
								b.TermAs[Fun2[Real, Nat, Real]](
									"λδ:real. λn:num. extended_to_real(μ({x:A | x ∈ Ω ∧ δ < |Σ_{k<K(n)} v(n, k, x) - &1|}))"))))
				}))
			a.Show(
				"smooth tests decide weak convergence to the standard normal",
				By(
					testConvergence,
					rowDistributions,
					normalMeasure,
					weak_convergence.WeakConvergenceSmoothTests.At(
						a.TermAs[Fun2[Nat, Set[Real], ExtendedNonnegReal]](
							"λn:num. pushforward_measure(Ω, μ, λx:A. Σ_{k<K(n)} ξ(n, k, x))"),
						normal)))
		})
	}),
})}
