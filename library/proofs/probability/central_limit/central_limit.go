// central_limit.go — the central limit theorem for independent identically distributed
// variables, and what it says of their distribution functions.

package central_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/borel_function"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/independence"
	"github.com/euc-ai/xugo/library/proofs/probability/lindeberg_bound"
	"github.com/euc-ai/xugo/library/proofs/probability/normal_distribution"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/probability/random_variable"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// CentralLimit — the central limit theorem for independent identically distributed variables
// (Lindeberg–Lévy): their sums, centred and scaled by σ·√n, converge weakly to the standard
// normal distribution. LindebergFeller applies to the rows ξ(n, k) = (X(k) − m)/(σ·√n), k < n:
// each ξ(n, k) is a Borel function of X(k), so row n is independent; X(k) has the moments of
// X(0), so ξ(n, k) is centred with variance 1/n and the variances of row n sum to 1 from n = 1
// on. By identical distribution every Lindeberg term of row n is the one of ξ(n, 0), so from
// n = 1 on row n's Lindeberg sum at ε is E[(X(0) − m)²; ε·σ·√n < |X(0) − m|]/σ², which tends
// to 0 as the threshold grows. The row sums are the normalized sums. The claims spell ξ(n, k)
// as «row»(n, k).
var CentralLimit = centralLimitThm{family.Add(registry.ProofEntry{
	Name: "CentralLimit",
	Key:  "prop_4c1a5cd228ffd00",
	Reading: "The variables are indexed by every natural number. The term at n = 0 is " +
		"the distribution of the constant 0, real division by zero being 0; a limit does not " +
		"read it. σ is the standard deviation, asked positive: the variance alone leaves its " +
		"sign open. Square-integrability of X(0) is asked beside the variance, which is total.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀X:(num → A → real). " +
			"∀m σ:real.",
		Hypotheses: []string{
			"independent_variable_family(Ω, S, μ, 𝕌, X)",
			"∀n:num. identically_distributed(Ω, μ, X(n), X(0))",
			"real_integrable(Ω, S, μ, λx:A. X(0, x) * X(0, x))",
			"expectation(Ω, S, μ, X(0)) = m",
			"variance(Ω, S, μ, X(0)) = σ * σ",
			"&0 < σ",
		},
		Conclusion: "weakly_converges(real_topology, " +
			"    λn:num. pushforward_measure(Ω, μ, «normalizedSum»(n)), " +
			"    normal_distribution(&0, &1))",
		Abbrev: Abbrev{
			{Name: "row", Text: "λn:num. λk:num. λx:A. (X(k, x) - m) / (σ * real_sqrt(&n))"},
			{Name: "tailMoment", Text: "λε:real. λn:num. " +
				"    event_integral(Ω, " +
				"        S, " +
				"        μ, " +
				"        {x:A | ε * (σ * real_sqrt(&n)) < |X(0, x) - m|}, " +
				"        λx:A. (X(0, x) - m) * (X(0, x) - m))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		// An affine map y ↦ (y − m)/c is continuous, hence Borel.
		affineBorel := ctx.Lemma("∀m c:real. "+
			"    real_measurable(𝕌, borel_sets(real_topology), λy:real. (y - m) / c)",
			func(a *Argument, m, c *Expr[Real]) {
				line := a.TermAs[Set[Real]]("𝕌")
				quotient := a.Have(
					"dividing by c is multiplying by real_inv(c)",
					"(λy:real. (y - m) / c) = (λy:real. (y - m) * real_inv(c))",
					Funext(),
					ByArith())
				a.Show(
					"y − m and the constant real_inv(c) are continuous, so is their product, and it is Borel",
					By(
						quotient,
						real_continuous.ContinuousOnId,
						real_continuous.ContinuousOnConst,
						real_continuous.ContinuousOnSub.At(
							a.TermAs[Fun[Real, Real]]("λy:real. y"), a.TermAs[Fun[Real, Real]]("λy:real. m"), line),
						real_continuous.ContinuousOnMul.At(
							a.TermAs[Fun[Real, Real]]("λy:real. y - m"),
							a.TermAs[Fun[Real, Real]]("λy:real. real_inv(c)"),
							line),
						borel_function.ContinuousBorelMeasurable))
			})
		// A square-integrable variable Y with mean m and variance v, standardized by c: (Y − m)/c is
		// the affine image real_inv(c)·Y − m·real_inv(c), so it is centred by the linearity of the
		// expectation, and square-integrable with variance real_inv(c)²·v by VarianceAffine.
		standardized := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀Y:(A → real). " +
				"∀m v c:real.",
			Hypotheses: []string{
				"probability_on(Ω, S, μ)",
				"real_measurable(Ω, S, Y)",
				"real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x))",
				"expectation(Ω, S, μ, Y) = m",
				"variance(Ω, S, μ, Y) = v",
			},
			Conclusion: "expectation(Ω, S, μ, λx:A. (Y(x) - m) / c) = &0 ∧ " +
				"real_integrable(Ω, S, μ, λx:A. (Y(x) - m) / c * ((Y(x) - m) / c)) ∧ " +
				"variance(Ω, S, μ, λx:A. (Y(x) - m) / c) = v / (c * c)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			Y *Arrow[A, Real],
			m, v, c *Expr[Real],
			probability, measurable, square, mean, variance Fact,
		) {
			inverse := a.TermAs[Real]("real_inv(c)")
			shift := a.TermAs[Real]("-(m * real_inv(c))")
			constant := a.TermAs[Fun[A, Real]]("λx:A. -(m * real_inv(c))")
			integrable := a.Have(
				"a probability measure is a measure, and Y, being square-integrable, is integrable",
				"measure_on(Ω, S, μ) ∧ real_integrable(Ω, S, μ, Y)",
				By(
					probability,
					measurable,
					square,
					probability_space.ProbabilityOnDef.At(Ω, S, μ),
					probability_space.SquareIntegrableIntegrable.At(Ω, S, μ, Y)))
			affine := a.Have(
				"(Y − m)/c is the affine image real_inv(c)·Y − m·real_inv(c)",
				"(λx:A. (Y(x) - m) / c) = (λx:A. real_inv(c) * Y(x) + -(m * real_inv(c)))",
				Funext(),
				ByArith())
			affineSquare := a.Have(
				"and its square is the square of that image",
				"(λx:A. (Y(x) - m) / c * ((Y(x) - m) / c)) = "+
					"(λx:A. (real_inv(c) * Y(x) + -(m * real_inv(c))) * (real_inv(c) * Y(x) + -(m * real_inv(c))))",
				Funext(),
				ByArith())
			centredMean := a.Have(
				"(Y − m)/c has mean real_inv(c)·m − m·real_inv(c) = 0, the integral being linear",
				"expectation(Ω, S, μ, λx:A. (Y(x) - m) / c) = &0",
				ByArith(
					mean,
					affine,
					integrable,
					probability,
					probability_space.ExpectationConstant.At(Ω, S, μ, shift),
					measure_integral.IntegrableScale.At(Ω, S, μ, Y, inverse),
					measure_integral.IntegralAdd.At(
						Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. real_inv(c) * Y(x)"), constant),
					measure_integral.IntegralScale.At(Ω, S, μ, Y, inverse),
					probability_space.ExpectationDef.At(
						Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. real_inv(c) * Y(x) + -(m * real_inv(c))")),
					probability_space.ExpectationDef.At(Ω, S, μ, Y),
					probability_space.ExpectationDef.At(Ω, S, μ, constant)))
			a.Show(
				"its square is integrable and its variance is real_inv(c)·real_inv(c)·v = v/(c·c)",
				ByArith(
					centredMean,
					affine,
					affineSquare,
					probability,
					measurable,
					square,
					variance,
					probability_space.VarianceAffine.At(Ω, S, μ, Y, inverse, shift)))
		})
		// Identically distributed variables have the same Lindeberg terms after a Borel map h: the
		// cut square y ↦ COND(ε < |h(y)|, h(y)², 0) is Borel, and an event integral is the
		// expectation of the cut integrand.
		tailTransfer := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀Y Z:(A → real). " +
				"∀h:(real → real). " +
				"∀ε:real.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"real_measurable(Ω, S, Y)",
				"real_measurable(Ω, S, Z)",
				"identically_distributed(Ω, μ, Y, Z)",
				"real_measurable(𝕌, borel_sets(real_topology), h)",
			},
			Conclusion: "event_integral(Ω, S, μ, {x:A | ε < |h(Y(x))|}, λx:A. h(Y(x)) * h(Y(x))) = " +
				"event_integral(Ω, S, μ, {x:A | ε < |h(Z(x))|}, λx:A. h(Z(x)) * h(Z(x)))",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			Y, Z *Arrow[A, Real],
			h *Arrow[Real, Real],
			ε *Expr[Real],
			space, measurableY, measurableZ, identical, borel Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			ray := a.Have(
				"|h| is Borel, so the event where it exceeds ε is a Borel set",
				"{y:real | y ∈ 𝕌 ∧ ε < |h(y)|} ∈ borel_sets(real_topology)",
				By(
					borel_function.LineBorelSigmaAlgebra,
					borel,
					measurable_function.RealMeasurableAbs.At(line, borelSets, h),
					measurable_function.RealMeasurableIffRay.At(
						line, borelSets, a.TermAs[Fun[Real, Real]]("λy:real. |h(y)|"))))
			everywhere := a.Have(
				"every real lies on the line",
				"{y:real | y ∈ 𝕌 ∧ ε < |h(y)|} = {y:real | ε < |h(y)|}",
				BySets())
			cut := a.Have(
				"so h² cut to that event is Borel",
				"real_measurable(𝕌, borel_sets(real_topology), λy:real. COND(ε < |h(y)|, h(y) * h(y), &0))",
				By(
					borel_function.LineBorelSigmaAlgebra,
					ray,
					everywhere,
					borel,
					measurable_function.RealMeasurableSquare.At(line, borelSets, h),
					measurable_function.RealMeasurableOnEvent.At(
						line,
						borelSets,
						a.TermAs[Set[Real]]("{y:real | ε < |h(y)|}"),
						a.TermAs[Fun[Real, Real]]("λy:real. h(y) * h(y)"))))
			a.Show(
				"each event integral is the expectation of the cut square at the variable, and these agree",
				By(
					space,
					measurableY,
					measurableZ,
					cut,
					identical,
					random_variable.IdenticallyDistributedExpectation.At(
						Ω, S, μ, Y, Z, a.TermAs[Fun[Real, Real]]("λy:real. COND(ε < |h(y)|, h(y) * h(y), &0)")),
					event_integral.EventIntegralDef,
					probability_space.ExpectationDef))
		})
		// Dividing a variable by r > 0 multiplies its threshold by r and its second moment beyond the
		// threshold by real_inv(r·r).
		tailRescaled := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀f:(A → real). " +
				"∀r ε:real.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"&0 < r",
			},
			Conclusion: "event_integral(Ω, S, μ, {x:A | ε < |f(x) / r|}, λx:A. f(x) / r * (f(x) / r)) = " +
				"event_integral(Ω, S, μ, {x:A | ε * r < |f(x)|}, λx:A. f(x) * f(x)) / (r * r)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow[A, Real],
			r, ε *Expr[Real],
			space, positive Fact,
		) {
			pointwise := a.Have(
				"ε < |f(x)/r| exactly when ε·r < |f(x)|, r being positive",
				"∀x:A. ε < |f(x) / r| ⇔ ε * r < |f(x)|",
				Derive(func(b *Argument) {
					b.FixAs[A]("x")
					b.Show(
						"clear the positive divisor r",
						ByArith(positive, real_order_field.LessThanDivMulLeft.At(ε, b.TermAs[Real]("|f(x)|"), r)))
				}))
			event := a.Have(
				"so the two events are one",
				"{x:A | ε < |f(x) / r|} = {x:A | ε * r < |f(x)|}",
				BySets(pointwise))
			squared := a.Have(
				"and the square of f/r is real_inv(r·r) times f²",
				"(λx:A. f(x) / r * (f(x) / r)) = (λx:A. real_inv(r * r) * (f(x) * f(x)))",
				Funext(),
				ByArith())
			a.Show(
				"the constant real_inv(r·r) comes out of the event integral",
				ByArith(
					event,
					squared,
					space,
					event_integral.EventIntegralScale.At(
						Ω,
						S,
						μ,
						a.TermAs[Set[A]]("{x:A | ε * r < |f(x)|}"),
						a.TermAs[Fun[A, Real]]("λx:A. f(x) * f(x)"),
						a.TermAs[Real]("real_inv(r * r)"))))
		})
		// The thresholds ε·σ·√n grow past every bound: √n passes B/(εσ) once n passes its square.
		thresholds := ctx.Lemma(Statement{
			Binders: "∀ε σ B:real.",
			Hypotheses: []string{
				"&0 < ε",
				"&0 < σ",
			},
			Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ B ≤ ε * (σ * real_sqrt(&n))",
		}, func(a *Argument, ε, σ, B *Expr[Real], positiveε, positiveσ Fact) {
			N, above := a.ObtainAs[Nat](
				"some N lies above (B/(εσ))²",
				"∃N:num. B / (ε * σ) * (B / (ε * σ)) ≤ &N",
				By(real_archimedean.ExistsNumAbove))
			a.Show(
				"past N the threshold is at least B",
				Witness(N),
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					past := b.Assume()
					b.Show(
						"√n is at least B/(εσ), and εσ is positive",
						ByArith(
							past,
							above,
							positiveε,
							positiveσ,
							real_sqrt.SqrtLowerBound.At(b.TermAs[Real]("B / (ε * σ)"), b.TermAs[Real]("&n")),
							real_order_field.LessEqDivMulRight.At(
								B, b.TermAs[Real]("real_sqrt(&n)"), b.TermAs[Real]("ε * σ"))))
				}))
		})
		// √n squares to n.
		rootSquare := ctx.Lemma("∀n:num. real_sqrt(&n) * real_sqrt(&n) = &n",
			func(a *Argument, n *Expr[Nat]) {
				a.Show(
					"n is not negative",
					ByArith(real_sqrt.SqrtPowTwo.At(a.TermAs[Real]("&n"))))
			})
		// √n is positive from n = 1 on.
		rootPositive := ctx.Lemma(Statement{
			Binders:    "∀n:num.",
			Hypotheses: []string{"1 ≤ n"},
			Conclusion: "&0 < real_sqrt(&n)",
		}, func(a *Argument, n *Expr[Nat], past Fact) {
			a.Show(
				"n is positive",
				ByArith(past, real_sqrt.SqrtPos.At(a.TermAs[Real]("&n"))))
		})
		// From n = 1 on, the Lindeberg sum of row n at ε is the second moment of X(0) − m beyond
		// ε·σ·√n over σ²: by identical distribution every term of the row is the one of ξ(n, 0),
		// and dividing X(0) − m by σ·√n turns that term into the second moment over (σ·√n)².
		rowLindebergSum := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀X:(num → A → real). " +
				"∀m σ ε:real. " +
				"∀n:num.",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"∀k:num. real_measurable(Ω, S, X(k))",
				"∀k:num. identically_distributed(Ω, μ, X(k), X(0))",
				"&0 < σ",
				"1 ≤ n",
			},
			Conclusion: "real_inv(σ * σ) * «tailMoment»(ε, n) = lindeberg_sum(Ω, S, μ, n, «row»(n), ε)",
		}, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			X *Arrow[Nat, Fun[A, Real]],
			m, σ, ε *Expr[Real],
			n *Expr[Nat],
			measure, measurable, identical, positive, past Fact,
		) {
			firstVariable := a.TermAs[Fun[A, Real]]("X(0)")
			scale := a.TermAs[Real]("σ * real_sqrt(&n)")
			firstTerm := a.TermAs[Real](
				"event_integral(Ω, S, μ, {x:A | ε < |«row»(n, 0, x)|}, λx:A. «row»(n, 0, x) * «row»(n, 0, x))")
			terms := a.Have(
				"by identical distribution every Lindeberg term of row n is the first",
				"∀k:num. "+
					"    event_integral(Ω, "+
					"        S, "+
					"        μ, "+
					"        {x:A | ε < |«row»(n, k, x)|}, "+
					"        λx:A. «row»(n, k, x) * «row»(n, k, x)) = "+
					"    event_integral(Ω, S, μ, {x:A | ε < |«row»(n, 0, x)|}, λx:A. «row»(n, 0, x) * «row»(n, 0, x))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					b.Show(
						"ξ(n, k) is the Borel map y ↦ (y − m)/(σ√n) at X(k)",
						By(
							At(identical, k),
							measure,
							measurable,
							At(affineBorel, m, scale),
							At(
								tailTransfer,
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("X(k)"),
								firstVariable,
								b.TermAs[Fun[Real, Real]]("λy:real. (y - m) / (σ * real_sqrt(&n))"),
								ε)))
				}))
			root := a.TermAs[Real]("real_sqrt(&n)")
			rescaled := a.Have(
				"so the Lindeberg sum is n times the first term, which is «tailMoment»(ε, n)/(σ√n)²",
				"lindeberg_sum(Ω, S, μ, n, «row»(n), ε) = "+
					"&n * («tailMoment»(ε, n) / (σ * real_sqrt(&n) * (σ * real_sqrt(&n))))",
				CalcEq(
					Leg(
						a.Term(
							"Σ_{k<n} event_integral(Ω, S, μ, {x:A | ε < |«row»(n, 0, x)|}, λx:A. «row»(n, 0, x) * «row»(n, 0, x))"),
						"the Lindeberg sum adds the n terms of the row, each the first",
						By(
							terms,
							lindeberg_bound.LindebergSumDef.At(Ω, S, μ, n, a.TermAs[Fun2[Nat, A, Real]]("«row»(n)"), ε),
							real_sum.CongruenceEverywhere.At(
								a.TermAs[Set[Nat]]("{k:num | k < n}"),
								a.TermAs[Fun[Nat, Real]](
									"λk:num. "+
										"    event_integral(Ω, S, μ, {x:A | ε < |«row»(n, k, x)|}, λx:A. «row»(n, k, x) * «row»(n, k, x))"),
								a.TermAs[Fun[Nat, Real]](
									"λk:num. "+
										"    event_integral(Ω, "+
										"        S, "+
										"        μ, "+
										"        {x:A | ε < |«row»(n, 0, x)|}, "+
										"        λx:A. «row»(n, 0, x) * «row»(n, 0, x))")))),
					Leg(
						a.Term(
							"&n * "+
								"event_integral(Ω, S, μ, {x:A | ε < |«row»(n, 0, x)|}, λx:A. «row»(n, 0, x) * «row»(n, 0, x))"),
						"n copies of the first term sum to n times it",
						By(real_sum.ConstBelow.At(n, firstTerm))),
					FinalLeg(
						"dividing X(0) − m by σ√n > 0 multiplies the threshold by σ√n and the second moment by 1/(σ√n)²",
						By(
							measure,
							positive,
							At(rootPositive, n),
							past,
							real_order_ring.MulPos.At(σ, root),
							At(tailRescaled, Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. X(0, x) - m"), scale, ε)))))
			a.Show(
				"and n/(σ√n)² = 1/σ²",
				ByArith(
					rescaled,
					past,
					positive,
					At(rootPositive, n),
					Scaled(
						a.Term(
							"«tailMoment»(ε, n) * "+
								"real_inv(σ) * "+
								"real_inv(σ) * "+
								"real_inv(real_sqrt(&n)) * "+
								"real_inv(real_sqrt(&n))"),
						At(rootSquare, n)),
					real_order_ring.MulPos.At(σ, root)))
		})
		return ctx.Theorem(headline, func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			X *Arrow[Nat, Fun[A, Real]],
			m, σ *Expr[Real],
			independent, identical, square, mean, variance, positive Fact,
		) {
			line := a.TermAs[Set[Real]]("𝕌")
			firstVariable := a.TermAs[Fun[A, Real]]("X(0)")
			space := a.Have(
				"independence carries a probability space on which every X(k) is measurable",
				"probability_on(Ω, S, μ) ∧ measure_on(Ω, S, μ) ∧ (∀k:num. real_measurable(Ω, S, X(k)))",
				By(
					independent,
					set_basic.InUniv,
					independence.IndependentVariableFamilyMeasurable.At(Ω, S, μ, a.TermAs[Set[Nat]]("𝕌"), X),
					probability_space.ProbabilityOnDef.At(Ω, S, μ)))
			borelSets := a.TermAs[Set[Set[Real]]]("borel_sets(real_topology)")
			identity := a.TermAs[Fun[Real, Real]]("λy:real. y")
			deviation := a.TermAs[Fun[Real, Real]]("λy:real. y - m")
			borel := a.Have(
				"the identity and its square are Borel; y − m is continuous, hence Borel, and so is its square",
				"real_measurable(𝕌, borel_sets(real_topology), λy:real. y) ∧ "+
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. y * y) ∧ "+
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. y - m) ∧ "+
					"real_measurable(𝕌, borel_sets(real_topology), λy:real. (y - m) * (y - m))",
				By(
					borel_function.LineBorelSigmaAlgebra,
					measurable_function.RealMeasurableSquare.At(line, borelSets, identity),
					real_continuous.ContinuousOnId,
					real_continuous.ContinuousOnConst,
					real_continuous.ContinuousOnSub.At(identity, a.TermAs[Fun[Real, Real]]("λy:real. m"), line),
					borel_function.ContinuousBorelMeasurable.At(deviation),
					measurable_function.RealMeasurableSquare.At(line, borelSets, deviation),
					borel_function.RealMeasurableIdentity))
			moments := a.Have(
				"each X(k) has the moments of X(0): it is square-integrable with mean m and variance σ²",
				"∀k:num. "+
					"    real_integrable(Ω, S, μ, λx:A. X(k, x) * X(k, x)) ∧ "+
					"    expectation(Ω, S, μ, X(k)) = m ∧ "+
					"    variance(Ω, S, μ, X(k)) = σ * σ",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]("k")
					variable := b.TermAs[Fun[A, Real]]("X(k)")
					b.Show(
						"X(k) and X(0) are identically distributed",
						By(
							At(identical, k),
							mean,
							variance,
							space,
							borel,
							square,
							random_variable.IdenticallyDistributedExpectation.At(
								Ω, S, μ, variable, firstVariable, b.TermAs[Fun[Real, Real]]("λy:real. y")),
							random_variable.IdenticallyDistributedExpectation.At(
								Ω, S, μ, variable, firstVariable, b.TermAs[Fun[Real, Real]]("λy:real. y * y")),
							random_variable.IdenticallyDistributedExpectation.At(
								Ω, S, μ, variable, firstVariable, b.TermAs[Fun[Real, Real]]("λy:real. (y - m) * (y - m)")),
							probability_space.VarianceDef.At(Ω, S, μ, variable),
							probability_space.VarianceDef.At(Ω, S, μ, firstVariable)))
				}))
			rows := a.Have(
				"so ξ(n, k) is centred and square-integrable, with variance σ²/(σ√n)²",
				"∀n k:num. "+
					"    expectation(Ω, S, μ, «row»(n, k)) = &0 ∧ "+
					"    real_integrable(Ω, S, μ, λx:A. «row»(n, k, x) * «row»(n, k, x)) ∧ "+
					"    variance(Ω, S, μ, «row»(n, k)) = σ * σ / (σ * real_sqrt(&n) * (σ * real_sqrt(&n)))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					k := b.FixAs[Nat]("k")
					b.Show(
						"X(k) standardized by σ·√n",
						By(
							At(moments, k),
							space,
							At(
								standardized,
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("X(k)"),
								m,
								b.TermAs[Real]("σ * σ"),
								b.TermAs[Real]("σ * real_sqrt(&n)"))))
				}))
			independentRows := a.Have(
				"each row is independent, ξ(n, k) being a Borel function of X(k)",
				"∀n:num. independent_variable_family(Ω, S, μ, {k:num | k < n}, «row»(n))",
				Derive(func(b *Argument) {
					b.FixAs[Nat]("n")
					below := b.TermAs[Set[Nat]]("{k:num | k < n}")
					b.Show(
						"y ↦ (y − m)/(σ√n) is Borel",
						By(
							independent,
							At(affineBorel, m, b.TermAs[Real]("σ * real_sqrt(&n)")),
							set_order.SubsetUniv.At(below),
							independence.IndependentVariableFamilyCompose.At(
								Ω,
								S,
								μ,
								b.TermAs[Set[Nat]]("𝕌"),
								below,
								X,
								b.TermAs[Fun2[Nat, Real, Real]]("λk:num. λy:real. (y - m) / (σ * real_sqrt(&n))"))))
				}))
			variances := a.Have(
				"the variances of row n sum to 1 from n = 1 on, so they tend to 1",
				"(λn:num. Σ_{k<n} variance(Ω, S, μ, «row»(n, k))) ⟶ &1",
				Derive(func(b *Argument) {
					eventually := b.Have(
						"from n = 1 on, row n holds n variances σ²/(σ²·n)",
						"∀n:num. 1 ≤ n ⇒ Σ_{k<n} variance(Ω, S, μ, «row»(n, k)) = &1",
						Derive(func(c *Argument) {
							n := c.FixAs[Nat]("n")
							past := c.Assume()
							term := c.TermAs[Real]("σ * σ / (σ * real_sqrt(&n) * (σ * real_sqrt(&n)))")
							sum := c.Have(
								"the n variances all equal σ²/(σ√n)², so they sum to n times it",
								"Σ_{k<n} variance(Ω, S, μ, «row»(n, k)) = &n * (σ * σ / (σ * real_sqrt(&n) * (σ * real_sqrt(&n))))",
								By(
									At(rows, n),
									real_sum.CongruenceEverywhere.At(
										c.TermAs[Set[Nat]]("{k:num | k < n}"),
										c.TermAs[Fun[Nat, Real]]("λk:num. variance(Ω, S, μ, «row»(n, k))"),
										c.TermAs[Fun[Nat, Real]]("λk:num. σ * σ / (σ * real_sqrt(&n) * (σ * real_sqrt(&n)))")),
									real_sum.ConstBelow.At(n, term)))
							root := c.TermAs[Real]("real_sqrt(&n)")
							c.Show(
								"and n·σ²/(σ·√n)² = 1",
								ByArith(
									past,
									Scaled(c.Term("real_inv(real_sqrt(&n)) * real_inv(real_sqrt(&n))"), At(rootSquare, n)),
									sum,
									positive,
									At(rootPositive, n),
									real_order_ring.MulPos.At(σ, root)))
						}))
					b.Show(
						"a sequence equal to 1 from n = 1 on tends to 1",
						By(
							eventually,
							real_sequences.LimitConst.At(b.TermAs[Real]("&1")),
							real_sequences.LimitEventuallyEqual.At(
								b.TermAs[Fun[Nat, Real]]("λn:num. &1"),
								b.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k<n} variance(Ω, S, μ, «row»(n, k))"),
								b.TermAs[Real]("&1"),
								b.TermAs[Nat]("1"))))
				}))
			deviationMeasurable := a.Have(
				"X(0) − m is measurable, y ↦ y − m being Borel",
				"real_measurable(Ω, S, λx:A. X(0, x) - m)",
				By(space, borel, borel_function.RealMeasurableCompose.At(Ω, S, firstVariable, deviation)))
			unitShift := a.Have(
				"(X(0) − m)² is the square of the affine image 1·X(0) − m",
				"(λx:A. (X(0, x) - m) * (X(0, x) - m)) = (λx:A. (&1 * X(0, x) + -m) * (&1 * X(0, x) + -m))",
				Funext(),
				ByArith())
			deviationSquareIntegrable := a.Have(
				"and its square is integrable",
				"real_integrable(Ω, S, μ, λx:A. (X(0, x) - m) * (X(0, x) - m))",
				By(
					space,
					square,
					unitShift,
					probability_space.VarianceAffine.At(
						Ω, S, μ, firstVariable, a.TermAs[Real]("&1"), a.TermAs[Real]("-m"))))
			lindeberg := a.Have(
				"the Lindeberg sums of the rows tend to 0",
				"∀ε:real. &0 < ε ⇒ (λn:num. lindeberg_sum(Ω, S, μ, n, «row»(n), ε)) ⟶ &0",
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]("ε")
					positiveε := b.Assume()
					tail := b.Have(
						"the second moment of X(0) − m beyond ε·σ·√n tends to 0, the thresholds growing past every bound",
						"(λn:num. «tailMoment»(ε, n)) ⟶ &0",
						By(
							space,
							deviationMeasurable,
							deviationSquareIntegrable,
							positiveε,
							positive,
							At(thresholds, ε, σ),
							event_integral.EventIntegralTailLimit.At(
								Ω,
								S,
								μ,
								b.TermAs[Fun[A, Real]]("λx:A. X(0, x) - m"),
								b.TermAs[Fun[A, Real]]("λx:A. (X(0, x) - m) * (X(0, x) - m)"),
								b.TermAs[Fun[Nat, Real]]("λn:num. ε * (σ * real_sqrt(&n))"))))
					scaled := b.Have(
						"so does the second moment over σ²",
						"(λn:num. real_inv(σ * σ) * «tailMoment»(ε, n)) ⟶ &0",
						ByArith(
							tail,
							real_sequences.LimitScale.At(
								b.TermAs[Fun[Nat, Real]]("λn:num. «tailMoment»(ε, n)"),
								b.TermAs[Real]("&0"),
								b.TermAs[Real]("real_inv(σ * σ)"))))
					b.Show(
						"and from n = 1 on the Lindeberg sum of row n is that second moment over σ²",
						By(
							scaled,
							space,
							identical,
							positive,
							At(rowLindebergSum, Ω, S, μ, X, m, σ, ε),
							real_sequences.LimitEventuallyEqual.At(
								b.TermAs[Fun[Nat, Real]]("λn:num. real_inv(σ * σ) * «tailMoment»(ε, n)"),
								b.TermAs[Fun[Nat, Real]]("λn:num. lindeberg_sum(Ω, S, μ, n, «row»(n), ε)"),
								b.TermAs[Real]("&0"),
								b.TermAs[Nat]("1"))))
				}))
			sums := a.Have(
				"the row sums are the normalized sums",
				"(λn:num. λx:A. Σ_{k<n} «row»(n, k, x)) = «normalizedSum»",
				Funext(),
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]("n")
					b.FixAs[A]("x")
					inverse := b.TermAs[Real]("real_inv(σ * real_sqrt(&n))")
					below := b.TermAs[Set[Nat]]("{k:num | k < n}")
					b.Show(
						"divide the sum by σ·√n term by term",
						CalcEq(
							Leg(
								b.Term("Σ_{k<n} (X(k, x) - m) * real_inv(σ * real_sqrt(&n))"),
								"dividing by σ·√n is multiplying by its inverse",
								ByArith()),
							Leg(
								b.Term("(Σ_{k<n} (X(k, x) - m)) * real_inv(σ * real_sqrt(&n))"),
								"the inverse comes out of the sum",
								By(real_sum.ScalarRight.At(inverse, b.TermAs[Fun[Nat, Real]]("λk:num. X(k, x) - m"), below))),
							Leg(
								b.Term("(Σ_{k<n} X(k, x) - Σ_{k<n} m) * real_inv(σ * real_sqrt(&n))"),
								"the sum of the differences is the difference of the sums",
								By(
									num_segment.FiniteBelowStrict.At(n),
									real_sum.Sub.At(
										below, b.TermAs[Fun[Nat, Real]]("λk:num. X(k, x)"), b.TermAs[Fun[Nat, Real]]("λk:num. m")))),
							FinalLeg(
								"n copies of m sum to n·m",
								ByArith(real_sum.ConstBelow.At(n, m)))))
				}))
			a.Show(
				"LindebergFeller at the rows ξ(n, k), k < n",
				By(
					sums,
					independentRows,
					rows,
					variances,
					lindeberg,
					LindebergFeller.At(
						Ω,
						S,
						μ,
						a.TermAs[Fun[Nat, Nat]]("λn:num. n"),
						a.TermAs[Fun3[Nat, Nat, A, Real]]("«row»"))))
		})
	}),
})}

// CentralLimitDistributionFunction — the central limit theorem for distribution functions:
// under the hypotheses of CentralLimit, the probability that the normalized sum is at most t
// tends to the standard normal distribution function at t. The distributions of the
// normalized sums converge weakly to the standard normal distribution (CentralLimit), so their
// masses of {y | y ≤ t} converge to its mass there
// (normal_distribution.StandardNormalDistributionFunctionLimit); by the definition of the
// pushforward that mass is μ of the event that the normalized sum is at most t.
var CentralLimitDistributionFunction = centralLimitDistributionFunctionThm{family.Add(registry.ProofEntry{
	Name: "CentralLimitDistributionFunction",
	Key:  "prop_83f385185e26dddf",
	Reading: "The right side is the standard normal distribution function at t. The " +
		"event on the left is cut to Ω, as the distribution of the normalized sum reads it.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀X:(num → A → real). " +
			"∀m σ t:real.",
		Hypotheses: []string{
			"independent_variable_family(Ω, S, μ, 𝕌, X)",
			"∀n:num. identically_distributed(Ω, μ, X(n), X(0))",
			"real_integrable(Ω, S, μ, λx:A. X(0, x) * X(0, x))",
			"expectation(Ω, S, μ, X(0)) = m",
			"variance(Ω, S, μ, X(0)) = σ * σ",
			"&0 < σ",
		},
		Conclusion: "(λn:num. extended_to_real(μ({x:A | x ∈ Ω ∧ «normalizedSum»(n, x) ≤ t}))) ⟶ " +
			"extended_to_real(normal_distribution(&0, &1, {y:real | y ≤ t}))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		X *Arrow[Nat, Fun[A, Real]],
		m, σ, t *Expr[Real],
		h Fact,
	) {
		weak := a.Have(
			"the distributions of the normalized sums converge weakly to the standard normal distribution",
			"weakly_converges(real_topology, "+
				"    λn:num. pushforward_measure(Ω, μ, «normalizedSum»(n)), "+
				"    normal_distribution(&0, &1))",
			By(h, CentralLimit))
		event := a.Have(
			"the n-th distribution gives {y | y ≤ t} the mass μ "+
				"gives the event that the normalized sum is at most t",
			"∀n:num. "+
				"    pushforward_measure(Ω, μ, «normalizedSum»(n), {y:real | y ≤ t}) = "+
				"    μ({x:A | x ∈ Ω ∧ «normalizedSum»(n, x) ≤ t})",
			Simp(Fwd(measure_space.PushforwardMeasureDef), Fwd(functions.PreimageOnDef)),
			SetTac())
		a.Show(
			"so the distribution functions at t converge to the standard normal one",
			By(
				weak,
				event,
				normal_distribution.StandardNormalDistributionFunctionLimit.At(
					a.TermAs[Fun2[Nat, Set[Real], ExtendedNonnegReal]](
						"λn:num. pushforward_measure(Ω, μ, «normalizedSum»(n))"),
					t)))
	}),
})}
