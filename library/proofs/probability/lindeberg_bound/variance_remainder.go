// variance_remainder.go — the third-order budget of the smoothing: each conditional
// variance's excess over ε² is at most the Lindeberg tail of its increment
// (conditionalVarianceExcess), and the means of v(k)·√v(k) sum to at most the clock
// times the root of ε² plus those excesses (threeHalvesPowerSumBound).

package lindeberg_bound

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/conditional_expectation"
	"github.com/euc-ai/xugo/library/proofs/measure/event_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/probability/probability_space"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// conditionalVarianceExcess bounds the conditional variance above ε² by the
// second moment in the Lindeberg tail, on a space of finite mass. On the event
// v > ε², which the conditioning field holds, the conditional expectation
// replaces v by the squared increment, and off the tail ξ² − ε² is at most 0.
var conditionalVarianceExcess = conditionalVarianceExcessThm{family.Add(registry.ProofEntry{
	Name: "conditionalVarianceExcess",
	Key:  "prop_1eaccc663b40cd9c",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀ξ v:(A → real). " +
			"∀ε:real.",
		Hypotheses: []string{
			"finite_measure_on(Ω, S, μ)",
			"real_measurable(Ω, S, ξ)",
			"is_cond_exp(Ω, S, μ, G, λx:A. ξ(x) * ξ(x), v)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. max(v(x) - real_pow(ε, 2), &0)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. max(v(x) - real_pow(ε, 2), &0)) ≤ " +
			"event_integral(Ω, S, μ, {x:A | ε < |ξ(x)|}, λx:A. ξ(x) * ξ(x))",
		Abbrev: Abbrev{
			{Name: "square", Text: "λx:A. ξ(x) * ξ(x)"},
			{Name: "excess", Text: "λx:A. max(v(x) - real_pow(ε, 2), &0)"},
			{Name: "varianceEvent", Text: "{x:A | x ∈ Ω ∧ real_pow(ε, 2) < v(x)}"},
			{Name: "tailEvent", Text: "{x:A | ε < |ξ(x)|}"},
			{Name: "carrierTail", Text: "{x:A | x ∈ Ω ∧ ε < |ξ(x)|}"},
			{Name: "gap", Text: "λf:(A → real). λx:A. f(x) - real_pow(ε, 2)"},
			{Name: "cut", Text: "λE:set(A). λf:(A → real). λx:A. COND(x ∈ E, f(x), &0)"},
			{Name: "tail", Text: "λx:A. COND(ε < |ξ(x)|, ξ(x) * ξ(x), &0)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]],
		ξ, v *Arrow[A, Real],
		ε *Expr[Real],
		finite, measurable, conditional Fact,
	) {
		square := a.TermAs[Fun[A, Real]]("«square»")
		absolute := a.TermAs[Fun[A, Real]]("λx:A. |ξ(x)|")
		data := a.Have(
			"the conditioning field and integrable functions",
			"measure_on(Ω, S, μ) ∧ "+
				"sigma_algebra_on(Ω, S) ∧ "+
				"sigma_algebra_on(Ω, G) ∧ "+
				"G ⊆ S ∧ "+
				"real_integrable(Ω, S, μ, «square») ∧ "+
				"real_integrable(Ω, S, μ, v) ∧ "+
				"real_measurable(Ω, G, v)",
			By(
				conditional,
				conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, square, v),
				measure_space.MeasureOn.At(Ω, S, μ)))
		D := a.TermAs[Set[A]]("«varianceEvent»")
		E := a.TermAs[Set[A]]("«carrierTail»")
		DinG := a.Have(
			"the threshold event belongs to the conditioning field",
			"«varianceEvent» ∈ G",
			By(data, measurable_function.RealMeasurableIffRay.At(Ω, G, v)))
		DinS := a.Have(
			"the threshold event is also ambient measurable",
			"«varianceEvent» ∈ S",
			BySets(data, DinG))
		tailEvent := a.Have(
			"the tail inside the carrier is measurable",
			"«carrierTail» ∈ S",
			By(
				data,
				measurable,
				measurable_function.RealMeasurableAbs.At(Ω, S, ξ),
				measurable_function.RealMeasurableIffRay.At(Ω, S, absolute)))
		threshold := a.TermAs[Real]("real_pow(ε, 2)")
		constant := a.TermAs[Fun[A, Real]]("λx:A. real_pow(ε, 2)")
		carrier := a.Have(
			"the carrier is measurable",
			"Ω ∈ S",
			By(data, sigma_algebra.SigmaAlgebraOnDef.At(Ω, S)))
		constantIntegrable := a.Have(
			"the threshold is a constant on a carrier of finite mass",
			"real_integrable(Ω, S, μ, λx:A. real_pow(ε, 2))",
			By(
				carrier,
				a.Unfolded(finite, measure_space.FiniteMeasureDef),
				measure_integral.IntegrableIndicator.At(Ω, S, μ, Ω, threshold),
				measure_integral.RealIntegrableEqOn.At(
					Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ Ω, real_pow(ε, 2), &0)"), constant)))
		vGap := a.TermAs[Fun[A, Real]]("«gap»(v)")
		xGap := a.TermAs[Fun[A, Real]]("«gap»(«square»)")
		integrableGaps := a.Have(
			"both differences from the threshold are integrable",
			"real_integrable(Ω, S, μ, «gap»(v)) ∧ real_integrable(Ω, S, μ, «gap»(«square»))",
			By(
				data,
				constantIntegrable,
				measure_integral.IntegrableSub.At(Ω, S, μ, v, constant),
				measure_integral.IntegrableSub.At(Ω, S, μ, square, constant)))
		cutV := a.TermAs[Fun[A, Real]]("«cut»(«varianceEvent», «gap»(v))")
		cutX := a.TermAs[Fun[A, Real]]("«cut»(«varianceEvent», «gap»(«square»))")
		cutTail := a.TermAs[Fun[A, Real]]("«cut»(«carrierTail», «square»)")
		tail := a.TermAs[Fun[A, Real]]("«tail»")
		excess := a.TermAs[Fun[A, Real]]("«excess»")
		cuts := a.Have(
			"the cuts to the measured events are integrable",
			"real_integrable(Ω, S, μ, «cut»(«varianceEvent», «gap»(v))) ∧ "+
				"real_integrable(Ω, S, μ, «cut»(«varianceEvent», «gap»(«square»))) ∧ "+
				"real_integrable(Ω, S, μ, «cut»(«carrierTail», «square»))",
			By(
				data,
				DinS,
				tailEvent,
				integrableGaps,
				event_integral.IntegrableOnEvent.At(Ω, S, μ, D, vGap),
				event_integral.IntegrableOnEvent.At(Ω, S, μ, D, xGap),
				event_integral.IntegrableOnEvent.At(Ω, S, μ, E, square)))
		conditionalEvent := a.Have(
			"the conditional event identity persists after subtracting the threshold",
			"event_integral(Ω, S, μ, «varianceEvent», «gap»(v)) = "+
				"event_integral(Ω, S, μ, «varianceEvent», «gap»(«square»))",
			By(
				data,
				DinG,
				DinS,
				constantIntegrable,
				conditional,
				conditional_expectation.IsCondExpDef.At(Ω, S, μ, G, square, v),
				event_integral.EventIntegralSub.At(Ω, S, μ, D, v, constant),
				event_integral.EventIntegralSub.At(Ω, S, μ, D, square, constant)))
		excessCut := a.Have(
			"the positive excess is the cut of the variance difference",
			"∀x:A. x ∈ Ω ⇒ «excess»(x) = «cut»(«varianceEvent», «gap»(v), x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inside := b.Assume()
				thresholdEvent := b.Have(
					"on the carrier the event tests the threshold",
					"x ∈ «varianceEvent» ⇔ real_pow(ε, 2) < v(x)",
					BySets(inside))
				b.Show(
					"both choices take the positive part",
					ByArith(
						Normalized,
						thresholdEvent,
						real_sup_inf.RealMaxDef.At(b.TermAs[Real]("v(x) - real_pow(ε, 2)"), b.TermAs[Real]("&0"))))
			}))
		tailCut := a.Have(
			"the tail function equals the integrable tail cut on the carrier",
			"∀x:A. x ∈ Ω ⇒ «cut»(«carrierTail», «square», x) = «tail»(x)",
			BySets())
		integrable := a.Have(
			"the positive excess and the tail are integrable",
			"real_integrable(Ω, S, μ, «excess») ∧ real_integrable(Ω, S, μ, «tail»)",
			By(
				cuts,
				excessCut,
				tailCut,
				measure_integral.RealIntegrableEqOn.At(Ω, S, μ, cutV, excess),
				measure_integral.RealIntegrableEqOn.At(Ω, S, μ, cutTail, tail)))
		small := a.Have(
			"an increment outside the tail has square at most ε²",
			"∀x:A. ¬(ε < |ξ(x)|) ⇒ ξ(x) * ξ(x) ≤ real_pow(ε, 2)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				small := b.Assume()
				within := b.Have(
					"|ξ(x)| is at most ε, which is then nonnegative",
					"|ξ(x)| ≤ ε ∧ &0 ≤ ε",
					ByArith(small, real_sgn_abs.AbsNonneg.At(ξ.Apply(x))))
				b.Show(
					"compare the squares of the absolute values",
					By(
						Normalized,
						within,
						real_sgn_abs.AbsFixedIffNonneg.At(ε),
						real_pow.AbsLessEqIffPowTwoLessEq.At(ξ.Apply(x), ε),
						real_pow.PowTwo.At(ξ.Apply(x))))
			}))
		ordered := a.Have(
			"the subtracted square on the variance event never exceeds the tail term",
			"∀x:A. x ∈ Ω ⇒ «cut»(«varianceEvent», «gap»(«square»), x) ≤ «tail»(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Assume()
				b.Show(
					"use the threshold bound off the tail and nonnegativity on the tail",
					ByArith(small.At(x), real_order_ring.SquareNonneg.At(ξ.Apply(x)), real_pow.PowTwoNonneg.At(ε)))
			}))
		excessIntegral := a.Have(
			"the excess has the same integral as the variance difference cut",
			"measure_integral(Ω, S, μ, «excess») = measure_integral(Ω, S, μ, «cut»(«varianceEvent», «gap»(v)))",
			By(
				excessCut,
				event_integral.EventIntegralEqOn.At(Ω, S, μ, Ω, excess, cutV),
				event_integral.EventIntegralCarrier.At(Ω, S, μ, excess),
				event_integral.EventIntegralCarrier.At(Ω, S, μ, cutV)))
		cutIdentity := a.Have(
			"the two differences have equal integrals after cutting",
			"measure_integral(Ω, S, μ, «cut»(«varianceEvent», «gap»(v))) = "+
				"measure_integral(Ω, S, μ, «cut»(«varianceEvent», «gap»(«square»)))",
			By(
				conditionalEvent,
				event_integral.EventIntegralDef.At(Ω, S, μ, D, vGap),
				event_integral.EventIntegralDef.At(Ω, S, μ, D, xGap)))
		compared := a.Have(
			"the integrable cut difference has at most the tail integral",
			"measure_integral(Ω, S, μ, «cut»(«varianceEvent», «gap»(«square»))) ≤ "+
				"measure_integral(Ω, S, μ, «tail»)",
			By(cuts, integrable, ordered, measure_integral.IntegralMono.At(Ω, S, μ, cutX, tail)))
		tailEq := a.Have(
			"membership in the tail is the original real threshold test",
			"«cut»(«tailEvent», «square») = «tail»",
			Funext(),
			BySets())
		tailIntegral := a.Have(
			"the tail integral is the Lindeberg event integral",
			"measure_integral(Ω, S, μ, «tail») = event_integral(Ω, S, μ, «tailEvent», «square»)",
			By(tailEq, event_integral.EventIntegralDef.At(Ω, S, μ, a.TermAs[Set[A]]("«tailEvent»"), square)))
		a.Show(
			"the positive excess is integrable and bounded in integral by the tail",
			By(integrable, excessIntegral, cutIdentity, compared, tailIntegral))
	}),
})}

// threeHalvesPowerSumBound — for a row of variances v(j) that are nonnegative and sum to at most c
// almost everywhere, whose excesses over d have means at most e(j), the means of v(j)·√v(j)
// sum to at most c·√(d + Σ e(j)). Pointwise each v(j) is at most R² = d + Σ (v(j) − d)⁺, so
// Σ v(j)·√v(j) ≤ c·R; under a probability the mean of R is at most the root of the mean of R²,
// which is d plus the summed mean excesses.
var threeHalvesPowerSumBound = threeHalvesPowerSumBoundThm{family.Add(registry.ProofEntry{
	Name: "threeHalvesPowerSumBound",
	Key:  "prop_7b6ba06fa0f3ada",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀n:num. " +
			"∀d c:real. " +
			"∀v:(num → A → real). " +
			"∀e:(num → real).",
		Hypotheses: []string{
			"probability_on(Ω, S, μ)",
			"&0 ≤ d",
			"&0 ≤ c",
			"∀j:num. " +
				"    j < n ⇒ " +
				"    real_measurable(Ω, S, v(j)) ∧ " +
				"    real_measurable(Ω, S, λx:A. real_sqrt(v(j, x))) ∧ " +
				"    real_integrable(Ω, S, μ, «excess»(j)) ∧ " +
				"    measure_integral(Ω, S, μ, «excess»(j)) ≤ e(j)",
			"measure_ae(Ω, S, μ, λx:A. (∀j:num. j < n ⇒ &0 ≤ v(j, x)) ∧ Σ_{j<n} v(j, x) ≤ c)",
			"real_measurable(Ω, S, «root»)",
		},
		Conclusion: "(∀j:num. j < n ⇒ real_integrable(Ω, S, μ, «threeHalves»(j))) ∧ " +
			"Σ_{j<n} measure_integral(Ω, S, μ, «threeHalves»(j)) ≤ c * real_sqrt(d + Σ_{j<n} e(j))",
		Abbrev: Abbrev{
			{Name: "excess", Text: "λj:num. λx:A. max(v(j, x) - d, &0)"},
			{Name: "budget", Text: "λx:A. d + Σ_{j<n} «excess»(j, x)"},
			{Name: "root", Text: "λx:A. real_sqrt(«budget»(x))"},
			{Name: "threeHalves", Text: "λj:num. λx:A. v(j, x) * real_sqrt(v(j, x))"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// d plus a sum of positive parts is nonnegative when d is.
			budgetNonnegative := ctx.Lemma(Statement{
				Binders:    "∀n:num. ∀a:(num → real). ∀d:real.",
				Hypotheses: []string{"&0 ≤ d"},
				Conclusion: "&0 ≤ d + Σ_{j<n} max(a(j) - d, &0)",
			}, func(arg *Argument, n *Expr[Nat], a *Arrow[Nat, Real], d *Expr[Real], dNonnegative Fact) {
				parts := arg.Have(
					"every positive part is nonnegative",
					"∀j:num. j ∈ {j:num | j < n} ⇒ &0 ≤ max(a(j) - d, &0)",
					By(real_sup_inf.MaxUpperBound))
				arg.Show(
					"so is their sum, and d",
					ByArith(
						parts,
						dNonnegative,
						real_sum.Nonneg.At(
							arg.TermAs[Set[Nat]]("{j:num | j < n}"),
							arg.TermAs[Fun[Nat, Real]]("λj:num. max(a(j) - d, &0)"))))
			})

			// The pointwise estimate: for nonnegative a(j) summing to at most c, each a(j) lies
			// below R² = d + Σ (a(j) − d)⁺, so each a(j)·√a(j) and their sum lie below c·R.
			pointwiseBound := ctx.Lemma(Statement{
				Binders: "∀n:num. ∀a:(num → real). ∀d c:real.",
				Hypotheses: []string{
					"&0 ≤ d",
					"∀j:num. j ∈ {j:num | j < n} ⇒ &0 ≤ a(j)",
					"Σ_{j<n} a(j) ≤ c",
				},
				Conclusion: "(∀j:num. " +
					"    j ∈ {j:num | j < n} ⇒ " +
					"    |a(j) * real_sqrt(a(j))| ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))) ∧ " +
					"|Σ_{j<n} a(j) * real_sqrt(a(j))| ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
			}, func(
				arg *Argument,
				n *Expr[Nat],
				a *Arrow[Nat, Real],
				d, c *Expr[Real],
				dNonnegative, nonnegative, bounded Fact,
			) {
				row := arg.TermAs[Set[Nat]]("{j:num | j < n}")
				excess := arg.TermAs[Fun[Nat, Real]]("λj:num. max(a(j) - d, &0)")
				total := arg.TermAs[Real]("Σ_{j<n} max(a(j) - d, &0)")
				root := arg.TermAs[Real]("real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))")
				finiteRow := arg.Have(
					"the row is finite",
					"finite({j:num | j < n})",
					By(num_segment.FiniteBelowStrict.At(n)))
				budget := arg.Have(
					"R² is nonnegative",
					"&0 ≤ d + Σ_{j<n} max(a(j) - d, &0)",
					By(dNonnegative, At(budgetNonnegative, n, a, d)))
				parts := arg.Have(
					"every positive part is nonnegative",
					"∀j:num. j ∈ {j:num | j < n} ⇒ &0 ≤ max(a(j) - d, &0)",
					By(real_sup_inf.MaxUpperBound))
				rootBelow := arg.Have(
					"each √a(j) lies between 0 and R",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j ∈ {j:num | j < n}",
						},
						Conclusion: "&0 ≤ real_sqrt(a(j)) ∧ real_sqrt(a(j)) ≤ real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					},
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						inRow := b.Assume()
						part := b.Have(
							"one positive part is at most the sum of all of them",
							"max(a(i) - d, &0) ≤ Σ_{j<n} max(a(j) - d, &0)",
							By(
								finiteRow,
								parts,
								inRow,
								real_order_ring.LessEqRefl,
								real_sum.TermBound.At(row, excess, total, i)))
						below := b.Have(
							"a(i) is at most d plus its positive part, hence at most R²",
							"&0 ≤ a(i) ∧ a(i) ≤ d + Σ_{j<n} max(a(j) - d, &0)",
							ByArith(
								part,
								inRow,
								nonnegative,
								real_sup_inf.MaxUpperBound.At(b.TermAs[Real]("a(i) - d"), b.TermAs[Real]("&0"))))
						b.Show(
							"the square root is monotone",
							ByArith(
								below,
								real_sqrt.SqrtNonneg.At(a.Apply(i)),
								real_sqrt.SqrtPowTwo.At(a.Apply(i)),
								real_sqrt.SqrtLowerBound.At(
									b.TermAs[Real]("real_sqrt(a(i))"),
									b.TermAs[Real]("d + Σ_{j<n} max(a(j) - d, &0)"))))
					}))
				weighted := arg.Have(
					"each a(j)·√a(j) lies between 0 and a(j)·R",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j ∈ {j:num | j < n}",
						},
						Conclusion: "&0 ≤ a(j) * real_sqrt(a(j)) ∧ " +
							"a(j) * real_sqrt(a(j)) ≤ a(j) * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					},
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						inRow := b.Assume()
						b.Show(
							"multiply the bounds on √a(i) by a(i) ≥ 0",
							ByArith(
								rootBelow,
								inRow,
								nonnegative,
								real_order_ring.LessEqMulLeft.At(
									a.Apply(i), b.TermAs[Real]("&0"), b.TermAs[Real]("real_sqrt(a(i))")),
								real_order_ring.LessEqMulLeft.At(a.Apply(i), b.TermAs[Real]("real_sqrt(a(i))"), root)))
					}))
				sumNonnegative := arg.Have(
					"the sum of the a(j)·√a(j) is nonnegative",
					"&0 ≤ Σ_{j<n} a(j) * real_sqrt(a(j))",
					By(weighted, real_sum.Nonneg.At(row, arg.TermAs[Fun[Nat, Real]]("λj:num. a(j) * real_sqrt(a(j))"))))
				sumBelow := arg.Have(
					"the sum of the a(j)·√a(j) is at most the sum of the a(j)·R",
					"Σ_{j<n} a(j) * real_sqrt(a(j)) ≤ Σ_{j<n} a(j) * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					By(
						finiteRow,
						weighted,
						real_sum.Monotone.At(
							row,
							arg.TermAs[Fun[Nat, Real]]("λj:num. a(j) * real_sqrt(a(j))"),
							arg.TermAs[Fun[Nat, Real]]("λj:num. a(j) * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))"))))
				factored := arg.Have(
					"R factors out of the sum",
					"Σ_{j<n} a(j) * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0)) = "+
						"(Σ_{j<n} a(j)) * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					By(real_sum.ScalarRight.At(root, a, row)))
				sumBound := arg.Have(
					"the sum of the a(j)·√a(j) is at most c·R",
					"Σ_{j<n} a(j) * real_sqrt(a(j)) ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					ByArith(
						factored,
						budget,
						sumBelow,
						bounded,
						real_sqrt.SqrtNonneg.At(arg.TermAs[Real]("d + Σ_{j<n} max(a(j) - d, &0)")),
						real_order_ring.LessEqMulLeft.At(root, arg.TermAs[Real]("Σ_{j<n} a(j)"), c)))
				termBound := arg.Have(
					"each a(j)·√a(j) is at most c·R in absolute value",
					Statement{
						Binders: "∀j:num.",
						Hypotheses: []string{
							"j ∈ {j:num | j < n}",
						},
						Conclusion: "|a(j) * real_sqrt(a(j))| ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					},
					Derive(func(b *Argument) {
						i := b.FixAs[Nat]("i")
						inRow := b.Assume()
						single := b.Have(
							"one nonnegative term lies below a bound on the sum",
							"a(i) * real_sqrt(a(i)) ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
							By(
								finiteRow,
								weighted,
								sumBound,
								inRow,
								real_sum.TermBound.At(
									row,
									b.TermAs[Fun[Nat, Real]]("λj:num. a(j) * real_sqrt(a(j))"),
									b.TermAs[Real]("c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))"),
									i)))
						b.Show(
							"the term is nonnegative, so it is its own absolute value",
							ByArith(
								weighted,
								single,
								inRow,
								real_sgn_abs.AbsFixedIffNonneg.At(b.TermAs[Real]("a(i) * real_sqrt(a(i))"))))
					}))
				absoluteSum := arg.Have(
					"the sum is nonnegative, so it is its own absolute value",
					"|Σ_{j<n} a(j) * real_sqrt(a(j))| ≤ c * real_sqrt(d + Σ_{j<n} max(a(j) - d, &0))",
					ByArith(
						sumNonnegative,
						sumBound,
						real_sgn_abs.AbsFixedIffNonneg.At(arg.TermAs[Real]("Σ_{j<n} a(j) * real_sqrt(a(j))"))))
				arg.Show(
					"both bounds",
					By(termBound, absoluteSum))
			})

			return ctx.Theorem(headline, func(
				a *Argument,
				Ω *Expr[Set[A]],
				S *Expr[Set[Set[A]]],
				μ *Arrow[Set[A], ExtendedNonnegReal],
				n *Expr[Nat],
				d, c *Expr[Real],
				v *Arrow2[Nat, A, Real],
				e *Arrow[Nat, Real],
				probability, dNonnegative, cNonnegative, row, clock, rootMeasurable Fact,
			) {
				rowSet := a.TermAs[Set[Nat]]("{j:num | j < n}")
				excess := a.TermAs[Fun2[Nat, A, Real]]("«excess»")
				excessSum := a.TermAs[Fun[A, Real]]("λx:A. Σ_{j<n} «excess»(j, x)")
				budget := a.TermAs[Fun[A, Real]]("«budget»")
				root := a.TermAs[Fun[A, Real]]("«root»")
				scaledRoot := a.TermAs[Fun[A, Real]]("λx:A. c * «root»(x)")
				constant := a.TermAs[Fun[A, Real]]("λx:A. d")
				threeHalves := a.TermAs[Fun2[Nat, A, Real]]("«threeHalves»")
				threeHalvesSum := a.TermAs[Fun[A, Real]]("λx:A. Σ_{j<n} «threeHalves»(j, x)")
				onClock := a.TermAs[Set[A]]("λx:A. (∀j:num. j < n ⇒ &0 ≤ v(j, x)) ∧ Σ_{j<n} v(j, x) ≤ c")

				space := a.Have(
					"a probability is a measure on a σ-algebra",
					"measure_on(Ω, S, μ) ∧ sigma_algebra_on(Ω, S)",
					By(
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_space.MeasureOn.At(Ω, S, μ)))
				finiteRow := a.Have(
					"the row is finite",
					"finite({j:num | j < n})",
					By(num_segment.FiniteBelowStrict.At(n)))

				// The mean of R² is d plus the summed mean excesses, at most d + Σ e(j).
				excessIntegrable := a.Have(
					"each excess over d is integrable",
					"∀j:num. j < n ⇒ real_integrable(Ω, S, μ, «excess»(j))",
					By(row))
				summedExcess := a.Have(
					"the excesses integrate term by term",
					"real_integrable(Ω, S, μ, λx:A. Σ_{j<n} «excess»(j, x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. Σ_{j<n} «excess»(j, x)) = "+
						"Σ_{j<n} measure_integral(Ω, S, μ, «excess»(j))",
					By(
						excessIntegrable,
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_integral.IntegralFiniteSum.At(Ω, S, μ, excess, n)))
				constantMean := a.Have(
					"the constant d has mean d",
					"real_integrable(Ω, S, μ, λx:A. d) ∧ measure_integral(Ω, S, μ, λx:A. d) = d",
					By(
						Normalized,
						probability,
						probability_space.ExpectationConstant.At(Ω, S, μ, d),
						probability_space.ExpectationDef.At(Ω, S, μ, constant)))
				budgetMean := a.Have(
					"R² is integrable with mean d plus the mean excesses",
					"real_integrable(Ω, S, μ, «budget») ∧ "+
						"measure_integral(Ω, S, μ, «budget») = d + Σ_{j<n} measure_integral(Ω, S, μ, «excess»(j))",
					By(
						space,
						constantMean,
						summedExcess,
						measure_integral.IntegrableAdd.At(Ω, S, μ, constant, excessSum),
						measure_integral.IntegralAdd.At(Ω, S, μ, constant, excessSum)))
				excessMeans := a.Have(
					"each mean excess is at most e(j)",
					"∀j:num. j ∈ {j:num | j < n} ⇒ measure_integral(Ω, S, μ, «excess»(j)) ≤ e(j)",
					By(row))
				meansBound := a.Have(
					"the mean excesses sum to at most Σ e(j)",
					"Σ_{j<n} measure_integral(Ω, S, μ, «excess»(j)) ≤ Σ_{j<n} e(j)",
					By(
						finiteRow,
						excessMeans,
						real_sum.Monotone.At(
							rowSet,
							a.TermAs[Fun[Nat, Real]]("λj:num. measure_integral(Ω, S, μ, «excess»(j))"),
							e)))
				budgetBound := a.Have(
					"the mean of R² is at most d + Σ e(j)",
					"measure_integral(Ω, S, μ, «budget») ≤ d + Σ_{j<n} e(j)",
					ByArith(meansBound, budgetMean))
				budgetNonnegativeAE := a.Have(
					"R² is nonnegative almost everywhere",
					"measure_ae(Ω, S, μ, λx:A. &0 ≤ «budget»(x))",
					By(
						space,
						a.Have(
							"R² is nonnegative everywhere on Ω",
							"∀x:A. x ∈ Ω ⇒ &0 ≤ «budget»(x)",
							Derive(func(b *Argument) {
								b.FixAs[A]("x")
								b.Assume()
								b.Show(
									"d is nonnegative",
									By(dNonnegative, At(budgetNonnegative, n, b.TermAs[Fun[Nat, Real]]("λj:num. v(j, x)"), d)))
							})),
						measure_space.AEOfEverywhere.At(Ω, S, μ, a.TermAs[Set[A]]("λx:A. &0 ≤ «budget»(x)"))))

				// Jensen's inequality for the square root bounds the mean of R.
				jensen := a.Have(
					"R is integrable, its mean is nonnegative and its square at most the mean of R²",
					"real_integrable(Ω, S, μ, «root») ∧ "+
						"measure_integral(Ω, S, μ, «root») ^ 2 ≤ measure_integral(Ω, S, μ, «budget») ∧ "+
						"&0 ≤ measure_integral(Ω, S, μ, «root»)",
					By(
						probability,
						budgetMean,
						rootMeasurable,
						budgetNonnegativeAE,
						probability_space.ProbabilityIntegralSqrtUpperBound.At(Ω, S, μ, budget)))
				squaredMean := a.Have(
					"the squared mean of R is at most d + Σ e(j)",
					"measure_integral(Ω, S, μ, «root») ^ 2 ≤ d + Σ_{j<n} e(j)",
					ByArith(budgetBound, jensen))
				rootMean := a.Have(
					"the mean of R is at most √(d + Σ e(j))",
					"measure_integral(Ω, S, μ, «root») ≤ real_sqrt(d + Σ_{j<n} e(j))",
					By(
						squaredMean,
						real_sqrt.SqrtLowerBound.At(
							a.TermAs[Real]("measure_integral(Ω, S, μ, «root»)"),
							a.TermAs[Real]("d + Σ_{j<n} e(j)"))))
				scaledMean := a.Have(
					"c·R is integrable with mean c times the mean of R",
					"real_integrable(Ω, S, μ, λx:A. c * «root»(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. c * «root»(x)) = c * measure_integral(Ω, S, μ, «root»)",
					By(
						jensen,
						space,
						measure_integral.IntegrableScale.At(Ω, S, μ, root, c),
						measure_integral.IntegralScale.At(Ω, S, μ, root, c)))

				// On the clock event the pointwise estimate holds at every x.
				pointwise := a.Have(
					"on the clock event each v(j)·√v(j), and their sum, lie below c·R",
					Statement{
						Binders: "∀x:A.",
						Hypotheses: []string{
							"x ∈ Ω",
							"(∀j:num. j < n ⇒ &0 ≤ v(j, x)) ∧ Σ_{j<n} v(j, x) ≤ c",
						},
						Conclusion: "(∀j:num. j < n ⇒ |«threeHalves»(j, x)| ≤ c * «root»(x)) ∧ " +
							"|Σ_{j<n} «threeHalves»(j, x)| ≤ c * «root»(x)",
					},
					Derive(func(b *Argument) {
						b.FixAs[A]("x")
						onClockAt := b.Assume()
						nonnegativeAt := b.Have(
							"the variances at x are nonnegative along the row",
							"∀j:num. j ∈ {j:num | j < n} ⇒ &0 ≤ v(j, x)",
							BySets(onClockAt))
						b.Show(
							"the pointwise estimate at a(j) = v(j, x)",
							By(
								nonnegativeAt,
								onClockAt,
								dNonnegative,
								At(pointwiseBound, n, b.TermAs[Fun[Nat, Real]]("λj:num. v(j, x)"), d, c)))
					}))
				integrable := a.Have(
					"each v(j)·√v(j) is integrable, dominated by c·R",
					"∀j:num. j < n ⇒ real_integrable(Ω, S, μ, «threeHalves»(j))",
					Derive(func(b *Argument) {
						b.FixAs[Nat]("j")
						early := b.Assume()
						measurable := b.Have(
							"v(j)·√v(j) is a product of measurable functions",
							"real_measurable(Ω, S, «threeHalves»(j))",
							By(
								space,
								early,
								row,
								measurable_function.RealMeasurableMul.At(
									Ω,
									S,
									b.TermAs[Fun[A, Real]]("v(j)"),
									b.TermAs[Fun[A, Real]]("λx:A. real_sqrt(v(j, x))"))))
						dominated := b.Have(
							"almost everywhere |v(j)·√v(j)| ≤ c·R",
							"measure_ae(Ω, S, μ, λx:A. |«threeHalves»(j, x)| ≤ c * «root»(x))",
							By(
								pointwise,
								early,
								clock,
								measure_space.AEMono.At(
									Ω,
									S,
									μ,
									onClock,
									b.TermAs[Set[A]]("λx:A. |«threeHalves»(j, x)| ≤ c * «root»(x)"))))
						b.Show(
							"a measurable function dominated by an integrable one",
							By(
								space,
								scaledMean,
								measurable,
								dominated,
								measure_integral.AEBoundedIntegral.At(
									Ω, S, μ, b.TermAs[Fun[A, Real]]("«threeHalves»(j)"), scaledRoot)))
					}))
				summed := a.Have(
					"the v(j)·√v(j) integrate term by term",
					"real_integrable(Ω, S, μ, λx:A. Σ_{j<n} «threeHalves»(j, x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. Σ_{j<n} «threeHalves»(j, x)) = "+
						"Σ_{j<n} measure_integral(Ω, S, μ, «threeHalves»(j))",
					By(
						integrable,
						probability,
						probability_space.ProbabilityOnDef.At(Ω, S, μ),
						measure_integral.IntegralFiniteSum.At(Ω, S, μ, threeHalves, n)))
				sumMeasurable := a.Have(
					"the sum of the v(j)·√v(j) is measurable",
					"real_measurable(Ω, S, λx:A. Σ_{j<n} «threeHalves»(j, x))",
					By(summed, measure_integral.RealIntegrableDef.At(Ω, S, μ, threeHalvesSum)))
				sumDominated := a.Have(
					"almost everywhere the sum of the v(j)·√v(j) is at most c·R in absolute value",
					"measure_ae(Ω, S, μ, λx:A. |Σ_{j<n} «threeHalves»(j, x)| ≤ c * «root»(x))",
					By(
						pointwise,
						clock,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							onClock,
							a.TermAs[Set[A]]("λx:A. |Σ_{j<n} «threeHalves»(j, x)| ≤ c * «root»(x)"))))
				sumMean := a.Have(
					"the mean of the sum is at most the mean of c·R in absolute value",
					"|measure_integral(Ω, S, μ, λx:A. Σ_{j<n} «threeHalves»(j, x))| ≤ "+
						"measure_integral(Ω, S, μ, λx:A. c * «root»(x))",
					By(
						space,
						scaledMean,
						sumMeasurable,
						sumDominated,
						measure_integral.AEBoundedIntegral.At(Ω, S, μ, threeHalvesSum, scaledRoot)))
				meanBound := a.Have(
					"the means sum to at most c·√(d + Σ e(j))",
					"Σ_{j<n} measure_integral(Ω, S, μ, «threeHalves»(j)) ≤ c * real_sqrt(d + Σ_{j<n} e(j))",
					ByArith(
						sumMean,
						rootMean,
						cNonnegative,
						scaledMean,
						summed,
						real_sgn_abs.AbsDominates.At(
							a.TermAs[Real]("measure_integral(Ω, S, μ, λx:A. Σ_{j<n} «threeHalves»(j, x))")),
						real_order_ring.LessEqMulLeft.At(
							c,
							a.TermAs[Real]("measure_integral(Ω, S, μ, «root»)"),
							a.TermAs[Real]("real_sqrt(d + Σ_{j<n} e(j))"))))
				a.Show(
					"each term is integrable and the means obey the bound",
					By(integrable, meanBound))
			})
		}),
})}
