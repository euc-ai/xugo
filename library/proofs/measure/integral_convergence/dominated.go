// dominated.go — the dominated convergence theorem on a measure space.
// Measurable functions f(n) converging pointwise on Ω to g and dominated on
// Ω by one integrable h have integrals converging to the integral of g, and
// the integrals of |f(n) − g| tend to 0. The limit is dominated by h too, so
// g is integrable; Fatou's lemma, applied to the embeddings of the
// nonnegative functions h + f(n) and read through the finite integrals,
// bounds the integrals of the f(n) from below near the integral of g, and
// the same bound for the −f(n) bounds them from above. And the integrals of
// integrable f(n) converge to that of an integrable g whenever the integrals
// of |f(n) − g| tend to 0. An integrable function is the L¹ limit of its
// truncations at ±n, bounded functions whose squares are integrable.

package integral_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/registry"
)

// DominatedLimitIntegrable — the pointwise limit on Ω of measurable
// functions dominated there by an integrable function is dominated by it
// too, and so is integrable. Were h(x) below |g(x)|, the values f(n, x)
// would come within |g(x)| − h(x) of g(x) and exceed h(x) in absolute
// value; and g is measurable as a pointwise limit of measurable functions.
// Of S only the σ-algebra laws are asked, and nothing of μ.
var DominatedLimitIntegrable = dominatedLimitIntegrableThm{family.Add(registry.ProofEntry{
	Name: "DominatedLimitIntegrable",
	Key:  "prop_d4f1a8c443aba719",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → real). " +
			"∀g h:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ (λn:num. f(n, x)) ⟶ g(x)",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |f(n, x)| ≤ h(x)",
			"real_integrable(Ω, S, μ, h)",
		},
		Conclusion: "(∀x:A. x ∈ Ω ⇒ |g(x)| ≤ h(x)) ∧ real_integrable(Ω, S, μ, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow2[Nat, A, Real],
		g, h *Arrow[A, Real],
		sigma, measurable, converges, dominated, integrable Fact,
	) {
		bounded := a.Have(
			"h dominates the limit on Ω",
			"∀x:A. x ∈ Ω ⇒ |g(x)| ≤ h(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				above := b.SupposeNot()
				converging := b.Have(
					"at x the values f(n, x) tend to g(x)",
					"(λn:num. f(n, x)) ⟶ g(x)",
					By(inΩ, converges.At(x)))
				N, near := b.ObtainAs[Nat](
					"past some N the values f(n, x) lie within |g(x)| − h(x) of g(x)",
					"∃N:num. ∀n:num. N ≤ n ⇒ |f(n, x) - g(x)| < |g(x)| - h(x)",
					ByArith(
						above,
						converging,
						real_sequences.RealConvergesToDef.At(b.TermAs[Fun[Nat, Real]]("λn:num. f(n, x)"), g.Apply(x))))
				b.Show(
					"so |f(N, x)| exceeds h(x)",
					ByArith(above, inΩ, near.At(N), dominated.At(N, x)))
			}))
		a.Show(
			"and g, measurable as a pointwise limit of measurable functions, is integrable",
			By(
				sigma,
				integrable,
				measurable,
				converges,
				bounded,
				measurable_function.RealMeasurableLimit.At(Ω, S, f, g),
				measure_integral.IntegrableDominated.At(Ω, S, μ, g, h)))
	}),
})}

// DominatedLowerLimit — the integrals of measurable functions f(n)
// converging on Ω to g under an integrable bound h eventually exceed the
// integral of g less any ε > 0. On Ω the functions h + f(n) are nonnegative,
// measurable and tend to h + g, all of them integrable, so the integrals of
// their embeddings are the finite values ∫h + ∫f(n) and ∫h + ∫g; Fatou's
// lemma puts ∫h + ∫g below the lower limit of the ∫h + ∫f(n), whose terms
// then eventually exceed ∫h + ∫g − ε.
var DominatedLowerLimit = dominatedLowerLimitThm{family.Add(registry.ProofEntry{
	Name: "DominatedLowerLimit",
	Key:  "prop_2d64ae91168f4cda",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f:(num → A → real). ∀g h:(A → real). ∀ε:real.",
		Hypotheses: []string{
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ (λn:num. f(n, x)) ⟶ g(x)",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |f(n, x)| ≤ h(x)",
			"real_integrable(Ω, S, μ, h)",
			"&0 < ε",
		},
		Conclusion: "∃N:num. ∀n:num. N ≤ n ⇒ «integralG» - ε < measure_integral(Ω, S, μ, f(n))",
		Abbrev: Abbrev{
			{Name: "integralG", Text: "measure_integral(Ω, S, μ, g)"},
			{Name: "integralH", Text: "measure_integral(Ω, S, μ, h)"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow2[Nat, A, Real],
		g, h *Arrow[A, Real],
		measurable, converges, dominated, integrable Fact,
		ε *Expr[Real],
		positive Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		limit := a.Conjuncts(
			GroupPremises(
				sigma,
				measurable,
				converges,
				dominated,
				integrable,
				DominatedLimitIntegrable.At(Ω, S, μ, f, g, h)),
			"h dominates the limit g on Ω",
			"which is integrable")
		fIntegrable := a.Have(
			"each f(n) is integrable, h dominating it",
			"∀n:num. real_integrable(Ω, S, μ, f(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a measurable function dominated by an integrable one",
					By(
						measurable.At(n),
						dominated.At(n),
						integrable,
						measure_integral.IntegrableDominated.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("f(n)"), h)))
			}))
		sumsNonneg := a.Have(
			"on Ω each h + f(n) is nonnegative",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ &0 ≤ h(x) + f(n, x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"|f(n, x)| lies below h(x)",
					ByArith(inΩ, dominated.At(n, x)))
			}))
		limitNonneg := a.Have(
			"and so is h + g",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ h(x) + g(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"|g(x)| lies below h(x)",
					ByArith(inΩ, limit[0].At(x)))
			}))
		bounded := a.Have(
			"−h lying below each f(m) on Ω, the integral of f(m) is at least −∫h",
			"∀m:num. &0 ≤ «integralH» + measure_integral(Ω, S, μ, f(m))",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				minusOne := b.TermAs[Real]("-&1")
				above := b.Have(
					"−h lies below f(m) on Ω",
					"∀x:A. x ∈ Ω ⇒ -&1 * h(x) ≤ f(m, x)",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						inΩ := e.Assume()
						e.Show(
							"h(x) + f(m, x) is nonnegative",
							ByArith(inΩ, sumsNonneg.At(m, x)))
					}))
				b.Show(
					"the integral is monotone and moves the factor −1 out",
					ByArith(
						measure,
						integrable,
						fIntegrable.At(m),
						above,
						measure_integral.IntegrableScale.At(Ω, S, μ, h, minusOne),
						measure_integral.IntegralScale.At(Ω, S, μ, h, minusOne),
						measure_integral.IntegralMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("λx:A. -&1 * h(x)"),
							b.TermAs[Fun[A, Real]]("f(m)"))))
			}))
		values := a.Have(
			"each h + f(m) is integrable, so the integral of its embedding is the finite value ∫h + ∫f(m)",
			"∀m:num. "+
				"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(h(x) + f(m, x))) = "+
				"    extended_of_real(«integralH» + measure_integral(Ω, S, μ, f(m)))",
			Derive(func(b *Argument) {
				m := b.FixAs[Nat]("m")
				fm := b.TermAs[Fun[A, Real]]("f(m)")
				b.Show(
					"the integral adds over integrable functions",
					By(
						measure,
						integrable,
						fIntegrable.At(m),
						sumsNonneg.At(m),
						measure_integral.IntegrableAdd.At(Ω, S, μ, h, fm),
						measure_integral.IntegralAdd.At(Ω, S, μ, h, fm),
						measure_integral.IntegralNonnegEmbedding.At(
							Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. h(x) + f(m, x)"))))
			}))
		limitValue := a.Have(
			"and the integral of the embedding of h + g is ∫h + ∫g",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(h(x) + g(x))) = "+
				"extended_of_real(«integralH» + «integralG»)",
			By(
				measure,
				integrable,
				limit[1],
				limitNonneg,
				measure_integral.IntegrableAdd.At(Ω, S, μ, h, g),
				measure_integral.IntegralAdd.At(Ω, S, μ, h, g),
				measure_integral.IntegralNonnegEmbedding.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. h(x) + g(x)"))))
		embeddedMeasurable := a.Have(
			"each h + f(n), embedded in [0, ∞], is measurable",
			"∀n:num. extended_measurable(Ω, S, λx:A. extended_of_real(h(x) + f(n, x)))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a sum of measurable functions, embedded",
					By(
						sigma,
						measurable.At(n),
						integrable,
						measure_integral.RealIntegrableDef.At(Ω, S, μ, h),
						measurable_function.RealMeasurableAdd.At(Ω, S, h, b.TermAs[Fun[A, Real]]("f(n)")),
						measurable_function.ExtendedMeasurableOfReal.At(
							Ω, S, b.TermAs[Fun[A, Real]]("λx:A. h(x) + f(n, x)"))))
			}))
		pointwise := a.Have(
			"on Ω the embedding of h + g lies below the lower limit of the embedded h + f(n)",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "extended_of_real(h(x) + g(x)) ≤ " +
					"extended_liminf(λn:num. extended_of_real(h(x) + f(n, x)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				sums := b.Have(
					"h(x) + f(n, x) tends to h(x) + g(x)",
					"(λn:num. h(x) + f(n, x)) ⟶ h(x) + g(x)",
					By(
						inΩ,
						converges.At(x),
						real_sequences.LimitConst.At(h.Apply(x)),
						real_sequences.LimitAdd.At(
							b.TermAs[Fun[Nat, Real]]("λn:num. h(x)"),
							b.TermAs[Fun[Nat, Real]]("λn:num. f(n, x)"),
							h.Apply(x),
							g.Apply(x))))
				b.Show(
					"a limit lies below the lower limit",
					By(
						sums,
						extended_nonneg_real.LimitLeLiminf.At(
							b.TermAs[Fun[Nat, Real]]("λn:num. h(x) + f(n, x)"),
							b.TermAs[Real]("h(x) + g(x)"))))
			}))
		lowered := a.Have(
			"so the integral of the embedding of h + g lies below that of the lower limit",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(h(x) + g(x))) ≤ "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_liminf(λn:num. extended_of_real(h(x) + f(n, x))))",
			By(
				pointwise,
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(h(x) + g(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]](
						"λx:A. extended_liminf(λn:num. extended_of_real(h(x) + f(n, x)))"))))
		fatou := a.Simplified(
			GroupPremises(
				measure,
				embeddedMeasurable,
				Fatou.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. λx:A. extended_of_real(h(x) + f(n, x))"))),
			Fwd(values))
		lower := a.Have(
			"Fatou's lemma puts ∫h + ∫g below the lower limit of the ∫h + ∫f(n)",
			"extended_of_real(«integralH» + «integralG») ≤ "+
				"extended_liminf(λn:num. extended_of_real(«integralH» + measure_integral(Ω, S, μ, f(n))))",
			By(limitValue, lowered, fatou, extended_nonneg_real.LeTrans))
		N, late := a.ObtainAs[Nat](
			"which therefore eventually exceed ∫h + ∫g − ε",
			"∃N:num. ∀n:num. "+
				"    N ≤ n ⇒ «integralH» + «integralG» - ε < «integralH» + measure_integral(Ω, S, μ, f(n))",
			By(
				bounded,
				lower,
				positive,
				extended_nonneg_real.ExtendedLiminfDef.At(
					a.TermAs[Fun[Nat, ExtendedNonnegReal]](
						"λn:num. extended_of_real(«integralH» + measure_integral(Ω, S, μ, f(n)))")),
				extended_nonneg_real.LowerLimitEventually.At(
					a.TermAs[Fun[Nat, Real]]("λm:num. «integralH» + measure_integral(Ω, S, μ, f(m))"),
					a.TermAs[Real]("«integralH» + «integralG»"),
					ε)))
		a.Take(N)
		n := a.FixAs[Nat]("n")
		past := a.Assume()
		a.Show(
			"less ∫h on both sides",
			ByArith(late.At(n), past))
	}),
})}

// DominatedConvergence — the dominated convergence theorem: measurable
// functions f(n) converging pointwise on Ω to g and dominated there by an
// integrable h are integrable, and so is g, and their integrals converge to
// its integral. The integrals of the f(n) eventually exceed ∫g − ε, and
// those of the −f(n), which converge to −g under the same bound, exceed
// −∫g − ε: past both indices the integrals lie within ε of ∫g.
var DominatedConvergence = dominatedConvergenceThm{family.Add(registry.ProofEntry{
	Name: "DominatedConvergence",
	Key:  "prop_a7ed7647f3d1b258",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f:(num → A → real). ∀g h:(A → real).",
		Hypotheses: []string{
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ (λn:num. f(n, x)) ⟶ g(x)",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |f(n, x)| ≤ h(x)",
			"real_integrable(Ω, S, μ, h)",
		},
		Conclusion: "real_integrable(Ω, S, μ, g) ∧ " +
			"(∀n:num. real_integrable(Ω, S, μ, f(n))) ∧ " +
			"(λn:num. measure_integral(Ω, S, μ, f(n))) ⟶ measure_integral(Ω, S, μ, g)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow2[Nat, A, Real],
		g, h *Arrow[A, Real],
		measurable, converges, dominated, integrable Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		limit := a.Conjuncts(
			GroupPremises(
				sigma,
				measurable,
				converges,
				dominated,
				integrable,
				DominatedLimitIntegrable.At(Ω, S, μ, f, g, h)),
			"h dominates the limit g on Ω",
			"which is integrable")
		fIntegrable := a.Have(
			"each f(n) is integrable, h dominating it",
			"∀n:num. real_integrable(Ω, S, μ, f(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a measurable function dominated by an integrable one",
					By(
						measurable.At(n),
						dominated.At(n),
						integrable,
						measure_integral.IntegrableDominated.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("f(n)"), h)))
			}))
		negMeasurable := a.Have(
			"each −f(n) is measurable",
			"∀n:num. real_measurable(Ω, S, λx:A. -f(n, x))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"the negative of a measurable function",
					By(
						sigma,
						measurable.At(n),
						measurable_function.RealMeasurableNeg.At(Ω, S, b.TermAs[Fun[A, Real]]("f(n)"))))
			}))
		negConverges := a.Have(
			"on Ω the −f(n) tend to −g",
			"∀x:A. x ∈ Ω ⇒ (λn:num. -f(n, x)) ⟶ -g(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"negation passes to the limit",
					By(
						inΩ,
						converges.At(x),
						real_sequences.LimitNeg.At(b.TermAs[Fun[Nat, Real]]("λn:num. f(n, x)"), g.Apply(x))))
			}))
		negDominated := a.Have(
			"and h dominates them",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |-f(n, x)| ≤ h(x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"|−f(n, x)| is |f(n, x)|",
					ByArith(inΩ, dominated.At(n, x)))
			}))
		converge := a.Have(
			"the integrals converge to the integral of g",
			"(λn:num. measure_integral(Ω, S, μ, f(n))) ⟶ measure_integral(Ω, S, μ, g)",
			Derive(func(b *Argument) {
				b.Do(Simp(Fwd(real_sequences.RealConvergesToDef)))
				ε := b.FixAs[Real]("ε")
				positive := b.Assume()
				_, above := b.ObtainAs[Nat](
					"past some N₁ the integrals of the f(n) exceed ∫g − ε",
					"∃N₁:num. ∀n:num. N₁ ≤ n ⇒ measure_integral(Ω, S, μ, g) - ε < measure_integral(Ω, S, μ, f(n))",
					By(
						measure,
						measurable,
						converges,
						dominated,
						integrable,
						positive,
						DominatedLowerLimit.At(Ω, S, μ, f, g, h, ε)))
				_, below := b.ObtainAs[Nat](
					"past some N₂ those of the −f(n) exceed the integral of −g less ε",
					"∃N₂:num. ∀n:num. "+
						"    N₂ ≤ n ⇒ "+
						"    measure_integral(Ω, S, μ, λx:A. -g(x)) - ε < measure_integral(Ω, S, μ, λx:A. -f(n, x))",
					By(
						measure,
						negMeasurable,
						negConverges,
						negDominated,
						integrable,
						positive,
						DominatedLowerLimit.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. -f(n, x)"),
							b.TermAs[Fun[A, Real]]("λx:A. -g(x)"),
							h,
							ε)))
				b.Take(b.TermAs[Nat]("N₁ + N₂"))
				n := b.FixAs[Nat]("n")
				past := b.Assume()
				b.Show(
					"past N₁ + N₂ both hold, and negation passes through the integral",
					ByArith(
						above.At(n),
						below.At(n),
						past,
						measure_integral.IntegralNeg.At(Ω, S, μ, g),
						measure_integral.IntegralNeg.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("f(n)"))))
			}))
		a.Show(
			"and g is integrable, h dominating it",
			By(limit[1], fIntegrable, converge))
	}),
})}

// DominatedConvergenceL1 — under the hypotheses of dominated convergence
// the integrals of |f(n) − g| tend to 0. On Ω the |f(n) − g| are measurable,
// tend to 0, and lie below h + h, which is integrable; dominated convergence
// for them gives integrals tending to the integral of the zero function,
// which is 0.
var DominatedConvergenceL1 = dominatedConvergenceL1Thm{family.Add(registry.ProofEntry{
	Name: "DominatedConvergenceL1",
	Key:  "prop_c0c09d2fba705a38",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f:(num → A → real). ∀g h:(A → real).",
		Hypotheses: []string{
			"∀n:num. real_measurable(Ω, S, f(n))",
			"∀x:A. x ∈ Ω ⇒ (λn:num. f(n, x)) ⟶ g(x)",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |f(n, x)| ≤ h(x)",
			"real_integrable(Ω, S, μ, h)",
		},
		Conclusion: "(λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|)) ⟶ &0",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow2[Nat, A, Real],
		g, h *Arrow[A, Real],
		measurable, converges, dominated, integrable Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		limit := a.Conjuncts(
			GroupPremises(
				sigma,
				measurable,
				converges,
				dominated,
				integrable,
				DominatedLimitIntegrable.At(Ω, S, μ, f, g, h)),
			"h dominates the limit g on Ω",
			"which is integrable")
		gMeasurable := a.Have(
			"g is measurable",
			"real_measurable(Ω, S, g)",
			By(limit[1], measure_integral.RealIntegrableDef.At(Ω, S, μ, g)))
		differencesMeasurable := a.Have(
			"each |f(n) − g| is measurable",
			"∀n:num. real_measurable(Ω, S, λx:A. |f(n, x) - g(x)|)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				sum := b.Have(
					"f(n) − g is f(n) plus −g",
					"(λx:A. f(n, x) - g(x)) = (λx:A. f(n, x) + -g(x))",
					Funext(),
					ByArith())
				b.Show(
					"the absolute value of a sum of measurable functions",
					By(
						sigma,
						measurable.At(n),
						gMeasurable,
						sum,
						measurable_function.RealMeasurableNeg.At(Ω, S, g),
						measurable_function.RealMeasurableAdd.At(
							Ω, S, b.TermAs[Fun[A, Real]]("f(n)"), b.TermAs[Fun[A, Real]]("λx:A. -g(x)")),
						measurable_function.RealMeasurableAbs.At(
							Ω, S, b.TermAs[Fun[A, Real]]("λx:A. f(n, x) - g(x)"))))
			}))
		distance := a.Have(
			"the distance of |y| from 0 is |y|",
			"∀y:real. ||y| - &0| = |y|",
			ByArith())
		differencesConverge := a.Have(
			"on Ω the |f(n) − g| tend to 0",
			"∀x:A. x ∈ Ω ⇒ (λn:num. |f(n, x) - g(x)|) ⟶ &0",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"|f(n, x) − g(x)| lies within ε of 0 once f(n, x) lies within ε of g(x)",
					By(
						inΩ,
						converges.At(x),
						distance,
						real_sequences.RealConvergesToDef.At(b.TermAs[Fun[Nat, Real]]("λn:num. f(n, x)"), g.Apply(x)),
						real_sequences.RealConvergesToDef.At(
							b.TermAs[Fun[Nat, Real]]("λn:num. |f(n, x) - g(x)|"), b.TermAs[Real]("&0"))))
			}))
		differencesDominated := a.Have(
			"on Ω the |f(n) − g| lie below h + h",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ ||f(n, x) - g(x)|| ≤ h(x) + h(x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"|f(n, x)| and |g(x)| each lie below h(x)",
					ByArith(inΩ, dominated.At(n, x), limit[0].At(x)))
			}))
		doubled := a.Have(
			"h + h is integrable",
			"real_integrable(Ω, S, μ, λx:A. h(x) + h(x))",
			By(measure, integrable, measure_integral.IntegrableAdd.At(Ω, S, μ, h, h)))
		a.Show(
			"dominated convergence for the |f(n) − g|",
			By(
				measure,
				differencesMeasurable,
				differencesConverge,
				differencesDominated,
				doubled,
				measure_integral.IntegralZero.At(Ω, S, μ),
				DominatedConvergence.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun2[Nat, A, Real]]("λn:num. λx:A. |f(n, x) - g(x)|"),
					a.TermAs[Fun[A, Real]]("λx:A. &0"),
					a.TermAs[Fun[A, Real]]("λx:A. h(x) + h(x)"))))
	}),
})}

// IntegralL1Limit — integrable f(n) whose distances |f(n) − g| from an
// integrable g have integrals tending to 0 have integrals tending to that of
// g. The integral of f(n) − g is ∫f(n) − ∫g, at most in absolute value the
// value of the integral of the embedding of |f(n) − g|, which is the
// integral of |f(n) − g|; so ∫f(n) lies within ∫|f(n) − g| of ∫g.
var IntegralL1Limit = integralL1LimitThm{family.Add(registry.ProofEntry{
	Name: "IntegralL1Limit",
	Key:  "prop_3f925ab94987fbcd",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → real). " +
			"∀g:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀n:num. real_integrable(Ω, S, μ, f(n))",
			"real_integrable(Ω, S, μ, g)",
			"real_converges_to(λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|), &0)",
		},
		Conclusion: "real_converges_to(λn:num. measure_integral(Ω, S, μ, f(n)), " +
			"    measure_integral(Ω, S, μ, g))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow2[Nat, A, Real],
		g *Arrow[A, Real],
		measure, integrable, integrableG, toZero Fact,
	) {
		bound := a.Have(
			"each ∫f(n) lies within ∫|f(n) − g| of ∫g",
			"∀n:num. "+
				"    |measure_integral(Ω, S, μ, f(n)) - measure_integral(Ω, S, μ, g)| ≤ "+
				"    measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				fn := b.TermAs[Fun[A, Real]]("f(n)")
				difference := b.Have(
					"f(n) − g is integrable, with integral ∫f(n) − ∫g",
					"real_integrable(Ω, S, μ, λx:A. f(n, x) - g(x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. f(n, x) - g(x)) = "+
						"measure_integral(Ω, S, μ, f(n)) - measure_integral(Ω, S, μ, g)",
					By(
						measure,
						integrable.At(n),
						integrableG,
						measure_integral.IntegrableSub.At(Ω, S, μ, fn, g),
						measure_integral.IntegralSub.At(Ω, S, μ, fn, g)))
				b.Show(
					"|∫(f(n) − g)| is at most the value of the integral "+
						"of the embedding of |f(n) − g|, which is ∫|f(n) − g|",
					ByArith(
						difference,
						measure_integral.IntegralOfNonneg.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. |f(n, x) - g(x)|")),
						measure_integral.IntegralAbsLe.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. f(n, x) - g(x)"))))
			}))
		integralG := a.TermAs[Real]("measure_integral(Ω, S, μ, g)")
		a.Show(
			"squeezed about the constant ∫g by distances tending to 0",
			By(
				bound,
				toZero,
				real_sequences.LimitConst.At(integralG),
				real_sequences.LimitSqueezeDistance.At(
					a.TermAs[Fun[Nat, Real]]("λn:num. measure_integral(Ω, S, μ, f(n))"),
					a.TermAs[Fun[Nat, Real]]("λn:num. measure_integral(Ω, S, μ, g)"),
					a.TermAs[Fun[Nat, Real]]("λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|)"),
					integralG)))
	}),
})}

// BoundedTruncationL1 — the truncations of an integrable function X at ±n
// are square integrable, and their distances from X have integrals tending
// to 0. The truncation at n is measurable and lies within n and within |X|
// of 0, so its square lies below n·|X|, which is integrable. At each point
// the truncations equal X(x) once n passes |X(x)|, so dominated convergence
// under |X| carries them to X in L¹.
var BoundedTruncationL1 = boundedTruncationL1Thm{family.Add(registry.ProofEntry{
	Name: "BoundedTruncationL1",
	Key:  "prop_fd892acff4996e91",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀X:(A → real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "real_integrable(Ω, S, μ, X)"},
		Conclusion: "(∀n:num. real_integrable(Ω, S, μ, λx:A. «truncation»(n, x) * «truncation»(n, x))) ∧ " +
			"(λn:num. measure_integral(Ω, S, μ, λx:A. |«truncation»(n, x) - X(x)|)) ⟶ &0",
		Abbrev: Abbrev{
			{Name: "truncation", Text: "λn:num. λx:A. max(-&n, min(&n, X(x)))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		X *Arrow[A, Real],
		measure, integrable Fact,
	) {
		sigma := a.Have(
			"μ's measurable sets form a σ-algebra",
			"sigma_algebra_on(Ω, S)",
			By(measure, measure_space.MeasureOn))
		measurable := a.Have(
			"each truncation is measurable, a max and a min of the measurable X with constants",
			"∀n:num. real_measurable(Ω, S, «truncation»(n))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"X is measurable, being integrable, and so are the constants ±n",
					By(
						sigma,
						integrable,
						measure_integral.RealIntegrableDef.At(Ω, S, μ, X),
						measurable_function.RealMeasurableConst.At(Ω, S, b.TermAs[Real]("&n")),
						measurable_function.RealMeasurableConst.At(Ω, S, b.TermAs[Real]("-&n")),
						measurable_function.RealMeasurableMin.At(Ω, S, b.TermAs[Fun[A, Real]]("λx:A. &n"), X),
						measurable_function.RealMeasurableMax.At(
							Ω,
							S,
							b.TermAs[Fun[A, Real]]("λx:A. -&n"),
							b.TermAs[Fun[A, Real]]("λx:A. min(&n, X(x))"))))
			}))
		bounded := a.Have(
			"the truncation at n lies within n of 0",
			"∀n:num. ∀x:A. |«truncation»(n, x)| ≤ &n",
			ByArith())
		dominated := a.Have(
			"and within |X| of 0, lying between 0 and X",
			"∀n:num. ∀x:A. |«truncation»(n, x)| ≤ |X(x)|",
			ByArith())
		absIntegrable := a.Have(
			"|X| is integrable",
			"real_integrable(Ω, S, μ, λx:A. |X(x)|)",
			By(sigma, integrable, measure_integral.IntegrableAbs))
		squareBound := a.Have(
			"so the square of the truncation at n lies below n·|X|",
			"∀n:num. ∀x:A. |«truncation»(n, x) * «truncation»(n, x)| ≤ &n * |X(x)|",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				b.Show(
					"a product of two factors each below n and below |X(x)|",
					ByArith(bounded.At(n, x), dominated.At(n, x)))
			}))
		squares := a.Have(
			"each square is integrable, being measurable and dominated by the integrable n·|X|",
			"∀n:num. real_integrable(Ω, S, μ, λx:A. «truncation»(n, x) * «truncation»(n, x))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				absX := b.TermAs[Fun[A, Real]]("λx:A. |X(x)|")
				b.Show(
					"the square of a measurable function, below a multiple of |X|",
					By(
						squareBound.At(n),
						measurable.At(n),
						sigma,
						measure,
						absIntegrable,
						measurable_function.RealMeasurableSquare.At(Ω, S, b.TermAs[Fun[A, Real]]("«truncation»(n)")),
						measure_integral.IntegrableScale.At(Ω, S, μ, absX, b.TermAs[Real]("&n")),
						measure_integral.IntegrableDominated.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("λx:A. «truncation»(n, x) * «truncation»(n, x)"),
							b.TermAs[Fun[A, Real]]("λx:A. &n * |X(x)|"))))
			}))
		converges := a.Have(
			"at each point the truncations tend to X(x)",
			"∀x:A. (λn:num. «truncation»(n, x)) ⟶ X(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				N, above := b.ObtainAs[Nat](
					"Archimedes gives an N beyond |X(x)|",
					"∃N:num. |X(x)| ≤ &N",
					By(real_archimedean.ExistsNumAbove))
				b.Do(Unfold(real_sequences.RealConvergesToDef))
				b.FixAs[Real]("ε")
				positive := b.Assume()
				b.Take(N)
				b.Show(
					"from N on the truncation is X(x) itself, at distance 0 < ε",
					ByArith(above, positive))
			}))
		l1 := a.Have(
			"dominated convergence under |X| sends the integrals of the distances to 0",
			"(λn:num. measure_integral(Ω, S, μ, λx:A. |«truncation»(n, x) - X(x)|)) ⟶ &0",
			By(
				converges,
				dominated,
				measurable,
				measure,
				absIntegrable,
				DominatedConvergenceL1.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun2[Nat, A, Real]]("«truncation»"),
					X,
					a.TermAs[Fun[A, Real]]("λx:A. |X(x)|"))))
		a.Show(
			"the squares are integrable, and the distances from X tend to 0 in L¹",
			By(squares, l1))
	}),
})}
