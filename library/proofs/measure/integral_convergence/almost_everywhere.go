// almost_everywhere.go — the convergence theorems where their hypotheses
// hold only almost everywhere: monotone convergence, Fatou's lemma and
// dominated convergence. Each gathers its countably many exceptions into
// one measurable set of measure zero, cuts the functions to 0 there, and
// applies the pointwise theorem to the cut functions, whose integrals are
// those of the functions they cut.

package integral_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MonotoneConvergenceAE — monotone convergence where the sequence rises and
// converges to g only almost everywhere. The countably many steps rise
// together almost everywhere, and with the limit, off a measurable set N of
// measure zero. Cut to 0 on N, each f(n) stays measurable, has the same
// integral, and the cut sequence rises at every point of Ω; its supremum is g
// off N. Monotone convergence for the cut sequence, and a.e. invariance of
// the integral, which reads no measurability of g, give the identity.
var MonotoneConvergenceAE = monotoneConvergenceAEThm{family.Add(registry.ProofEntry{
	Name: "MonotoneConvergenceAE",
	Key:  "prop_20e5917671902c7",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → extended_nonneg_real). " +
			"∀g:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀n:num. extended_measurable(Ω, S, f(n))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. f(n, x) ≤ f(n + 1, x))",
			"measure_ae(Ω, S, μ, λx:A. g(x) = extended_sup(image(λn:num. f(n, x), 𝕌)))",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, g) = " +
			"extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, f(n)), 𝕌))",
		Abbrev: Abbrev{
			{Name: "cut", Text: "λE:set(A). λn:num. λx:A. COND(x ∉ E, f(n, x), &0)"},
			{Name: "good", Text: "λx:A. " +
				"    (∀n:num. f(n, x) ≤ f(n + 1, x)) ∧ g(x) = extended_sup(image(λn:num. f(n, x), 𝕌))"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow2[Nat, A, ExtendedNonnegReal], g *Arrow[A, ExtendedNonnegReal],
		measure, measurable, rising, limit Fact) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		allSteps := a.Have(
			"the countably many steps rise together almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. ∀n:num. f(n, x) ≤ f(n + 1, x))",
			By(
				measure,
				rising,
				measure_space.AECountable.At(
					Ω, S, μ, a.TermAs[Fun[Nat, Set[A]]]("λn:num. λx:A. f(n, x) ≤ f(n + 1, x)"))))
		together := a.Have(
			"and with the limit g",
			"measure_ae(Ω, S, μ, «good»)",
			By(
				measure,
				allSteps,
				limit,
				measure_space.AEConjunction.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. ∀n:num. f(n, x) ≤ f(n + 1, x)"),
					a.TermAs[Set[A]]("λx:A. g(x) = extended_sup(image(λn:num. f(n, x), 𝕌))"))))
		exceptional := a.Conjuncts(
			a.Unfolded(a.Unfolded(together, measure_space.AlmostEverywhereDef), measure_space.NullSetDef),
			"the points of Ω where this fails lie in Ω",
			"and in a measurable set N of measure zero")
		N, null := a.UnpackAs[Set[A]](exceptional[1], "N")
		covering := a.Conjuncts(
			null,
			"N is measurable",
			"N has measure zero",
			"N holds every point of Ω where the sequence fails to rise to g")
		measurableN := covering[0]
		good := a.Have(
			"off N the sequence rises at every point of Ω, to g",
			"∀x:A. x ∈ Ω ∧ x ∉ N ⇒ «good»(x)",
			BySets(covering[2]))
		offN := a.Have(
			"almost every point lies off N",
			"measure_ae(Ω, S, μ, λx:A. x ∉ N)",
			By(measurableN, covering[1], measure_space.AEOffNullSet.At(Ω, S, μ, N)))
		cutMeasurable := a.Have(
			"cut to 0 on N, each f(n) stays measurable",
			"∀n:num. extended_measurable(Ω, S, «cut»(N, n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				fn := b.TermAs[Fun[A, ExtendedNonnegReal]]("f(n)")
				fRays := b.Have(
					"f(n) exceeds each real level on a measurable set",
					"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)} ∈ S",
					By(sigma, measurable.At(n), measurable_function.ExtendedMeasurableIffRay.At(Ω, S, fn)))
				cutRays := b.Have(
					"the cut function exceeds a level exactly where f(n) does off N, 0 exceeding no level",
					"∀r:real. "+
						"    {x:A | x ∈ Ω ∧ extended_of_real(r) < «cut»(N, n, x)} = "+
						"    {x:A | x ∈ Ω ∧ extended_of_real(r) < f(n, x)} ∖ N",
					BySets(extended_nonneg_real.ZeroLe, extended_nonneg_real.LtIffNotLe))
				measurableRays := b.Have(
					"a difference of measurable sets",
					"∀r:real. {x:A | x ∈ Ω ∧ extended_of_real(r) < «cut»(N, n, x)} ∈ S",
					By(cutRays, fRays, measurableN, sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
				b.Show(
					"its rays decide its measurability",
					By(
						sigma,
						measurableRays,
						measurable_function.ExtendedMeasurableIffRay.At(
							Ω,
							S,
							b.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(N, n)"))))
			}))
		cutRising := a.Have(
			"the cut sequence rises at every point of Ω: off N as f does, on N staying 0",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ «cut»(N, n, x) ≤ «cut»(N, n + 1, x)",
			By(good, extended_nonneg_real.LeRefl))
		monotone := a.Have(
			"so monotone convergence holds for the cut sequence",
			"nonneg_integral(Ω, S, μ, λx:A. extended_sup(image(λn:num. «cut»(N, n, x), 𝕌))) = "+
				"extended_sup(image(λn:num. nonneg_integral(Ω, S, μ, «cut»(N, n)), 𝕌))",
			By(
				measure,
				cutMeasurable,
				cutRising,
				nonneg_integral.MonotoneConvergence.At(
					Ω, S, μ, a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«cut»(N)"))))
		terms := a.Have(
			"each cut function agrees with f(n) off N, so it has the same integral",
			"∀n:num. nonneg_integral(Ω, S, μ, «cut»(N, n)) = nonneg_integral(Ω, S, μ, f(n))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				agree := b.Have(
					"the cut function equals f(n) almost everywhere",
					"measure_ae_eq(Ω, S, μ, «cut»(N, n), f(n))",
					Simp(Fwd(measure_space.AEEqualDef)),
					By(
						offN,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Set[A]]("λx:A. x ∉ N"),
							b.TermAs[Set[A]]("λx:A. «cut»(N, n, x) = f(n, x)"))))
				b.Show(
					"a.e. equal functions have the same integral",
					By(
						measure,
						agree,
						nonneg_integral.NonnegIntegralAE.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(N, n)"),
							b.TermAs[Fun[A, ExtendedNonnegReal]]("f(n)"))))
			}))
		supremum := a.Have(
			"off N the supremum of the cut sequence is that of f, which is g",
			"∀x:A. x ∈ Ω ∧ x ∉ N ⇒ extended_sup(image(λn:num. «cut»(N, n, x), 𝕌)) = g(x)",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				off := b.Assume()
				same := b.Have(
					"off N the cut sequence is f itself",
					"image(λn:num. «cut»(N, n, x), 𝕌) = image(λn:num. f(n, x), 𝕌)",
					BySets(off))
				b.Show(
					"and its supremum is g there",
					By(same, GroupPremises(off, good.At(x))))
			}))
		limitAE := a.Have(
			"so g equals the supremum of the cut sequence almost everywhere",
			"measure_ae_eq(Ω, S, μ, g, λx:A. extended_sup(image(λn:num. «cut»(N, n, x), 𝕌)))",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				offN,
				supremum,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. g(x) = extended_sup(image(λn:num. «cut»(N, n, x), 𝕌))"))))
		throughLimit := a.Have(
			"g has the integral of that supremum",
			"nonneg_integral(Ω, S, μ, g) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_sup(image(λn:num. «cut»(N, n, x), 𝕌)))",
			By(
				measure,
				limitAE,
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					g,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_sup(image(λn:num. «cut»(N, n, x), 𝕌))"))))
		a.Show(
			"the integrals of the cut functions are those of the f(n)",
			By(throughLimit, a.Simplified(monotone, Fwd(terms))))
	}),
})}

// DominatedConvergenceAE — dominated convergence where the f(n) converge to g
// and lie below h only almost everywhere. The countably many bounds hold
// together almost everywhere, and with the convergence, off a measurable set
// N of measure zero. Cut to 0 on N, the f(n), g and h stay measurable, and
// at every point of Ω the cut f(n) lie below the cut h and converge to the
// cut g; the cut h is integrable, equal to h almost everywhere. Pointwise
// dominated convergence for the cut functions makes the cut g and each cut
// f(n) integrable and the integrals of their distances tend to 0. Equal
// almost everywhere to the functions they cut, they carry integrability to g
// and the f(n), the cut g and h being measurable, and the integrals of
// |f(n) − g| are those of the cut distances; the integrals of the f(n) then
// converge to that of g (IntegralL1Limit).
var DominatedConvergenceAE = dominatedConvergenceAEThm{family.Add(registry.ProofEntry{
	Name: "DominatedConvergenceAE",
	Reading: "Measurability of g is load-bearing because the " +
		"concluded real_integrable(g) contains it and S may be incomplete.",
	Key: "prop_7f0587d3bcb43e79",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → real). " +
			"∀g h:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀n:num. real_measurable(Ω, S, f(n))",
			"real_measurable(Ω, S, g)",
			"real_integrable(Ω, S, μ, h)",
			"measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. f(n, x), g(x)))",
			"∀n:num. measure_ae(Ω, S, μ, λx:A. |f(n, x)| ≤ h(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, g) ∧ " +
			"(∀n:num. real_integrable(Ω, S, μ, f(n))) ∧ " +
			"real_converges_to(λn:num. measure_integral(Ω, S, μ, f(n)), measure_integral(Ω, S, μ, g)) ∧ " +
			"real_converges_to(λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|), &0)",
		Abbrev: Abbrev{
			{Name: "cut", Text: "λE:set(A). λn:num. λx:A. COND(x ∉ E, f(n, x), &0)"},
			{Name: "cutLimit", Text: "λE:set(A). λx:A. COND(x ∉ E, g(x), &0)"},
			{Name: "cutBound", Text: "λE:set(A). λx:A. COND(x ∉ E, h(x), &0)"},
			{Name: "good", Text: "λx:A. (∀n:num. |f(n, x)| ≤ h(x)) ∧ real_converges_to(λn:num. f(n, x), g(x))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow2[Nat, A, Real],
		g, h *Arrow[A, Real],
		measure, measurable, gMeasurable, integrable, converges, dominated Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		hMeasurable := a.Have(
			"h is measurable",
			"real_measurable(Ω, S, h)",
			By(integrable, measure_integral.RealIntegrableDef.At(Ω, S, μ, h)))
		bounds := a.Have(
			"the countably many bounds hold together almost everywhere",
			"measure_ae(Ω, S, μ, λx:A. ∀n:num. |f(n, x)| ≤ h(x))",
			By(
				measure,
				dominated,
				measure_space.AECountable.At(
					Ω, S, μ, a.TermAs[Fun[Nat, Set[A]]]("λn:num. λx:A. |f(n, x)| ≤ h(x)"))))
		together := a.Have(
			"and with the convergence",
			"measure_ae(Ω, S, μ, «good»)",
			By(
				measure,
				bounds,
				converges,
				measure_space.AEConjunction.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. ∀n:num. |f(n, x)| ≤ h(x)"),
					a.TermAs[Set[A]]("λx:A. real_converges_to(λn:num. f(n, x), g(x))"))))
		exceptional := a.Conjuncts(
			a.Unfolded(a.Unfolded(together, measure_space.AlmostEverywhereDef), measure_space.NullSetDef),
			"the points of Ω where this fails lie in Ω",
			"and in a measurable set N of measure zero")
		N, null := a.UnpackAs[Set[A]](exceptional[1], "N")
		covering := a.Conjuncts(
			null,
			"N is measurable",
			"N has measure zero",
			"N holds every point of Ω where a bound or the convergence fails")
		measurableN := covering[0]
		good := a.Have(
			"off N, at each point of Ω the f(n) lie below h and converge to g",
			"∀x:A. x ∈ Ω ∧ x ∉ N ⇒ «good»(x)",
			BySets(covering[2]))
		offN := a.Have(
			"almost every point lies off N",
			"measure_ae(Ω, S, μ, λx:A. x ∉ N)",
			By(measurableN, covering[1], measure_space.AEOffNullSet.At(Ω, S, μ, N)))
		cutMeasurable := a.Have(
			"cut to 0 on N, each f(n) stays measurable",
			"∀n:num. real_measurable(Ω, S, «cut»(N, n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"a measurable function cut on a measurable set",
					By(
						sigma,
						measurableN,
						measurable.At(n),
						measurable_function.RealMeasurableCut.At(Ω, S, N, b.TermAs[Fun[A, Real]]("f(n)"))))
			}))
		limitsMeasurable := a.Have(
			"and so do g and h",
			"real_measurable(Ω, S, «cutLimit»(N)) ∧ real_measurable(Ω, S, «cutBound»(N))",
			By(
				sigma,
				measurableN,
				gMeasurable,
				hMeasurable,
				measurable_function.RealMeasurableCut.At(Ω, S, N, g),
				measurable_function.RealMeasurableCut.At(Ω, S, N, h)))
		cutConverges := a.Have(
			"at every point of Ω the cut f(n) converge to the cut g",
			"∀x:A. x ∈ Ω ⇒ real_converges_to(λn:num. «cut»(N, n, x), «cutLimit»(N, x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Cases(b.Term("x ∈ N"))
				b.When(
					"on N the cut sequence and the cut limit are 0",
					func(c *Argument, inN Fact) {
						c.Show(
							"a constant sequence tends to its value",
							Simp(Fwd(inN)),
							TrivialSimplify(),
							By(real_sequences.LimitConst.At(c.TermAs[Real]("&0"))))
					})
				b.Otherwise(
					"off N they are the f(n, x) and g(x)",
					func(c *Argument, offFact Fact) {
						c.Show(
							"which converge there",
							Simp(Fwd(offFact)),
							TrivialSimplify(),
							By(inΩ, offFact, good.At(x)))
					})
			}))
		cutDominated := a.Have(
			"and lie below the cut h",
			"∀n:num. ∀x:A. x ∈ Ω ⇒ |«cut»(N, n, x)| ≤ «cutBound»(N, x)",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Cases(b.Term("x ∈ N"))
				b.When(
					"on N both are 0",
					func(c *Argument, inN Fact) {
						c.Show(
							"|0| ≤ 0",
							ByArith(inN))
					})
				b.Otherwise(
					"off N they are f(n, x) and h(x)",
					func(c *Argument, offFact Fact) {
						bounded := c.Have(
							"off N the f(n, x) lie below h(x)",
							"∀m:num. |f(m, x)| ≤ h(x)",
							By(Normalized, inΩ, offFact, good.At(x)))
						c.Show(
							"so f(n, x) does",
							ByArith(offFact, bounded.At(n)))
					})
			}))
		agree := a.Have(
			"off N each cut function equals the function it cuts",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∉ N"},
				Conclusion: "(∀n:num. " +
					"    «cut»(N, n, x) = f(n, x) ∧ |«cut»(N, n, x) - «cutLimit»(N, x)| = |f(n, x) - g(x)|) ∧ " +
					"«cutLimit»(N, x) = g(x) ∧ " +
					"«cutBound»(N, x) = h(x)",
			},
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				off := b.Assume()
				b.Show(
					"off N each cut keeps its value",
					Simp(Fwd(off)),
					TrivialNormalized())
			}))
		boundAE := a.Have(
			"so the cut h equals h almost everywhere",
			"measure_ae_eq(Ω, S, μ, h, «cutBound»(N))",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				offN,
				agree,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. h(x) = «cutBound»(N, x)"))))
		limitAE := a.Have(
			"the cut g equals g almost everywhere",
			"measure_ae_eq(Ω, S, μ, g, «cutLimit»(N))",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				offN,
				agree,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. g(x) = «cutLimit»(N, x)"))))
		termsAE := a.Have(
			"each cut f(n) equals f(n) almost everywhere, and the cut distance the distance of f(n) from g",
			"∀n:num. "+
				"    measure_ae_eq(Ω, S, μ, f(n), «cut»(N, n)) ∧ "+
				"    measure_ae_eq(Ω, S, μ, λx:A. |f(n, x) - g(x)|, λx:A. |«cut»(N, n, x) - «cutLimit»(N, x)|)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"they agree off N",
					Simp(Fwd(measure_space.AEEqualDef)),
					By(
						offN,
						agree,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Set[A]]("λx:A. x ∉ N"),
							b.TermAs[Set[A]]("λx:A. f(n, x) = «cut»(N, n, x)")),
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Set[A]]("λx:A. x ∉ N"),
							b.TermAs[Set[A]]("λx:A. |f(n, x) - g(x)| = |«cut»(N, n, x) - «cutLimit»(N, x)|"))))
			}))
		boundIntegrable := a.Have(
			"the cut h is integrable, equal to h almost everywhere",
			"real_integrable(Ω, S, μ, «cutBound»(N))",
			By(
				measure,
				hMeasurable,
				limitsMeasurable,
				integrable,
				boundAE,
				measure_integral.IntegrableAE.At(Ω, S, μ, h, a.TermAs[Fun[A, Real]]("«cutBound»(N)"))))
		cut := a.TermAs[Fun2[Nat, A, Real]]("«cut»(N)")
		cutLimit := a.TermAs[Fun[A, Real]]("«cutLimit»(N)")
		cutBound := a.TermAs[Fun[A, Real]]("«cutBound»(N)")
		cutResults := a.Conjuncts(
			GroupPremises(
				measure,
				cutMeasurable,
				cutConverges,
				cutDominated,
				boundIntegrable,
				DominatedConvergence.At(Ω, S, μ, cut, cutLimit, cutBound)),
			"dominated convergence for the cut functions makes the cut g integrable",
			"and each cut f(n)",
			"and their integrals converge")
		cutDistances := GroupPremises(
			measure,
			cutMeasurable,
			cutConverges,
			cutDominated,
			boundIntegrable,
			DominatedConvergenceL1.At(Ω, S, μ, cut, cutLimit, cutBound))
		gIntegrable := a.Have(
			"g is integrable, equal to the cut g almost everywhere and measurable",
			"real_integrable(Ω, S, μ, g)",
			By(
				measure,
				gMeasurable,
				limitsMeasurable,
				limitAE,
				cutResults[0],
				measure_integral.IntegrableAE.At(Ω, S, μ, g, cutLimit)))
		fIntegrable := a.Have(
			"and so is each f(n)",
			"∀n:num. real_integrable(Ω, S, μ, f(n))",
			Derive(func(b *Argument) {
				n := b.FixAs[Nat]("n")
				b.Show(
					"f(n) equals the cut f(n) almost everywhere, and is measurable",
					By(
						measure,
						measurable.At(n),
						cutMeasurable.At(n),
						termsAE.At(n),
						cutResults[1].At(n),
						measure_integral.IntegrableAE.At(
							Ω, S, μ, b.TermAs[Fun[A, Real]]("f(n)"), b.TermAs[Fun[A, Real]]("«cut»(N, n)"))))
			}))
		termwise := a.Have(
			"the integrals of |f(n) − g| are those of the cut distances",
			"∀n:num. "+
				"    measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|) = "+
				"    measure_integral(Ω, S, μ, λx:A. |«cut»(N, n, x) - «cutLimit»(N, x)|)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				b.Show(
					"functions equal almost everywhere have the same integral",
					By(
						measure,
						termsAE,
						measure_integral.IntegralAE.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("λx:A. |f(n, x) - g(x)|"),
							b.TermAs[Fun[A, Real]]("λx:A. |«cut»(N, n, x) - «cutLimit»(N, x)|"))))
			}))
		distances := a.Have(
			"so the integrals of |f(n) − g| tend to 0",
			"real_converges_to(λn:num. measure_integral(Ω, S, μ, λx:A. |f(n, x) - g(x)|), &0)",
			Simp(Fwd(termwise)),
			By(cutDistances))
		a.Show(
			"and the integrals of the f(n) converge to that of g",
			By(measure, gIntegrable, fIntegrable, distances, IntegralL1Limit.At(Ω, S, μ, f, g)))
	}),
})}

// FatouAE — Fatou's lemma for a function g lying below the lower limit of
// the f(n) only almost everywhere. Replace g by 0 where it does not lie
// below the lower limit: the result equals g almost everywhere, so it has
// the integral of g, which reads no measurability of g, and it lies below the
// lower limit at every point, so its integral is at most that of the lower
// limit, at most the lower limit of the integrals by Fatou's lemma.
var FatouAE = fatouAEThm{family.Add(registry.ProofEntry{
	Name: "FatouAE",
	Key:  "prop_31860c978b45062b",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f:(num → A → extended_nonneg_real). " +
			"∀g:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀n:num. extended_measurable(Ω, S, f(n))",
			"measure_ae(Ω, S, μ, λx:A. g(x) ≤ extended_liminf(λn:num. f(n, x)))",
		},
		Conclusion: "nonneg_integral(Ω, S, μ, g) ≤ extended_liminf(λn:num. nonneg_integral(Ω, S, μ, f(n)))",
		Abbrev: Abbrev{
			{Name: "lower", Text: "λx:A. extended_liminf(λn:num. f(n, x))"},
			{Name: "trimmed", Text: "λx:A. COND(g(x) ≤ extended_liminf(λn:num. f(n, x)), g(x), &0)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow2[Nat, A, ExtendedNonnegReal], g *Arrow[A, ExtendedNonnegReal],
		measure, measurable, below Fact) {
		trimmed := a.TermAs[Fun[A, ExtendedNonnegReal]]("«trimmed»")
		agree := a.Have(
			"g equals the trimmed function wherever it lies below the lower limit, so almost everywhere",
			"measure_ae_eq(Ω, S, μ, g, «trimmed»)",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				below,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. g(x) ≤ extended_liminf(λn:num. f(n, x))"),
					a.TermAs[Set[A]]("λx:A. g(x) = «trimmed»(x)"))))
		same := a.Have(
			"so the two have the same integral",
			"nonneg_integral(Ω, S, μ, g) = nonneg_integral(Ω, S, μ, «trimmed»)",
			By(measure, agree, nonneg_integral.NonnegIntegralAE.At(Ω, S, μ, g, trimmed)))
		lowered := a.Have(
			"the trimmed function lies below the lower limit at every point, so its integral does",
			"nonneg_integral(Ω, S, μ, «trimmed») ≤ nonneg_integral(Ω, S, μ, «lower»)",
			By(
				extended_nonneg_real.ZeroLe,
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					trimmed,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("«lower»"))))
		a.Show(
			"and Fatou's lemma bounds the integral of the lower limit",
			By(same, lowered, measure, measurable, Fatou.At(Ω, S, μ, f), extended_nonneg_real.LeTrans))
	}),
})}
