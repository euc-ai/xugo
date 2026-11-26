package measure_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegrableAE — functions equal almost everywhere are integrable together
// and have the same integral. Where f and g agree, so does any function of
// them; so |f| and |g|, and the positive and negative parts of f and g, are
// equal almost everywhere and have the same integrals.
var IntegrableAE = integrableAEThm{family.Add(registry.ProofEntry{
	Name: "IntegrableAE",
	Reading: "Measurability of f and g is load-bearing only for the integrability " +
		"equivalence, since S may be incomplete. The integral equality holds without it.",
	Key: "prop_33d02180b5f234da",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"real_measurable(Ω, S, f)",
			"real_measurable(Ω, S, g)",
			"measure_ae_eq(Ω, S, μ, f, g)",
		},
		Conclusion: "(real_integrable(Ω, S, μ, f) ⇔ real_integrable(Ω, S, μ, g)) ∧ " +
			"measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, μ, g)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, Real], measure, measurableF, measurableG, equal Fact) {
		agree := a.Unfolded(equal, measure_space.AEEqualDef)
		composed := a.Have(
			"wherever f and g agree, so does any function of them",
			"∀h:(real → extended_nonneg_real). measure_ae_eq(Ω, S, μ, λx:A. h(f(x)), λx:A. h(g(x)))",
			Derive(func(b *Argument) {
				b.FixAs[Fun[Real, ExtendedNonnegReal]]("h")
				b.Show(
					"h ∘ f and h ∘ g agree where f and g do",
					Simp(Fwd(measure_space.AEEqualDef)),
					By(
						agree,
						measure_space.AEMono.At(
							Ω,
							S,
							μ,
							b.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
							b.TermAs[Set[A]]("λx:A. h(f(x)) = h(g(x))"))))
			}))
		absolute := a.Have(
			"so |f| and |g| have the same integral",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|)) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|g(x)|))",
			By(
				measure,
				composed.At(a.TermAs[Fun[Real, ExtendedNonnegReal]]("λu:real. extended_of_real(|u|)")),
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|g(x)|)"))))
		positive := a.Have(
			"and so do their positive parts",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x))) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(g(x)))",
			By(
				measure,
				composed.At(a.TermAs[Fun[Real, ExtendedNonnegReal]]("λu:real. extended_of_real(u)")),
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(g(x))"))))
		negative := a.Have(
			"and their negative parts",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x))) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-g(x)))",
			By(
				measure,
				composed.At(a.TermAs[Fun[Real, ExtendedNonnegReal]]("λu:real. extended_of_real(-u)")),
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-g(x))"))))
		a.Show(
			"both are measurable, so integrability is the finiteness of the equal "+
				"integrals of |f| and |g|; and the integrals are built from equal parts",
			SplitConj(
				Case(
					"f and g are integrable together",
					By(measurableF, measurableG, absolute, RealIntegrableDef)),
				Case(
					"f and g have the same integral",
					By(positive, negative, RealIntegralDef))))
	}),
})}

// IntegralAE — functions equal almost everywhere have the same integral:
// where f and g agree, so do the embeddings of f and g, and of −f and −g, so
// the two parts have the same integrals. No measurability is asked.
var IntegralAE = integralAEThm{family.Add(registry.ProofEntry{
	Name: "IntegralAE",
	Key:  "prop_de84c1fd822108d",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"measure_ae_eq(Ω, S, μ, f, g)",
		},
		Conclusion: "measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, μ, g)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, Real],
		measure, equal Fact,
	) {
		agree := a.Unfolded(equal, measure_space.AEEqualDef)
		parts := a.Have(
			"wherever f and g agree, so do their embeddings, and those of −f and −g",
			"measure_ae_eq(Ω, S, μ, λx:A. extended_of_real(f(x)), λx:A. extended_of_real(g(x))) ∧ "+
				"measure_ae_eq(Ω, S, μ, λx:A. extended_of_real(-f(x)), λx:A. extended_of_real(-g(x)))",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				agree,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
					a.TermAs[Set[A]]("λx:A. extended_of_real(f(x)) = extended_of_real(g(x))")),
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. f(x) = g(x)"),
					a.TermAs[Set[A]]("λx:A. extended_of_real(-f(x)) = extended_of_real(-g(x))"))))
		a.Show(
			"so the two parts have the same integrals",
			By(
				measure,
				parts,
				RealIntegralDef.At(Ω, S, μ, f),
				RealIntegralDef.At(Ω, S, μ, g),
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(g(x))")),
				nonneg_integral.NonnegIntegralAE.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-g(x))"))))
	}),
})}

// AEBoundedIntegral — a measurable f bounded in size almost everywhere by an
// integrable g is integrable, and its integral is at most that of g in size.
// The bound fails only inside a measurable null set N; cut f and g to 0 on N.
// Almost every point lies off N, where the cuts are f and g, so the cut of g
// is integrable with the integral of g. At every point of Ω it bounds the cut
// of f in size, so the cut of f is integrable with integral at most that of g
// in size; and f, equal to it almost everywhere, is integrable with the same
// integral.
var AEBoundedIntegral = aEBoundedIntegralThm{family.Add(registry.ProofEntry{
	Name: "AEBoundedIntegral",
	Key:  "prop_d71de5c9f35b075d",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"real_measurable(Ω, S, f)",
			"real_integrable(Ω, S, μ, g)",
			"measure_ae(Ω, S, μ, λx:A. |f(x)| ≤ g(x))",
		},
		Conclusion: "real_integrable(Ω, S, μ, f) ∧ " +
			"|measure_integral(Ω, S, μ, f)| ≤ measure_integral(Ω, S, μ, g)",
		Abbrev: Abbrev{
			{Name: "cut", Text: "λN:set(A). λq:(A → real). λx:A. COND(x ∉ N, q(x), &0)"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, Real], measure, measurable, integrable, bounded Fact) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		exceptional := a.Conjuncts(
			a.Unfolded(a.Unfolded(bounded, measure_space.AlmostEverywhereDef), measure_space.NullSetDef),
			"the points of Ω where |f| exceeds g lie in Ω",
			"and in a measurable set N of measure zero")
		N, null := a.UnpackAs[Set[A]](exceptional[1], "N")
		covering := a.Conjuncts(
			null,
			"N is measurable",
			"N has measure zero",
			"N holds every point of Ω where |f| exceeds g")
		offN := a.Have(
			"so almost every point lies off N",
			"measure_ae(Ω, S, μ, λx:A. x ∉ N)",
			By(covering[0], covering[1], measure_space.AEOffNullSet.At(Ω, S, μ, N)))
		gMeasurable := a.Conjuncts(
			a.Unfolded(integrable, RealIntegrableDef),
			"g is measurable",
			"|g| has a finite integral")[0]
		cutF := a.TermAs[Fun[A, Real]]("«cut»(N, f)")
		cutG := a.TermAs[Fun[A, Real]]("«cut»(N, g)")
		cutsMeasurable := a.Have(
			"f and g cut to 0 on N are measurable",
			"real_measurable(Ω, S, «cut»(N, f)) ∧ real_measurable(Ω, S, «cut»(N, g))",
			By(
				sigma,
				covering[0],
				measurable,
				gMeasurable,
				measurable_function.RealMeasurableCut.At(Ω, S, N, f),
				measurable_function.RealMeasurableCut.At(Ω, S, N, g)))
		agree := a.Have(
			"off N the cuts are f and g, so they agree with f and g almost everywhere",
			"measure_ae_eq(Ω, S, μ, «cut»(N, f), f) ∧ measure_ae_eq(Ω, S, μ, «cut»(N, g), g)",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				offN,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. «cut»(N, f, x) = f(x)")),
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. «cut»(N, g, x) = g(x)"))))
		parts := a.Conjuncts(
			agree,
			"the cut of f agrees with f",
			"and the cut of g with g")
		cutGIntegral := a.Have(
			"so the cut of g is integrable with the integral of g",
			"real_integrable(Ω, S, μ, «cut»(N, g)) ∧ "+
				"measure_integral(Ω, S, μ, «cut»(N, g)) = measure_integral(Ω, S, μ, g)",
			By(measure, cutsMeasurable, gMeasurable, integrable, parts[1], IntegrableAE.At(Ω, S, μ, cutG, g)))
		within := a.Have(
			"at every point of Ω the cut of g bounds the cut of f in size",
			"∀x:A. x ∈ Ω ⇒ |«cut»(N, f, x)| ≤ «cut»(N, g, x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Cases(b.Term("x ∈ N"))
				b.When(
					"on N both cuts are 0",
					func(c *Argument, onN Fact) {
						c.Show(
							"and |0| ≤ 0",
							ByArith(onN, real_sgn_abs.AbsOfZero))
					})
				b.Otherwise(
					"off N the cuts are f and g, and the bound holds there",
					func(c *Argument, outN Fact) {
						kept := c.Have(
							"the cuts are f and g at x, and |f(x)| ≤ g(x)",
							"«cut»(N, f, x) = f(x) ∧ «cut»(N, g, x) = g(x) ∧ |f(x)| ≤ g(x)",
							BySets(inΩ, outN, covering[2]))
						c.Show(
							"so the bound is the one at x",
							ByArith(kept))
					})
			}))
		cutFIntegrable := a.Have(
			"so the cut of f is integrable",
			"real_integrable(Ω, S, μ, «cut»(N, f))",
			By(cutsMeasurable, within, cutGIntegral, IntegrableDominated.At(Ω, S, μ, cutF, cutG)))
		sameF := a.Have(
			"and so is f, with the same integral",
			"real_integrable(Ω, S, μ, f) ∧ "+
				"measure_integral(Ω, S, μ, «cut»(N, f)) = measure_integral(Ω, S, μ, f)",
			By(
				measure,
				cutsMeasurable,
				measurable,
				cutFIntegrable,
				parts[0],
				IntegrableAE.At(Ω, S, μ, cutF, f)))
		absCutF := a.TermAs[Fun[A, Real]]("λx:A. |«cut»(N, f, x)|")
		sizeBound := a.Have(
			"the integral of the cut of f is at most that of its size, at most that of the cut of g",
			"|measure_integral(Ω, S, μ, «cut»(N, f))| ≤ measure_integral(Ω, S, μ, «cut»(N, g))",
			By(
				sigma,
				cutFIntegrable,
				cutGIntegral,
				within,
				real_sgn_abs.AbsNonneg,
				IntegralAbsLe.At(Ω, S, μ, cutF),
				IntegralOfNonneg.At(Ω, S, μ, absCutF),
				IntegrableAbs.At(Ω, S, μ, cutF),
				IntegralMono.At(Ω, S, μ, absCutF, cutG),
				real_construction.LessEqTrans))
		a.Show(
			"f is integrable, and its integral and that of g are those of the cuts",
			By(sameF, cutGIntegral, sizeBound))
	}),
})}

// BoundedMeasurableProduct — a measurable h bounded by C almost everywhere
// multiplies an integrable f into an integrable h·f, with ∫|h·f| at most
// C·∫|f|. Cut h to 0 on a measurable null set N holding the points of Ω where
// |h| exceeds C. The cut k is measurable and bounded by C on Ω, so |k·f| is
// at most C·|f| there, an integrable function; so k·f and |k·f| are
// integrable, and ∫|k·f| ≤ ∫C·|f| = C·∫|f|. Off N, h·f is k·f, so h·f is
// integrable and ∫|h·f| = ∫|k·f|.
var BoundedMeasurableProduct = boundedMeasurableProductThm{family.Add(registry.ProofEntry{
	Name: "BoundedMeasurableProduct",
	Key:  "prop_d5c662230d893c06",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀f h:(A → real). " +
			"∀C:real.",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"real_integrable(Ω, S, μ, f)",
			"real_measurable(Ω, S, h)",
			"&0 ≤ C",
			"measure_ae(Ω, S, μ, λx:A. |h(x)| ≤ C)",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. h(x) * f(x)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. |h(x) * f(x)|) ≤ C * measure_integral(Ω, S, μ, λx:A. |f(x)|)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		f, h *Arrow[A, Real], C *Expr[Real], measure, integrable, measurable, nonneg, bounded Fact) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		exceptional := a.Conjuncts(
			a.Unfolded(a.Unfolded(bounded, measure_space.AlmostEverywhereDef), measure_space.NullSetDef),
			"the points of Ω where |h| exceeds C lie in Ω",
			"and in a measurable set N of measure zero")
		N, null := a.UnpackAs[Set[A]](exceptional[1], "N")
		covering := a.Conjuncts(
			null,
			"N is measurable",
			"N has measure zero",
			"N holds every point of Ω where |h| exceeds C")
		offN := a.Have(
			"almost every point lies off N",
			"measure_ae(Ω, S, μ, λx:A. x ∉ N)",
			By(covering[0], covering[1], measure_space.AEOffNullSet.At(Ω, S, μ, N)))
		fParts := a.Conjuncts(
			a.Unfolded(integrable, RealIntegrableDef),
			"f is measurable",
			"|f| has a finite integral")
		cut := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∉ N, h(x), &0)")
		cutTimesF := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∉ N, h(x), &0) * f(x)")
		absCutTimesF := a.TermAs[Fun[A, Real]]("λx:A. |COND(x ∉ N, h(x), &0) * f(x)|")
		absF := a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")
		dominating := a.TermAs[Fun[A, Real]]("λx:A. C * |f(x)|")
		measurableCut := a.Have(
			"h cut to 0 on N is measurable",
			"real_measurable(Ω, S, λx:A. COND(x ∉ N, h(x), &0))",
			By(sigma, covering[0], measurable, measurable_function.RealMeasurableCut.At(Ω, S, N, h)))
		products := a.Have(
			"so are h·f and the cut times f, and the size of the latter",
			"real_measurable(Ω, S, λx:A. h(x) * f(x)) ∧ "+
				"real_measurable(Ω, S, λx:A. COND(x ∉ N, h(x), &0) * f(x)) ∧ "+
				"real_measurable(Ω, S, λx:A. |COND(x ∉ N, h(x), &0) * f(x)|)",
			By(
				sigma,
				measurable,
				measurableCut,
				fParts[0],
				measurable_function.RealMeasurableMul.At(Ω, S, h, f),
				measurable_function.RealMeasurableMul.At(Ω, S, cut, f),
				measurable_function.RealMeasurableAbs.At(Ω, S, cutTimesF)))
		integrableAbsF := a.Have(
			"|f| is integrable, f being integrable",
			"real_integrable(Ω, S, μ, λx:A. |f(x)|)",
			By(sigma, integrable, IntegrableAbs.At(Ω, S, μ, f)))
		integrableBound := a.Have(
			"so is C·|f|",
			"real_integrable(Ω, S, μ, λx:A. C * |f(x)|)",
			By(measure, integrableAbsF, IntegrableScale.At(Ω, S, μ, absF, C)))
		within := a.Have(
			"on Ω the cut times f is at most C·|f| in size",
			"∀x:A. x ∈ Ω ⇒ |COND(x ∉ N, h(x), &0) * f(x)| ≤ C * |f(x)|",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Cases(b.Term("x ∈ N"))
				b.When(
					"on N the cut is 0",
					func(c *Argument, inN Fact) {
						zero := c.Have(
							"the cut vanishes at x",
							"COND(x ∉ N, h(x), &0) = &0",
							By(inN))
						c.Show(
							"0 lies below C·|f(x)|, C being nonnegative",
							ByArith(zero, nonneg))
					})
				b.Otherwise(
					"off N the cut is h, bounded by C",
					func(c *Argument, outN Fact) {
						kept := c.Have(
							"the cut is h at x, and |h(x)| ≤ C",
							"COND(x ∉ N, h(x), &0) = h(x) ∧ |h(x)| ≤ C",
							BySets(inΩ, outN, covering[2]))
						c.Show(
							"so |h(x)·f(x)| = |h(x)|·|f(x)| ≤ C·|f(x)|",
							ByArith(kept, real_sgn_abs.AbsMul))
					})
			}))
		cutIntegrable := a.Have(
			"so the cut times f and its size are integrable",
			"real_integrable(Ω, S, μ, λx:A. COND(x ∉ N, h(x), &0) * f(x)) ∧ "+
				"real_integrable(Ω, S, μ, λx:A. |COND(x ∉ N, h(x), &0) * f(x)|)",
			By(
				products,
				within,
				integrableBound,
				real_sgn_abs.AbsIdempotent,
				IntegrableDominated.At(Ω, S, μ, cutTimesF, dominating),
				IntegrableDominated.At(Ω, S, μ, absCutTimesF, dominating)))
		agree := a.Have(
			"off N, h·f and its size are those of the cut times f, so almost everywhere",
			"measure_ae_eq(Ω, S, μ, λx:A. h(x) * f(x), λx:A. COND(x ∉ N, h(x), &0) * f(x)) ∧ "+
				"measure_ae_eq(Ω, S, μ, λx:A. |h(x) * f(x)|, λx:A. |COND(x ∉ N, h(x), &0) * f(x)|)",
			Simp(Fwd(measure_space.AEEqualDef)),
			By(
				offN,
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. h(x) * f(x) = COND(x ∉ N, h(x), &0) * f(x)")),
				measure_space.AEMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Set[A]]("λx:A. x ∉ N"),
					a.TermAs[Set[A]]("λx:A. |h(x) * f(x)| = |COND(x ∉ N, h(x), &0) * f(x)|"))))
		parts := a.Conjuncts(
			agree,
			"h·f agrees with the cut times f",
			"and so does its size")
		productIntegrable := a.Have(
			"so h·f is integrable",
			"real_integrable(Ω, S, μ, λx:A. h(x) * f(x))",
			By(
				measure,
				products,
				parts[0],
				cutIntegrable,
				IntegrableAE.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. h(x) * f(x)"), cutTimesF)))
		sameIntegral := a.Have(
			"and the integral of |h·f| is that of the size of the cut times f",
			"measure_integral(Ω, S, μ, λx:A. |h(x) * f(x)|) = "+
				"measure_integral(Ω, S, μ, λx:A. |COND(x ∉ N, h(x), &0) * f(x)|)",
			By(
				measure,
				parts[1],
				IntegralAE.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. |h(x) * f(x)|"), absCutTimesF)))
		dominated := a.Have(
			"which is at most the integral of C·|f|",
			"measure_integral(Ω, S, μ, λx:A. |COND(x ∉ N, h(x), &0) * f(x)|) ≤ "+
				"measure_integral(Ω, S, μ, λx:A. C * |f(x)|)",
			By(cutIntegrable, integrableBound, within, IntegralMono.At(Ω, S, μ, absCutTimesF, dominating)))
		a.Show(
			"h·f is integrable, and C·∫|f| is the integral of C·|f|",
			SplitConj(
				Case(
					"h·f is integrable",
					By(productIntegrable)),
				Case(
					"its size has integral at most C times that of |f|",
					ByArith(sameIntegral, dominated, measure, IntegralScale.At(Ω, S, μ, absF, C)))))
	}),
})}

// SubSigmaRealIntegral — on a sub-sigma-algebra G of S a G-measurable real
// function is integrable for G exactly when it is for S, with the same
// integral. It is S-measurable too, its rays lying in G ⊆ S; and |f| and
// the positive and negative parts of f, embedded in [0, ∞], are
// G-measurable, so each has the same integral for G and for S.
var SubSigmaRealIntegral = subSigmaRealIntegralThm{family.Add(registry.ProofEntry{
	Name: "SubSigmaRealIntegral",
	Key:  "prop_9323c8485e928ed8",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀f:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"real_measurable(Ω, G, f)",
		},
		Conclusion: "(real_integrable(Ω, G, μ, f) ⇔ real_integrable(Ω, S, μ, f)) ∧ " +
			"measure_integral(Ω, G, μ, f) = measure_integral(Ω, S, μ, f)",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		G *Expr[Set[Set[A]]], f *Arrow[A, Real], measure, sigmaG, sub, measurable Fact) {
		laws := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigmaS := laws[0]
		measurableS := a.Have(
			"f is S-measurable, its rays lying in G ⊆ S",
			"real_measurable(Ω, S, f)",
			By(
				sigmaG,
				measurable,
				measurable_function.RealMeasurableIffRay.At(Ω, G, f),
				sigmaS,
				sub,
				set_basic.SubsetDef,
				measurable_function.RealMeasurableIffRay.At(Ω, S, f)))
		absolute := a.Have(
			"|f| has the same integral for G and for S",
			"nonneg_integral(Ω, G, μ, λx:A. extended_of_real(|f(x)|)) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|))",
			By(
				measure,
				sigmaG,
				sub,
				measurable,
				measurable_function.RealMeasurableAbs.At(Ω, G, f),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, G, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|")),
				nonneg_integral.SubSigmaIntegral.At(
					Ω,
					S,
					μ,
					G,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)"))))
		positive := a.Have(
			"and so does its positive part",
			"nonneg_integral(Ω, G, μ, λx:A. extended_of_real(f(x))) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))",
			By(
				measure,
				sigmaG,
				sub,
				measurable,
				measurable_function.ExtendedMeasurableOfReal.At(Ω, G, f),
				nonneg_integral.SubSigmaIntegral.At(
					Ω, S, μ, G, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"))))
		negative := a.Have(
			"and its negative part",
			"nonneg_integral(Ω, G, μ, λx:A. extended_of_real(-f(x))) = "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x)))",
			By(
				measure,
				sigmaG,
				sub,
				measurable,
				measurable_function.RealMeasurableNeg.At(Ω, G, f),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, G, a.TermAs[Fun[A, Real]]("λx:A. -f(x)")),
				nonneg_integral.SubSigmaIntegral.At(
					Ω,
					S,
					μ,
					G,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"))))
		a.Show(
			"f is measurable for both, and integrability and the integral are read off equal integrals",
			SplitConj(
				Case(
					"f is integrable for G exactly when it is for S",
					By(measurable, measurableS, absolute, RealIntegrableDef)),
				Case(
					"the two integrals agree",
					By(positive, negative, RealIntegralDef))))
	}),
})}
