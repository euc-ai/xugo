// integral_laws.go — the laws of the real integral on a measure space. The
// integral of f is the finite value of the integral of the embedding of f in
// [0, ∞] less that of the embedding of −f. Negation exchanges the two parts;
// a nonnegative factor moves through each; where f is a difference u − v of nonnegative measurable
// functions of finite integral, its integral is that of u less that of v,
// which makes the integral additive on integrable functions, finite sums
// included; the two parts of integrable functions compare as the functions
// do; and two measures that agree on the measurable sets integrate alike.

package measure_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegralOfNonneg — the integral of a function nonnegative on Ω is the
// finite value of the integral of its embedding in [0, ∞]: on Ω the
// embedding of −f is 0, so the integral of that part is 0, whose finite
// value is 0. No integrability is asked, and no structure of Ω, S or μ.
var IntegralOfNonneg = integralOfNonnegThm{family.Add(registry.ProofEntry{
	Name: "IntegralOfNonneg",
	Key:  "prop_ed548037c9efc985",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ⇒ &0 ≤ f(x)"},
		Conclusion: "measure_integral(Ω, S, μ, f) = " +
			"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x))))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		nonneg Fact,
	) {
		vanishing := a.Have(
			"on Ω the embedding of −f is 0",
			"∀x:A. x ∈ Ω ⇒ extended_of_real(-f(x)) = &0",
			ByArith(nonneg, extended_nonneg_real.OfRealNeg))
		negativeZero := a.Have(
			"so the integral of that part is the integral of the zero function, 0",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x))) = &0",
			By(
				vanishing,
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. &0")),
				nonneg_integral.NonnegIntegralZero.At(Ω, S, μ)))
		a.Show(
			"so of the two finite values whose difference is the integral, the second is 0",
			ByArith(negativeZero, RealIntegralDef.At(Ω, S, μ, f), extended_nonneg_real.ToRealZero))
	}),
})}

// IntegralNonnegEmbedding — the integral of an integrable function
// nonnegative on Ω, embedded in [0, ∞], is its nonnegative integral: the
// integral is the finite value of that nonnegative integral, which is finite
// as f is integrable, and a finite value embeds back as itself.
var IntegralNonnegEmbedding = integralNonnegEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "IntegralNonnegEmbedding",
	Key:  "prop_3728c4454948965",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ f(x)",
		},
		Conclusion: "extended_of_real(measure_integral(Ω, S, μ, f)) = " +
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		integrable, nonneg Fact,
	) {
		a.Show(
			"the integral is the finite value of a finite nonnegative integral, which embeds back as itself",
			By(
				integrable,
				nonneg,
				IntegralOfNonneg.At(Ω, S, μ, f),
				IntegrablePartsFinite.At(Ω, S, μ, f),
				extended_nonneg_real.OfRealToReal.At(
					a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))"))))
	}),
})}

// IntegralNonneg — a function nonnegative on Ω has a nonnegative integral:
// the integral is the finite value of the integral of the embedding of f,
// and a finite value is not negative. No integrability is asked, and no
// structure of Ω, S or μ.
var IntegralNonneg = integralNonnegThm{family.Add(registry.ProofEntry{
	Name: "IntegralNonneg",
	Key:  "prop_93081b738a631ead",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"∀x:A. x ∈ Ω ⇒ &0 ≤ f(x)"},
		Conclusion: "&0 ≤ measure_integral(Ω, S, μ, f)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		nonneg Fact,
	) {
		a.Show(
			"the integral is the finite value of the integral of the embedding of f, which is not negative",
			ByArith(
				nonneg,
				IntegralOfNonneg.At(Ω, S, μ, f),
				extended_nonneg_real.ToRealNonneg.At(
					a.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))"))))
	}),
})}

// IntegralIndicator — the cut of a real height c to a measurable set E has
// integral c times the measure of E. The embeddings of the cut and of its
// negative are the cuts of the embedded heights max(c, 0) and max(−c, 0),
// whose integrals are those heights times μ(E).
var IntegralIndicator = integralIndicatorThm{family.Add(registry.ProofEntry{
	Name: "IntegralIndicator",
	Key:  "prop_7737defdd1cc55eb",
	Reading: "No finiteness of μ(E) is asked: where μ(E) is " +
		"∞ both sides read 0, extended_to_real reading ∞ as 0.",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A). ∀c:real.",
		Hypotheses: []string{"E ∈ S"},
		Conclusion: "measure_integral(Ω, S, μ, λx:A. COND(x ∈ E, c, &0)) = c * extended_to_real(μ(E))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		c *Expr[Real],
		event Fact,
	) {
		embedded := a.Have(
			"the embedded cut of a real height integrates to the embedded height times the mass",
			"∀r:real. "+
				"    nonneg_integral(Ω, S, μ, λx:A. extended_of_real(COND(x ∈ E, r, &0))) = "+
				"    extended_of_real(r) * μ(E)",
			Derive(func(b *Argument) {
				b.FixAs[Real]("r")
				height := b.TermAs[ExtendedNonnegReal]("extended_of_real(r)")
				pushed := b.Have(
					"embedding the cut cuts the embedded height",
					"(λx:A. extended_of_real(COND(x ∈ E, r, &0))) = (λx:A. COND(x ∈ E, extended_of_real(r), &0))",
					CnfRefute())
				b.Show(
					"integrate the cut of the embedded height",
					By(pushed, measure, event, nonneg_integral.NonnegIntegralIndicator.At(Ω, S, μ, E, height)))
			}))
		negative := a.Have(
			"negating the cut negates its height",
			"(λx:A. -COND(x ∈ E, c, &0)) = (λx:A. COND(x ∈ E, -c, &0))",
			ByArith())
		a.Show(
			"the signed difference of the two heights is c",
			Simp(Fwd(RealIntegralDef)),
			Simp(
				Fwd(negative),
				Fwd(embedded),
				Fwd(extended_nonneg_real.ToRealMul),
				Fwd(extended_nonneg_real.ToRealOfRealMax)),
			ByArith())
	}),
})}

// IntegrableIndicator — the cut of a real height c to a measurable set E of
// finite measure is integrable: it is measurable, and its absolute value is
// the cut of |c|, whose integral |c|·μ(E) is finite.
var IntegrableIndicator = integrableIndicatorThm{family.Add(registry.ProofEntry{
	Name: "IntegrableIndicator",
	Key:  "prop_df2d7058710ebd50",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀E:set(A). ∀c:real.",
		Hypotheses: []string{"E ∈ S", "μ(E) ≠ extended_infinity"},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. COND(x ∈ E, c, &0))",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		E *Expr[Set[A]],
		c *Expr[Real],
		event, finite Fact,
	) {
		cut := a.TermAs[Fun[A, Real]]("λx:A. COND(x ∈ E, c, &0)")
		magnitude := a.TermAs[Real]("|c|")
		height := a.TermAs[ExtendedNonnegReal]("extended_of_real(|c|)")
		absolute := a.Have(
			"the embedded absolute value of the cut is the cut of the embedded |c|",
			"(λx:A. extended_of_real(|COND(x ∈ E, c, &0)|)) = (λx:A. COND(x ∈ E, extended_of_real(|c|), &0))",
			BySets(real_sgn_abs.AbsOfZero))
		measurable := a.Have(
			"the cut of a constant to a measurable set is measurable",
			"real_measurable(Ω, S, λx:A. COND(x ∈ E, c, &0))",
			By(
				measure,
				event,
				measure_space.MeasureOn.At(Ω, S, μ),
				measurable_function.RealMeasurableIndicator.At(Ω, S, E, c)))
		a.Show(
			"the cut has finite absolute integral |c|·μ(E)",
			By(
				measurable,
				absolute,
				measure,
				event,
				finite,
				nonneg_integral.NonnegIntegralIndicator.At(Ω, S, μ, E, height),
				RealIntegrableDef.At(Ω, S, μ, cut),
				extended_nonneg_real.OfRealNotInfinity.At(magnitude),
				extended_nonneg_real.MulEqInfinity.At(height, μ.Apply(E))))
	}),
})}

// IntegralZero — the zero function has integral 0: being nonnegative, its
// integral is the finite value of the integral of its embedding, the zero
// function of [0, ∞], whose integral is 0. No hypothesis is asked.
var IntegralZero = integralZeroThm{family.Add(registry.ProofEntry{
	Name: "IntegralZero",
	Key:  "prop_b16e3b9af91b5d50",
	Build: family.Theorem("∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). "+
		"    measure_integral(Ω, S, μ, λx:A. &0) = &0",
		func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal]) {
			a.Show(
				"the integral is the finite value of the integral of the zero function of [0, ∞], which is 0",
				By(
					IntegralOfNonneg.At(Ω, S, μ, a.TermAs[Fun[A, Real]]("λx:A. &0")),
					nonneg_integral.NonnegIntegralZero.At(Ω, S, μ),
					extended_nonneg_real.ToRealZero))
		}),
})}

// IntegralNeg — negating a function negates its integral: the embedding of
// −f is the second part of f, and that of −(−f) the first. No structure is
// asked of Ω, S or μ, and no integrability.
var IntegralNeg = integralNegThm{family.Add(registry.ProofEntry{
	Name: "IntegralNeg",
	Key:  "prop_441bd6295daa05d2",
	Build: family.Theorem("∀Ω:set(A). "+
		"∀S:set(set(A)). "+
		"∀μ:(set(A) → extended_nonneg_real). "+
		"∀f:(A → real). "+
		"    measure_integral(Ω, S, μ, λx:A. -f(x)) = -measure_integral(Ω, S, μ, f)",
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow[A, Real],
		) {
			twice := a.Have(
				"negating twice gives back f",
				"(λx:A. extended_of_real(--f(x))) = (λx:A. extended_of_real(f(x)))",
				Funext(),
				ByArith())
			a.Show(
				"so the two parts of −f are those of f, exchanged",
				Unfold(RealIntegralDef),
				twice.Rw(),
				ByArith())
		}),
})}

// IntegralScale — a real factor moves through the integral. For d ≥ 0 the
// embedding of d·r is the embedding of d times that of r, so the two parts of
// d·f are d times those of f, and the factor moves through their integrals
// and through the finite values. A negative c gives c·f, the negative of
// (−c)·f. No integrability is asked: where a part has an infinite integral,
// its finite value is 0 on both sides.
var IntegralScale = integralScaleThm{family.Add(registry.ProofEntry{
	Name: "IntegralScale",
	Key:  "prop_bdc0af47a6a7f369",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀f:(A → real). ∀c:real.",
		Conclusion: "measure_integral(Ω, S, μ, λx:A. c * f(x)) = c * measure_integral(Ω, S, μ, f)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow[A, Real],
		c *Expr[Real],
	) {
		positivePart := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))")
		negativePart := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))")
		nonnegFactor := a.Have(
			"a nonnegative factor moves through the integral",
			"∀d:real. &0 ≤ d ⇒ measure_integral(Ω, S, μ, λx:A. d * f(x)) = d * measure_integral(Ω, S, μ, f)",
			Derive(func(b *Argument) {
				d := b.FixAs[Real]("d")
				dNonneg := b.Assume()
				factor := b.TermAs[ExtendedNonnegReal]("extended_of_real(d)")
				embedded := b.Have(
					"the embedding of d·r is the embedding of d times that of r",
					"∀r:real. extended_of_real(d * r) = extended_of_real(d) * extended_of_real(r)",
					Derive(func(e *Argument) {
						r := e.FixAs[Real]("r")
						e.Cases(e.Term("&0 ≤ r"))
						e.When(
							"a nonnegative r embeds as itself, and so does d·r",
							func(g *Argument, rNonneg Fact) {
								g.Show(
									"the embedding multiplies nonnegative reals",
									By(dNonneg, rNonneg, extended_nonneg_real.OfRealMul.At(d, r)))
							})
						e.Otherwise(
							"a negative r and d·r both embed as 0",
							func(g *Argument, negative Fact) {
								g.Show(
									"d times 0 is 0",
									ByArith(
										dNonneg,
										negative,
										extended_nonneg_real.OfRealNeg.At(r),
										extended_nonneg_real.OfRealNeg.At(g.TermAs[Real]("d * r")),
										extended_nonneg_real.MulZero.At(factor)))
							})
					}))
				parts := b.Have(
					"so the two parts of d·f are d times those of f",
					"∀x:A. "+
						"    extended_of_real(d * f(x)) = extended_of_real(d) * extended_of_real(f(x)) ∧ "+
						"    extended_of_real(-(d * f(x))) = extended_of_real(d) * extended_of_real(-f(x))",
					Derive(func(e *Argument) {
						x := e.FixAs[A]("x")
						e.Show(
							"−(d·f(x)) is d·(−f(x))",
							ByArith(embedded.At(f.Apply(x)), embedded.At(e.TermAs[Real]("-f(x)"))))
					}))
				integrals := b.Have(
					"and the integrals of the two parts of d·f are d times those of f",
					"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(d) * extended_of_real(f(x))) = "+
						"extended_of_real(d) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x))) ∧ "+
						"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(d) * extended_of_real(-f(x))) = "+
						"extended_of_real(d) * nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x)))",
					By(
						measure,
						dNonneg,
						nonneg_integral.NonnegIntegralScale.At(Ω, S, μ, positivePart, d),
						nonneg_integral.NonnegIntegralScale.At(Ω, S, μ, negativePart, d)))
				b.Show(
					"the factor d moves through the finite values, d being the value of its embedding",
					Simp(Fwd(RealIntegralDef), Fwd(parts), Fwd(integrals), Fwd(extended_nonneg_real.ToRealMul)),
					ByArith(dNonneg, extended_nonneg_real.ToRealOfReal.At(d)))
			}))
		a.Cases(a.Term("&0 ≤ c"))
		a.When(
			"c is nonnegative",
			func(b *Argument, nonnegC Fact) {
				b.Show(
					"and moves through the integral",
					By(nonnegC, nonnegFactor.At(c)))
			})
		a.Otherwise(
			"c is negative, and c·f is the negative of (−c)·f",
			func(b *Argument, negativeC Fact) {
				flip := b.Have(
					"c·f is −((−c)·f)",
					"(λx:A. c * f(x)) = (λx:A. -((-c) * f(x)))",
					Funext(),
					ByArith())
				b.Show(
					"negation passes through the integral, and −c is positive",
					flip.Rw(),
					ByArith(
						negativeC,
						nonnegFactor.At(b.TermAs[Real]("-c")),
						IntegralNeg.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. (-c) * f(x)"))))
			})
	}),
})}

// IntegralMono — the integral is monotone on integrable functions: where
// f ≤ g on Ω, the embedding of f lies below that of g and the embedding of −g
// below that of −f, so their integrals, all four finite, compare the same
// way. No structure is asked of Ω, S or μ.
var IntegralMono = integralMonoThm{family.Add(registry.ProofEntry{
	Name: "IntegralMono",
	Key:  "prop_16af44674ae5673b",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
			"∀x:A. x ∈ Ω ⇒ f(x) ≤ g(x)",
		},
		Conclusion: "measure_integral(Ω, S, μ, f) ≤ measure_integral(Ω, S, μ, g)",
		Abbrev: Abbrev{
			{Name: "positiveF", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))"},
			{Name: "negativeF", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x)))"},
			{Name: "positiveG", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(g(x)))"},
			{Name: "negativeG", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-g(x)))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f, g *Arrow[A, Real],
		integrableF, integrableG, below Fact,
	) {
		parts := a.Have(
			"on Ω the embedding of f lies below that of g, and the embedding of −g below that of −f",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "extended_of_real(f(x)) ≤ extended_of_real(g(x)) ∧ " +
					"extended_of_real(-g(x)) ≤ extended_of_real(-f(x))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				fx := f.Apply(x)
				gx := g.Apply(x)
				le := b.Have(
					"f(x) ≤ g(x)",
					"f(x) ≤ g(x)",
					By(inΩ, below.At(x)))
				flipped := b.Have(
					"so −g(x) ≤ −f(x)",
					"-g(x) ≤ -f(x)",
					ByArith(le))
				b.Show(
					"the embedding is monotone",
					By(
						le,
						flipped,
						extended_nonneg_real.OfRealMono.At(fx, gx),
						extended_nonneg_real.OfRealMono.At(b.TermAs[Real]("-g(x)"), b.TermAs[Real]("-f(x)"))))
			}))
		values := a.Have(
			"so their integrals compare the same way, and all four are finite",
			"extended_to_real(«positiveF») ≤ extended_to_real(«positiveG») ∧ "+
				"extended_to_real(«negativeG») ≤ extended_to_real(«negativeF»)",
			By(
				integrableF,
				integrableG,
				parts,
				IntegrablePartsFinite.At(Ω, S, μ, f),
				IntegrablePartsFinite.At(Ω, S, μ, g),
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(g(x))")),
				nonneg_integral.NonnegIntegralMono.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-g(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))")),
				extended_nonneg_real.ExtendedLeDef))
		a.Show(
			"each integral is the value of its first part less that of its second",
			ByArith(values, RealIntegralDef.At(Ω, S, μ, f), RealIntegralDef.At(Ω, S, μ, g)))
	}),
})}

// IntegralAbsLe — the integral of an integrable function is at most, in
// absolute value, the integral of |f|: the integral is the difference of the
// values of its two parts, two nonnegative reals each at most the finite
// integral of |f|, since the embeddings of f and of −f lie below that of
// |f|. No structure is asked of Ω, S or μ.
var IntegralAbsLe = integralAbsLeThm{family.Add(registry.ProofEntry{
	Name: "IntegralAbsLe",
	Key:  "prop_d6f543d7cdcd727e",
	Build: family.Theorem(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{"real_integrable(Ω, S, μ, f)"},
		Conclusion: "|measure_integral(Ω, S, μ, f)| ≤ " +
			"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|)))",
		Abbrev: Abbrev{
			{Name: "positive", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))"},
			{Name: "negative", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x)))"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		f *Arrow[A, Real],
		integrable Fact,
	) {
		finite := a.Conjuncts(
			a.Unfolded(integrable, RealIntegrableDef),
			"f is measurable",
			"and |f| has a finite integral")[1]
		abs := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)")
		below := a.Have(
			"the embeddings of f and of −f lie below that of |f|",
			"∀x:A. "+
				"    extended_of_real(f(x)) ≤ extended_of_real(|f(x)|) ∧ "+
				"    extended_of_real(-f(x)) ≤ extended_of_real(|f(x)|)",
			ByArith(extended_nonneg_real.OfRealLe, real_sgn_abs.AbsNonneg))
		values := a.Have(
			"so the value of each part is at most the finite integral of |f|",
			"extended_to_real(«positive») ≤ "+
				"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|))) ∧ "+
				"extended_to_real(«negative») ≤ "+
				"extended_to_real(nonneg_integral(Ω, S, μ, λx:A. extended_of_real(|f(x)|)))",
			By(
				finite,
				below,
				nonneg_integral.NonnegIntegralMono.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"), abs),
				nonneg_integral.NonnegIntegralMono.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"), abs),
				extended_nonneg_real.ExtendedLeDef))
		a.Show(
			"and the integral is the difference of the two, both nonnegative",
			ByArith(
				values,
				RealIntegralDef.At(Ω, S, μ, f),
				extended_nonneg_real.ToRealNonneg.At(a.TermAs[ExtendedNonnegReal]("«positive»")),
				extended_nonneg_real.ToRealNonneg.At(a.TermAs[ExtendedNonnegReal]("«negative»"))))
	}),
})}

// IntegralAbsSubLe — where an integrable h bounds the distance |f − g| of
// two integrable functions on Ω, it bounds the distance of their integrals:
// h bounds f − g and g − f, and integrating each bound gives the two signed
// bounds on the difference of the integrals.
var IntegralAbsSubLe = integralAbsSubLeThm{family.Add(registry.ProofEntry{
	Name: "IntegralAbsSubLe",
	Key:  "prop_c351aaa65e877044",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g h:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
			"real_integrable(Ω, S, μ, h)",
			"∀x:A. x ∈ Ω ⇒ |f(x) - g(x)| ≤ h(x)",
		},
		Conclusion: "|measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g)| ≤ " +
			"measure_integral(Ω, S, μ, h)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g, h *Arrow[A, Real],
		integrableF, integrableG, integrableH, bound Fact,
	) {
		forward := a.Have(
			"the pointwise bound holds for the forward difference",
			"∀x:A. x ∈ Ω ⇒ f(x) - g(x) ≤ h(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inSpace := b.Assume()
				b.Show(
					"a real value is at most its absolute value",
					ByArith(inSpace, bound))
			}))
		backward := a.Have(
			"the bound holds for the reversed difference",
			"∀x:A. x ∈ Ω ⇒ g(x) - f(x) ≤ h(x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				inSpace := b.Assume()
				b.Show(
					"negating the difference preserves its absolute value",
					ByArith(inSpace, bound))
			}))
		fg := a.TermAs[Fun[A, Real]]("λx:A. f(x) - g(x)")
		gf := a.TermAs[Fun[A, Real]]("λx:A. g(x) - f(x)")
		above := a.Have(
			"integrate the forward difference",
			"measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g) ≤ measure_integral(Ω, S, μ, h)",
			ByArith(
				forward,
				measure,
				integrableF,
				integrableG,
				integrableH,
				IntegrableSub.At(Ω, S, μ, f, g),
				IntegralSub.At(Ω, S, μ, f, g),
				IntegralMono.At(Ω, S, μ, fg, h)))
		below := a.Have(
			"integrate the reversed difference",
			"measure_integral(Ω, S, μ, g) - measure_integral(Ω, S, μ, f) ≤ measure_integral(Ω, S, μ, h)",
			ByArith(
				backward,
				measure,
				integrableF,
				integrableG,
				integrableH,
				IntegrableSub.At(Ω, S, μ, g, f),
				IntegralSub.At(Ω, S, μ, g, f),
				IntegralMono.At(Ω, S, μ, gf, h)))
		a.Show(
			"the two signed bounds control the absolute difference",
			ByArith(above, below))
	}),
})}

// IntegralNonnegDifference — the integral does not depend on how f is
// written as a difference: where f = u − v on Ω for measurable u and v,
// nonnegative on Ω, whose embeddings have finite integrals, the integral of
// f is the value of the integral of u less that of v. On Ω, f is the
// measurable function u + (−v). Its positive part plus v and its negative
// part plus u embed as one function on Ω, so the integrals of the two sums
// agree and split; each part lies below u or v, so every integral in sight
// is finite, and the equation holds between the finite values.
var IntegralNonnegDifference = integralNonnegDifferenceThm{family.Add(registry.ProofEntry{
	Name: "IntegralNonnegDifference",
	Key:  "prop_ba81f22510cf4db8",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f u v:(A → real).",
		Hypotheses: []string{
			"real_measurable(Ω, S, u)",
			"real_measurable(Ω, S, v)",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ u(x)",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ v(x)",
			"«integralU» ≠ extended_infinity",
			"«integralV» ≠ extended_infinity",
			"∀x:A. x ∈ Ω ⇒ f(x) = u(x) - v(x)",
		},
		Conclusion: "measure_integral(Ω, S, μ, f) = " +
			"extended_to_real(«integralU») - extended_to_real(«integralV»)",
		Abbrev: Abbrev{
			{Name: "integralU", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(u(x)))"},
			{Name: "integralV", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(v(x)))"},
			{Name: "positive", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(u(x) + -v(x)))"},
			{Name: "negative", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-(u(x) + -v(x))))"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, u, v *Arrow[A, Real],
		uMeasurable, vMeasurable, uNonneg, vNonneg, uFinite, vFinite, difference Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		w := a.TermAs[Fun[A, Real]]("λx:A. u(x) + -v(x)")
		embedU := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(u(x))")
		embedV := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(v(x))")
		embedW := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(u(x) + -v(x))")
		embedNegativeW := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-(u(x) + -v(x)))")
		measurable := a.Have(
			"u + (−v) and its negative are measurable",
			"real_measurable(Ω, S, λx:A. u(x) + -v(x)) ∧ real_measurable(Ω, S, λx:A. -(u(x) + -v(x)))",
			By(
				sigma,
				uMeasurable,
				vMeasurable,
				measurable_function.RealMeasurableNeg.At(Ω, S, v),
				measurable_function.RealMeasurableAdd.At(Ω, S, u, a.TermAs[Fun[A, Real]]("λx:A. -v(x)")),
				measurable_function.RealMeasurableNeg.At(Ω, S, w)))
		embedded := a.Have(
			"so are the embeddings of u + (−v), of its negative, of u and of v",
			"extended_measurable(Ω, S, λx:A. extended_of_real(u(x) + -v(x))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(-(u(x) + -v(x)))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(u(x))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(v(x)))",
			By(
				sigma,
				uMeasurable,
				vMeasurable,
				measurable,
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, w),
				measurable_function.ExtendedMeasurableOfReal.At(
					Ω, S, a.TermAs[Fun[A, Real]]("λx:A. -(u(x) + -v(x))")),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, u),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, v)))
		agree := a.Have(
			"on Ω, f is u + (−v)",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "extended_of_real(f(x)) = extended_of_real(u(x) + -v(x)) ∧ " +
					"extended_of_real(-f(x)) = extended_of_real(-(u(x) + -v(x)))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				b.Show(
					"u(x) − v(x) is u(x) + (−v(x))",
					ByArith(inΩ, difference.At(x)))
			}))
		parts := a.Have(
			"so the two parts of f have the integrals of those of u + (−v)",
			"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x))) = «positive» ∧ "+
				"nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x))) = «negative»",
			By(
				agree,
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))"), embedW),
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω, S, μ, a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))"), embedNegativeW)))
		exchange := a.Have(
			"on Ω the embedding of u + (−v) plus that of v is the embedding of its negative plus that of u",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "extended_of_real(u(x) + -v(x)) + extended_of_real(v(x)) = " +
					"extended_of_real(-(u(x) + -v(x))) + extended_of_real(u(x))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				ux := u.Apply(x)
				vx := v.Apply(x)
				wx := b.TermAs[Real]("u(x) + -v(x)")
				negativeWx := b.TermAs[Real]("-(u(x) + -v(x))")
				zero := b.TermAs[ExtendedNonnegReal]("extended_of_real(&0)")
				nonneg := b.Have(
					"u(x) and v(x) are nonnegative",
					"&0 ≤ u(x) ∧ &0 ≤ v(x)",
					By(inΩ, uNonneg.At(x), vNonneg.At(x)))
				b.Cases(b.Term("v(x) ≤ u(x)"))
				b.When(
					"where v(x) ≤ u(x), the negative part is 0 and the positive part plus v(x) is u(x)",
					func(e *Argument, below Fact) {
						e.Show(
							"the embedding adds nonnegative reals",
							ByArith(
								below,
								nonneg,
								extended_nonneg_real.OfRealAdd.At(wx, vx),
								extended_nonneg_real.OfRealNeg.At(negativeWx),
								extended_nonneg_real.AddComm.At(zero, e.TermAs[ExtendedNonnegReal]("extended_of_real(u(x))")),
								extended_nonneg_real.AddZero.At(e.TermAs[ExtendedNonnegReal]("extended_of_real(u(x))"))))
					})
				b.Otherwise(
					"where u(x) < v(x), the positive part is 0 and the negative part plus u(x) is v(x)",
					func(e *Argument, above Fact) {
						e.Show(
							"the embedding adds nonnegative reals",
							ByArith(
								above,
								nonneg,
								extended_nonneg_real.OfRealAdd.At(negativeWx, ux),
								extended_nonneg_real.OfRealNeg.At(wx),
								extended_nonneg_real.AddComm.At(zero, e.TermAs[ExtendedNonnegReal]("extended_of_real(v(x))")),
								extended_nonneg_real.AddZero.At(e.TermAs[ExtendedNonnegReal]("extended_of_real(v(x))"))))
					})
			}))
		sums := a.Have(
			"so the integrals of the two sums agree, and each splits as a sum",
			"«positive» + «integralV» = «negative» + «integralU»",
			By(
				measure,
				embedded,
				exchange,
				nonneg_integral.NonnegIntegralEqOn.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, ExtendedNonnegReal]](
						"λx:A. extended_of_real(u(x) + -v(x)) + extended_of_real(v(x))"),
					a.TermAs[Fun[A, ExtendedNonnegReal]](
						"λx:A. extended_of_real(-(u(x) + -v(x))) + extended_of_real(u(x))")),
				nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, embedW, embedV),
				nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, embedNegativeW, embedU)))
		below := a.Have(
			"on Ω the embedding of u + (−v) lies below that of "+
				"u, and the embedding of its negative below that of v",
			Statement{
				Binders:    "∀x:A.",
				Hypotheses: []string{"x ∈ Ω"},
				Conclusion: "extended_of_real(u(x) + -v(x)) ≤ extended_of_real(u(x)) ∧ " +
					"extended_of_real(-(u(x) + -v(x))) ≤ extended_of_real(v(x))",
			},
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				inΩ := b.Assume()
				nonneg := b.Have(
					"u(x) and v(x) are nonnegative",
					"&0 ≤ u(x) ∧ &0 ≤ v(x)",
					By(inΩ, uNonneg.At(x), vNonneg.At(x)))
				b.Show(
					"the embedding keeps the order where the larger side is nonnegative",
					ByArith(
						nonneg,
						extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("u(x) + -v(x)"), u.Apply(x)),
						extended_nonneg_real.OfRealLe.At(b.TermAs[Real]("-(u(x) + -v(x))"), v.Apply(x))))
			}))
		finite := a.Have(
			"so both parts of u + (−v) have finite integrals",
			"«positive» ≠ extended_infinity ∧ «negative» ≠ extended_infinity",
			By(
				uFinite,
				vFinite,
				below,
				nonneg_integral.NonnegIntegralMono.At(Ω, S, μ, embedW, embedU),
				nonneg_integral.NonnegIntegralMono.At(Ω, S, μ, embedNegativeW, embedV),
				extended_nonneg_real.ExtendedLeDef))
		values := a.Have(
			"and the two sums, all four summands finite, agree as reals",
			"extended_to_real(«positive») + extended_to_real(«integralV») = "+
				"extended_to_real(«negative») + extended_to_real(«integralU»)",
			By(
				uFinite,
				vFinite,
				sums,
				finite,
				extended_nonneg_real.ToRealAdd.At(
					a.TermAs[ExtendedNonnegReal]("«positive»"), a.TermAs[ExtendedNonnegReal]("«integralV»")),
				extended_nonneg_real.ToRealAdd.At(
					a.TermAs[ExtendedNonnegReal]("«negative»"), a.TermAs[ExtendedNonnegReal]("«integralU»"))))
		a.Show(
			"the integral of f is the value of its first part less that of its second, the parts of u + (−v)",
			Simp(Fwd(RealIntegralDef), Fwd(parts)),
			ByArith(values))
	}),
})}

// IntegralAdd — the integral is additive on integrable functions. f + g is
// the sum of the positive parts of f and g less the sum of their negative
// parts: two nonnegative measurable functions, whose embeddings are the sums
// of the embeddings of f and g, and of −f and −g, so their integrals are the
// sums of the integrals of the parts, all finite. The integral of f + g is
// then the one sum less the other (IntegralNonnegDifference), which regroups
// as the integral of f plus that of g.
var IntegralAdd = integralAddThm{family.Add(registry.ProofEntry{
	Name: "IntegralAdd",
	Key:  "prop_8335c6aa1f128db6",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "measure_integral(Ω, S, μ, λx:A. f(x) + g(x)) = " +
			"measure_integral(Ω, S, μ, f) + measure_integral(Ω, S, μ, g)",
		Abbrev: Abbrev{
			{Name: "positive", Text: "nonneg_integral(Ω, " +
				"    S, " +
				"    μ, " +
				"    λx:A. extended_of_real(max(f(x), &0) + max(g(x), &0)))"},
			{Name: "negative", Text: "nonneg_integral(Ω, " +
				"    S, " +
				"    μ, " +
				"    λx:A. extended_of_real(max(-f(x), &0) + max(-g(x), &0)))"},
			{Name: "positiveF", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(f(x)))"},
			{Name: "negativeF", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-f(x)))"},
			{Name: "positiveG", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(g(x)))"},
			{Name: "negativeG", Text: "nonneg_integral(Ω, S, μ, λx:A. extended_of_real(-g(x)))"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		embedF := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))")
		embedG := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(g(x))")
		embedNegativeF := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))")
		embedNegativeG := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-g(x))")
		measurable := a.Have(
			"f and g are measurable",
			"real_measurable(Ω, S, f) ∧ real_measurable(Ω, S, g)",
			By(integrableF, integrableG, RealIntegrableDef.At(Ω, S, μ, f), RealIntegrableDef.At(Ω, S, μ, g)))
		sumsMeasurable := a.Have(
			"so are the sum of their positive parts and the sum of their negative parts",
			"real_measurable(Ω, S, λx:A. max(f(x), &0) + max(g(x), &0)) ∧ "+
				"real_measurable(Ω, S, λx:A. max(-f(x), &0) + max(-g(x), &0))",
			By(
				sigma,
				measurable,
				measurable_function.RealMeasurableParts.At(Ω, S, f),
				measurable_function.RealMeasurableParts.At(Ω, S, g),
				measurable_function.RealMeasurableAdd.At(
					Ω,
					S,
					a.TermAs[Fun[A, Real]]("λx:A. max(f(x), &0)"),
					a.TermAs[Fun[A, Real]]("λx:A. max(g(x), &0)")),
				measurable_function.RealMeasurableAdd.At(
					Ω,
					S,
					a.TermAs[Fun[A, Real]]("λx:A. max(-f(x), &0)"),
					a.TermAs[Fun[A, Real]]("λx:A. max(-g(x), &0)"))))
		embedded := a.Have(
			"and so are the embeddings of f, g, −f and −g",
			"extended_measurable(Ω, S, λx:A. extended_of_real(f(x))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(g(x))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(-f(x))) ∧ "+
				"extended_measurable(Ω, S, λx:A. extended_of_real(-g(x)))",
			By(
				sigma,
				measurable,
				measurable_function.RealMeasurableNeg.At(Ω, S, f),
				measurable_function.RealMeasurableNeg.At(Ω, S, g),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, f),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, g),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. -f(x)")),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. -g(x)"))))
		split := a.Have(
			"the sum of the positive parts embeds as the sum of the embeddings "+
				"of f and g, and the sum of the negative parts as that of −f and −g",
			"∀x:A. "+
				"    extended_of_real(max(f(x), &0) + max(g(x), &0)) = "+
				"    extended_of_real(f(x)) + extended_of_real(g(x)) ∧ "+
				"    extended_of_real(max(-f(x), &0) + max(-g(x), &0)) = "+
				"    extended_of_real(-f(x)) + extended_of_real(-g(x))",
			Derive(func(b *Argument) {
				x := b.FixAs[A]("x")
				b.Show(
					"the embedding adds nonnegative reals and reads a real at its positive part",
					ByArith(
						extended_nonneg_real.OfRealAdd.At(
							b.TermAs[Real]("max(f(x), &0)"), b.TermAs[Real]("max(g(x), &0)")),
						extended_nonneg_real.OfRealAdd.At(
							b.TermAs[Real]("max(-f(x), &0)"), b.TermAs[Real]("max(-g(x), &0)")),
						extended_nonneg_real.OfRealPositivePart.At(f.Apply(x)),
						extended_nonneg_real.OfRealPositivePart.At(g.Apply(x)),
						extended_nonneg_real.OfRealPositivePart.At(b.TermAs[Real]("-f(x)")),
						extended_nonneg_real.OfRealPositivePart.At(b.TermAs[Real]("-g(x)"))))
			}))
		sums := a.Have(
			"so the integrals of the embeddings of the two sums "+
				"are the sums of the integrals of the parts of f and g",
			"«positive» = «positiveF» + «positiveG» ∧ «negative» = «negativeF» + «negativeG»",
			Simp(Fwd(split)),
			By(
				measure,
				embedded,
				nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, embedF, embedG),
				nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, embedNegativeF, embedNegativeG)))
		positiveF := a.TermAs[ExtendedNonnegReal]("«positiveF»")
		negativeF := a.TermAs[ExtendedNonnegReal]("«negativeF»")
		positiveG := a.TermAs[ExtendedNonnegReal]("«positiveG»")
		negativeG := a.TermAs[ExtendedNonnegReal]("«negativeG»")
		values := a.Have(
			"the parts of integrable functions have finite integrals, so the sums are finite and add as reals",
			"«positive» ≠ extended_infinity ∧ "+
				"«negative» ≠ extended_infinity ∧ "+
				"extended_to_real(«positive») = extended_to_real(«positiveF») + extended_to_real(«positiveG») ∧ "+
				"extended_to_real(«negative») = extended_to_real(«negativeF») + extended_to_real(«negativeG»)",
			By(
				integrableF,
				integrableG,
				sums,
				IntegrablePartsFinite.At(Ω, S, μ, f),
				IntegrablePartsFinite.At(Ω, S, μ, g),
				extended_nonneg_real.AddEqInfinity.At(positiveF, positiveG),
				extended_nonneg_real.AddEqInfinity.At(negativeF, negativeG),
				extended_nonneg_real.ToRealAdd.At(positiveF, positiveG),
				extended_nonneg_real.ToRealAdd.At(negativeF, negativeG)))
		difference := a.Have(
			"f + g is the sum of the positive parts less the sum of the negative parts, both nonnegative",
			"∀x:A. "+
				"    &0 ≤ max(f(x), &0) + max(g(x), &0) ∧ "+
				"    &0 ≤ max(-f(x), &0) + max(-g(x), &0) ∧ "+
				"    f(x) + g(x) = (max(f(x), &0) + max(g(x), &0)) - (max(-f(x), &0) + max(-g(x), &0))",
			ByArith())
		whole := a.Have(
			"so the integral of f + g is the one integral less the other",
			"measure_integral(Ω, S, μ, λx:A. f(x) + g(x)) = "+
				"extended_to_real(«positive») - extended_to_real(«negative»)",
			By(
				measure,
				sumsMeasurable,
				difference,
				values,
				IntegralNonnegDifference.At(
					Ω,
					S,
					μ,
					a.TermAs[Fun[A, Real]]("λx:A. f(x) + g(x)"),
					a.TermAs[Fun[A, Real]]("λx:A. max(f(x), &0) + max(g(x), &0)"),
					a.TermAs[Fun[A, Real]]("λx:A. max(-f(x), &0) + max(-g(x), &0)"))))
		a.Show(
			"which regroups as the integral of f plus that of g",
			ByArith(whole, values, RealIntegralDef.At(Ω, S, μ, f), RealIntegralDef.At(Ω, S, μ, g)))
	}),
})}

// IntegralSub — the integral of a difference of integrable functions is the
// difference of their integrals: f − g is f plus (−1)·g, and the integral
// adds and moves the factor −1 out.
var IntegralSub = integralSubThm{family.Add(registry.ProofEntry{
	Name: "IntegralSub",
	Key:  "prop_a21f89344e70272c",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders: "∀f g:(A → real).",
		Hypotheses: []string{
			"real_integrable(Ω, S, μ, f)",
			"real_integrable(Ω, S, μ, g)",
		},
		Conclusion: "measure_integral(Ω, S, μ, λx:A. f(x) - g(x)) = " +
			"measure_integral(Ω, S, μ, f) - measure_integral(Ω, S, μ, g)",
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f, g *Arrow[A, Real],
		integrableF, integrableG Fact,
	) {
		minusOne := a.TermAs[Real]("-&1")
		sum := a.Have(
			"f − g is f plus (−1)·g",
			"(λx:A. f(x) - g(x)) = (λx:A. f(x) + -&1 * g(x))",
			Funext(),
			ByArith())
		a.Show(
			"the integral adds, and the factor −1 moves out of the integral of (−1)·g",
			sum.Rw(),
			ByArith(
				measure,
				integrableF,
				integrableG,
				IntegrableScale.At(Ω, S, μ, g, minusOne),
				IntegralScale.At(Ω, S, μ, g, minusOne),
				IntegralAdd.At(Ω, S, μ, f, a.TermAs[Fun[A, Real]]("λx:A. -&1 * g(x)"))))
	}),
})}

// IntegralFiniteSum — a finite sum of integrable functions is
// integrable, and its integral is the sum of their integrals: by induction on
// the number of terms, the empty sum being the zero function and each further
// term added by the additivity of the integral.
var IntegralFiniteSum = integralFiniteSumThm{family.Add(registry.ProofEntry{
	Name: "IntegralFiniteSum",
	Key:  "prop_67e396c4e1cf3138",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀z:(num → A → real). " +
			"∀n:num.",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀i:num. i < n ⇒ real_integrable(Ω, S, μ, z(i))",
		},
		Conclusion: "real_integrable(Ω, S, μ, λx:A. Σ_{i<n} z(i, x)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. Σ_{i<n} z(i, x)) = Σ_{i<n} measure_integral(Ω, S, μ, z(i))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact, z *Arrow2[Nat, A, Real], n *Expr[Nat]) {
		a.Induct(n)
		a.Base(
			"the empty sum is the zero function, integrable with integral zero",
			func(b *Argument) {
				b.Assume()
				zero := b.TermAs[Fun[A, Real]]("λx:A. &0")
				integrable := b.Have(
					"the zero function is measurable, and its size has integral 0, which is finite",
					"real_integrable(Ω, S, μ, λx:A. &0)",
					By(
						Normalized,
						measure,
						measure_space.MeasureOn.At(Ω, S, μ),
						measurable_function.RealMeasurableConst.At(Ω, S, b.TermAs[Real]("&0")),
						real_sgn_abs.AbsOfZero,
						nonneg_integral.NonnegIntegralZero.At(Ω, S, μ),
						extended_nonneg_real.OfRealNotInfinity,
						RealIntegrableDef.At(Ω, S, μ, zero)))
				b.Show(
					"the empty sums are 0",
					Simp(Fwd(real_sum.BelowClauses)),
					By(integrable, IntegralZero.At(Ω, S, μ)))
			})
		a.Step(
			"adjoining the next term adds its integral",
			func(b *Argument, previous Fact) {
				given := b.Assume()
				indices := b.Have(
					"all earlier indices and the new index belong to the longer sum",
					"(∀i:num. i < n ⇒ i < suc(n)) ∧ n < suc(n)",
					ByArith())
				earlier := b.Have(
					"the induction hypothesis integrates the shorter sum",
					"real_integrable(Ω, S, μ, λx:A. Σ_{i<n} z(i, x)) ∧ "+
						"measure_integral(Ω, S, μ, λx:A. Σ_{i<n} z(i, x)) = Σ_{i<n} measure_integral(Ω, S, μ, z(i))",
					By(given, indices, previous))
				last := b.Have(
					"the new term is integrable",
					"real_integrable(Ω, S, μ, z(n))",
					By(given, indices))
				sum := b.Have(
					"the longer sum is the shorter one plus the new term",
					"(λx:A. Σ_{i<suc(n)} z(i, x)) = (λx:A. (Σ_{i<n} z(i, x)) + z(n, x))",
					Funext(),
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						c.Show(
							"the sum recursion at this point",
							By(real_sum.BelowClauses.At(c.TermAs[Fun[Nat, Real]]("λi:num. z(i, x)"))))
					}))
				integrals := b.Have(
					"the sum of the integrals adds the new integral",
					"(Σ_{i<suc(n)} measure_integral(Ω, S, μ, z(i))) = "+
						"(Σ_{i<n} measure_integral(Ω, S, μ, z(i))) + measure_integral(Ω, S, μ, z(n))",
					By(real_sum.BelowClauses.At(b.TermAs[Fun[Nat, Real]]("λi:num. measure_integral(Ω, S, μ, z(i))"))))
				shorter := b.TermAs[Fun[A, Real]]("λx:A. Σ_{i<n} z(i, x)")
				term := b.TermAs[Fun[A, Real]]("z(n)")
				b.Show(
					"integrability and additivity of the integral give the longer sum",
					By(
						measure,
						earlier,
						last,
						sum,
						integrals,
						IntegrableAdd.At(Ω, S, μ, shorter, term),
						IntegralAdd.At(Ω, S, μ, shorter, term)))
			})
	}),
})}

// SquareIntegrableSum — a finite sum of measurable square-integrable functions
// is measurable and square-integrable, by induction on its length: the square
// of p + q lies below 2(p² + q²), which is integrable.
var SquareIntegrableSum = squareIntegrableSumThm{family.Add(registry.ProofEntry{
	Name: "SquareIntegrableSum",
	Key:  "prop_184804782ab280c7",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀z:(num → A → real). " +
			"∀n:num.",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"∀i:num. i < n ⇒ real_measurable(Ω, S, z(i)) ∧ real_integrable(Ω, S, μ, λx:A. z(i, x) * z(i, x))",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. Σ_{i<n} z(i, x)) ∧ " +
			"real_integrable(Ω, S, μ, λx:A. (Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x))",
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact, z *Arrow2[Nat, A, Real], n *Expr[Nat]) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		a.Induct(n)
		a.Base(
			"the empty sum is the zero function, measurable and integrable",
			func(b *Argument) {
				b.Assume()
				zero := b.Have(
					"the zero function is measurable, and its size has integral 0, which is finite",
					"real_measurable(Ω, S, λx:A. &0) ∧ real_integrable(Ω, S, μ, λx:A. &0)",
					By(
						Normalized,
						sigma,
						measurable_function.RealMeasurableConst.At(Ω, S, b.TermAs[Real]("&0")),
						real_sgn_abs.AbsOfZero,
						nonneg_integral.NonnegIntegralZero.At(Ω, S, μ),
						extended_nonneg_real.OfRealNotInfinity,
						RealIntegrableDef.At(Ω, S, μ, b.TermAs[Fun[A, Real]]("λx:A. &0"))))
				square := b.Have(
					"and its square is itself",
					"(λx:A. &0 * &0) = (λx:A. &0)",
					Funext(),
					ByArith())
				b.Show(
					"the empty sum and its square are the zero function",
					Simp(Fwd(real_sum.BelowClauses)),
					By(zero, square))
			})
		a.Step(
			"one more term adds a measurable square-integrable function",
			func(b *Argument, previous Fact) {
				given := b.Assume()
				indices := b.Have(
					"all earlier indices and the new index belong to the longer sum",
					"(∀i:num. i < n ⇒ i < suc(n)) ∧ n < suc(n)",
					ByArith())
				parts := b.Have(
					"the shorter sum is measurable and square-integrable, and so is the new term",
					"real_measurable(Ω, S, λx:A. Σ_{i<n} z(i, x)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. (Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x)) ∧ "+
						"real_measurable(Ω, S, z(n)) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. z(n, x) * z(n, x))",
					By(given, indices, previous))
				shorter := b.TermAs[Fun[A, Real]]("λx:A. Σ_{i<n} z(i, x)")
				longer := b.TermAs[Fun[A, Real]]("λx:A. Σ_{i<n} z(i, x) + z(n, x)")
				squares := b.TermAs[Fun[A, Real]]("λx:A. (Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x) + z(n, x) * z(n, x)")
				pointwise := b.Have(
					"(p + q)² ≤ 2(p² + q²), p the shorter sum and q the new term",
					Statement{
						Binders:    "∀x:A.",
						Hypotheses: []string{"x ∈ Ω"},
						Conclusion: "|(Σ_{i<n} z(i, x) + z(n, x)) * (Σ_{i<n} z(i, x) + z(n, x))| ≤ " +
							"&2 * ((Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x) + z(n, x) * z(n, x))",
					},
					Derive(func(c *Argument) {
						c.FixAs[A]("x")
						c.Assume()
						c.Show(
							"the squares of p − q and p + q are nonnegative",
							ByArith(
								real_order_ring.SquareNonneg.At(c.TermAs[Real]("Σ_{i<n} z(i, x) - z(n, x)")),
								real_order_ring.SquareNonneg.At(c.TermAs[Real]("Σ_{i<n} z(i, x) + z(n, x)")),
								real_sgn_abs.AbsFixedIffNonneg.At(
									c.TermAs[Real]("(Σ_{i<n} z(i, x) + z(n, x)) * (Σ_{i<n} z(i, x) + z(n, x))"))))
					}))
				measurable := b.Have(
					"p + q and its square are measurable, and 2(p² + q²) is integrable",
					"real_measurable(Ω, S, λx:A. Σ_{i<n} z(i, x) + z(n, x)) ∧ "+
						"real_measurable(Ω, S, λx:A. (Σ_{i<n} z(i, x) + z(n, x)) * (Σ_{i<n} z(i, x) + z(n, x))) ∧ "+
						"real_integrable(Ω, S, μ, λx:A. &2 * ((Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x) + z(n, x) * z(n, x)))",
					By(
						sigma,
						measure,
						parts,
						measurable_function.RealMeasurableAdd.At(Ω, S, shorter, b.TermAs[Fun[A, Real]]("z(n)")),
						measurable_function.RealMeasurableMul.At(Ω, S, longer, longer),
						IntegrableAdd.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("λx:A. (Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x)"),
							b.TermAs[Fun[A, Real]]("λx:A. z(n, x) * z(n, x)")),
						IntegrableScale.At(Ω, S, μ, squares, b.TermAs[Real]("&2"))))
				b.Show(
					"the longer sum adds the new term, and its square is dominated by 2(p² + q²)",
					Simp(Fwd(real_sum.BelowClauses)),
					By(
						pointwise,
						measurable,
						IntegrableDominated.At(
							Ω,
							S,
							μ,
							b.TermAs[Fun[A, Real]]("λx:A. (Σ_{i<n} z(i, x) + z(n, x)) * (Σ_{i<n} z(i, x) + z(n, x))"),
							b.TermAs[Fun[A, Real]]("λx:A. &2 * ((Σ_{i<n} z(i, x)) * Σ_{i<n} z(i, x) + z(n, x) * z(n, x))"))))
			})
	}),
})}

// IntegralEqualMeasures — two measures that agree on the measurable
// sets integrate alike: a function is integrable for one exactly when it is
// for the other, with the same integral. They give each level set of a
// simple function the same mass, so every simple function has the same
// simple integral for both; the simple minorants of a nonnegative function
// are then the same, and so are its nonnegative integrals; and integrability
// and the integral of a real function are read off the nonnegative integrals
// of |f|, f and −f.
var IntegralEqualMeasures = integralEqualMeasuresThm{family.Add(registry.ProofEntry{
	Name: "IntegralEqualMeasures",
	Key:  "prop_ba69e20aff4e6a53",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ ν:(set(A) → extended_nonneg_real). ∀f:(A → real).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"∀E:set(A). E ∈ S ⇒ μ(E) = ν(E)",
		},
		Conclusion: "(real_integrable(Ω, S, μ, f) ⇔ real_integrable(Ω, S, ν, f)) ∧ " +
			"measure_integral(Ω, S, μ, f) = measure_integral(Ω, S, ν, f)",
	}, func(ctx *Script, headline string) *GoalStackNode {
		simpleIntegralsAgree := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ ν:(set(A) → extended_nonneg_real). ∀f:(A → real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀E:set(A). E ∈ S ⇒ μ(E) = ν(E)",
				"measure_simple(Ω, S, f)",
			},
			Conclusion: "measure_simple_integral(Ω, μ, f) = measure_simple_integral(Ω, ν, f)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ, ν *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow[A, Real], sigma, agree, simple Fact) {
			levels := a.Have(
				"the two measures give each level set of f the same mass",
				"(λy:real. extended_of_real(y) * μ({x:A | x ∈ Ω ∧ f(x) = y})) = "+
					"λy:real. extended_of_real(y) * ν({x:A | x ∈ Ω ∧ f(x) = y})",
				Funext(),
				Derive(func(b *Argument) {
					y := b.FixAs[Real]("y")
					b.Show(
						"the level set at y is measurable",
						By(sigma, agree, simple, measure_simple.SimpleLevelSets.At(Ω, S, f, y)))
				}))
			a.Show(
				"so the simple integrals, sums over the levels of f, agree",
				Simp(Fwd(measure_simple.SimpleIntegralDef), Fwd(levels)),
				Basic())
		})
		nonnegativeIntegralsAgree := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ ν:(set(A) → extended_nonneg_real). " +
				"∀f:(A → extended_nonneg_real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"∀E:set(A). E ∈ S ⇒ μ(E) = ν(E)",
			},
			Conclusion: "nonneg_integral(Ω, S, μ, f) = nonneg_integral(Ω, S, ν, f)",
		}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ, ν *Arrow[Set[A], ExtendedNonnegReal],
			f *Arrow[A, ExtendedNonnegReal], sigma, agree Fact) {
			simple := a.Have(
				"every simple function has the same simple integral for both measures",
				Statement{
					Binders:    "∀s:(A → real).",
					Hypotheses: []string{"measure_simple(Ω, S, s)"},
					Conclusion: "measure_simple_integral(Ω, μ, s) = measure_simple_integral(Ω, ν, s)",
				},
				Derive(func(b *Argument) {
					s := b.FixAs[Fun[A, Real]]("s")
					isSimple := b.Assume()
					b.Show(
						"the simple integrals agree",
						By(sigma, agree, isSimple, At(simpleIntegralsAgree, Ω, S, μ, ν, s)))
				}))
			minorants := a.Have(
				"so the simple integrals below f are the same for both measures",
				"{r:extended_nonneg_real | "+
					"    ∃s:(A → real). "+
					"        measure_simple(Ω, S, s) ∧ "+
					"        (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)) ∧ "+
					"        r = measure_simple_integral(Ω, μ, s)} = "+
					"{r:extended_nonneg_real | "+
					"    ∃s:(A → real). "+
					"        measure_simple(Ω, S, s) ∧ "+
					"        (∀x:A. x ∈ Ω ⇒ extended_of_real(s(x)) ≤ f(x)) ∧ "+
					"        r = measure_simple_integral(Ω, ν, s)}",
				Simp(Fwd(set_basic.Extension)),
				Derive(func(b *Argument) {
					b.FixAs[ExtendedNonnegReal]("r")
					b.Iff()
					b.Forward(
						"a simple minorant of f with integral r for ν has integral r for μ",
						func(c *Argument, below Fact) {
							s, minorant := c.UnpackAs[Fun[A, Real]](below, "s")
							c.Show(
								"the same minorant serves",
								BySets(minorant, simple.At(s)))
						})
					b.Backward(
						"and one with integral r for μ has integral r for ν",
						func(c *Argument, below Fact) {
							s, minorant := c.UnpackAs[Fun[A, Real]](below, "s")
							c.Show(
								"the same minorant serves",
								BySets(minorant, simple.At(s)))
						})
				}))
			a.Show(
				"and so are their suprema, the two nonnegative integrals",
				Simp(Fwd(nonneg_integral.NonnegIntegralDef), Fwd(minorants)),
				Basic())
		})
		return ctx.Theorem(headline, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ, ν *Arrow[Set[A], ExtendedNonnegReal], f *Arrow[A, Real], sigma, agree Fact) {
			a.Show(
				"integrability and the integral are read off the nonnegative integrals of |f|, f and −f",
				By(
					sigma,
					agree,
					At(nonnegativeIntegralsAgree, Ω, S, μ, ν,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|f(x)|)")),
					At(nonnegativeIntegralsAgree, Ω, S, μ, ν,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(f(x))")),
					At(nonnegativeIntegralsAgree, Ω, S, μ, ν,
						a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(-f(x))")),
					RealIntegrableDef.At(Ω, S, μ, f),
					RealIntegralDef.At(Ω, S, μ, f),
					RealIntegrableDef.At(Ω, S, ν, f),
					RealIntegralDef.At(Ω, S, ν, f)))
		})
	}),
})}
