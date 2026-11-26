// seminorm.go — the function layer of the Lebesgue seminorm: positive
// powers of measurable functions, the pth power of |f| for f in Lᵖ and its
// integral ‖f‖ₚᵖ, the functions of seminorm zero, and Hölder's inequality
// for conjugate exponents.

package lp_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/almost_everywhere_function"
	"github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_convex"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_rpow"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// RealMeasurableRpow — a positive power of a measurable function is
// measurable. Every power exceeds a negative level, and for c ≥ 0 the power
// u(x)^p exceeds c exactly where u(x) exceeds c^(1/p): where u(x) is not
// positive the power is 0, and on the positive reals the power is
// increasing and the (1/p)th power undoes it.
var RealMeasurableRpow = realMeasurableRpowThm{family.Add(registry.ProofEntry{
	Name: "RealMeasurableRpow",
	Key:  "prop_708ddac22bf3b9da",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀u:(A → real). ∀p:real.",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"real_measurable(Ω, S, u)",
			"&0 < p",
		},
		Conclusion: "real_measurable(Ω, S, λx:A. real_rpow(u(x), p))",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		u *Arrow[A, Real],
		p *Expr[Real],
		sigma, measurable, positive Fact,
	) {
		inverseP := a.TermAs[Real]("real_inv(p)")
		uRays := a.Have(
			"u exceeds each level on a measurable set",
			"∀r:real. {x:A | x ∈ Ω ∧ r < u(x)} ∈ S",
			By(sigma, measurable, measurable_function.RealMeasurableIffRay.At(Ω, S, u)))
		reciprocal := a.Have(
			"p and 1/p are reciprocal",
			"real_inv(p) * p = &1 ∧ p * real_inv(p) = &1",
			ByArith(positive))
		rays := a.Have(
			"so does u^p",
			"∀c:real. {x:A | x ∈ Ω ∧ c < real_rpow(u(x), p)} ∈ S",
			Derive(func(b *Argument) {
				c := b.FixAs[Real]("c")
				b.Cases(b.Term("&0 ≤ c"))
				b.When(
					"for c ≥ 0, u^p exceeds c exactly where u exceeds c^(1/p)",
					func(d *Argument, nonnegC Fact) {
						root := d.TermAs[Real]("real_rpow(c, real_inv(p))")
						rootFacts := d.Have(
							"c^(1/p) is nonnegative and its pth power is c",
							"&0 ≤ real_rpow(c, real_inv(p)) ∧ real_rpow(real_rpow(c, real_inv(p)), p) = c",
							ByArith(
								nonnegC,
								reciprocal,
								real_rpow.RpowNonneg.At(c, inverseP),
								real_rpow.RpowRpow.At(c, inverseP, p),
								real_rpow.RpowOneExponent.At(c)))
						pointwise := d.Have(
							"c < u(x)^p exactly when c^(1/p) < u(x)",
							"∀x:A. c < real_rpow(u(x), p) ⇔ real_rpow(c, real_inv(p)) < u(x)",
							Derive(func(e *Argument) {
								x := e.FixAs[A]("x")
								power := e.TermAs[Real]("real_rpow(u(x), p)")
								e.Iff()
								e.Forward(
									"the (1/p)th power is increasing, and it takes u(x)^p back to u(x)",
									func(g *Argument, above Fact) {
										positiveU := g.Assuming(
											g.TermAs[Bool]("&0 < u(x)"),
											"where u(x) is not positive its power is 0, which does not exceed c",
											Given(func(h *Argument, notPositive Fact) {
												h.Show(
													"u(x)^p is 0 at a base that is not positive and an exponent that is not 0",
													ByArith(nonnegC, above, positive, notPositive, real_rpow.RealRpowDef.At(u.Apply(x), p)))
											}))
										g.Show(
											"c^(1/p) < (u(x)^p)^(1/p) = u(x)",
											ByArith(
												nonnegC,
												above,
												positive,
												reciprocal,
												positiveU,
												real_rpow.RpowLessBase.At(c, power, inverseP),
												real_rpow.RpowRpow.At(u.Apply(x), p, inverseP),
												real_rpow.RpowOneExponent.At(u.Apply(x))))
									})
								e.Backward(
									"the pth power is increasing, and it takes c^(1/p) back to c",
									func(g *Argument, beyond Fact) {
										g.Show(
											"c = (c^(1/p))^p < u(x)^p",
											ByArith(positive, beyond, rootFacts, real_rpow.RpowLessBase.At(root, u.Apply(x), p)))
									})
							}))
						same := d.Have(
							"so the two sets agree",
							"{x:A | x ∈ Ω ∧ c < real_rpow(u(x), p)} = {x:A | x ∈ Ω ∧ real_rpow(c, real_inv(p)) < u(x)}",
							BySets(pointwise))
						d.Show(
							"and the second is measurable",
							By(same, uRays.At(root)))
					})
				b.Otherwise(
					"every power exceeds a negative level",
					func(d *Argument, negative Fact) {
						above := d.Have(
							"each power is nonnegative, so above c",
							"∀x:A. c < real_rpow(u(x), p)",
							ByArith(negative, real_rpow.RpowNonneg))
						whole := d.Have(
							"so the set is Ω",
							"{x:A | x ∈ Ω ∧ c < real_rpow(u(x), p)} = Ω",
							BySets(above))
						d.Show(
							"which is measurable",
							By(whole, sigma, sigma_algebra.SigmaAlgebraOnDef))
					})
			}))
		a.Show(
			"its rays decide its measurability",
			By(
				sigma,
				rays,
				measurable_function.RealMeasurableIffRay.At(
					Ω, S, a.TermAs[Fun[A, Real]]("λx:A. real_rpow(u(x), p)"))))
	}),
})}

// LpSeminormNonneg — the p-seminorm of a function is nonnegative, being a
// real power.
var LpSeminormNonneg = lpSeminormNonnegThm{family.Add(registry.ProofEntry{
	Name: "LpSeminormNonneg",
	Key:  "prop_3838d5b2f40d6dd3",
	Build: family.Theorem(
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. ∀f:(A → complex). "+
			"    &0 ≤ lp_seminorm(Ω, S, μ, p, f)",
		func(
			a *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal],
			p *Expr[Real],
			f *Arrow[A, Complex],
		) {
			a.Show(
				"a real power is nonnegative",
				By(LpSeminormDef.At(Ω, S, μ, p, f), real_rpow.RpowNonneg))
		}),
})}

// LpPowerIntegral — for p > 0 and f in Lᵖ, the pth power of |f| is
// integrable and its integral is ‖f‖ₚᵖ. The power is measurable, a
// positive power of the measurable |f|, and it is its own absolute value,
// so the finiteness lp_functions asks for is its integrability. Being
// nonnegative, its integral is the real value of its nonnegative integral
// I, and ‖f‖ₚᵖ = (I^(1/p))^p = I.
var LpPowerIntegral = lpPowerIntegralThm{family.Add(registry.ProofEntry{
	Name: "LpPowerIntegral",
	Key:  "prop_a0aa4f80e55709ca",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀f:(A → complex).",
		Hypotheses: []string{
			"sigma_algebra_on(Ω, S)",
			"&0 < p",
			"f ∈ lp_functions(Ω, S, μ, p)",
		},
		Conclusion: "real_integrable(Ω, S, μ, «absPow»(p, f)) ∧ " +
			"measure_integral(Ω, S, μ, «absPow»(p, f)) = real_rpow(lp_seminorm(Ω, S, μ, p, f), p)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		p *Expr[Real],
		f *Arrow[A, Complex],
		sigma, positive, inLp Fact,
	) {
		power := a.TermAs[Fun[A, Real]]("«absPow»(p, f)")
		integral := a.TermAs[ExtendedNonnegReal]("«absPowIntegral»(Ω, S, μ, p, f)")
		measurableF := a.Have(
			"f is measurable",
			"complex_measurable(Ω, S, f)",
			BySets(
				inLp,
				LpFunctionsDef.At(Ω, S, μ, p),
				almost_everywhere_function.MeasurableFunctionsDef.At(Ω, S)))
		finite := a.Have(
			"and |f|^p has finite nonnegative integral",
			"«absPowIntegral»(Ω, S, μ, p, f) ≠ extended_infinity",
			BySets(inLp, LpFunctionsDef.At(Ω, S, μ, p)))
		measurablePower := a.Have(
			"|f|^p is measurable, a positive power of the measurable |f|",
			"real_measurable(Ω, S, «absPow»(p, f))",
			By(
				sigma,
				measurableF,
				positive,
				complex_measure_integral.ComplexMeasurableAbs.At(Ω, S, f),
				RealMeasurableRpow.At(Ω, S, a.TermAs[Fun[A, Real]]("λx:A. |f(x)|"), p)))
		ownAbs := a.Have(
			"|f|^p is its own absolute value",
			"(λx:A. extended_of_real(|«absPow»(p, f, x)|)) = (λx:A. extended_of_real(«absPow»(p, f, x)))",
			Funext(),
			ByArith(real_rpow.RpowNonneg))
		integrable := a.Have(
			"so |f|^p is integrable",
			"real_integrable(Ω, S, μ, «absPow»(p, f))",
			By(finite, ownAbs, measurablePower, measure_integral.RealIntegrableDef.At(Ω, S, μ, power)))
		realValue := a.TermAs[Real]("extended_to_real(«absPowIntegral»(Ω, S, μ, p, f))")
		reciprocal := a.Have(
			"1/p and p are reciprocal",
			"real_inv(p) * p = &1",
			ByArith(positive))
		seminorm := a.Have(
			"‖f‖ₚᵖ = (I^(1/p))^p = I",
			"real_rpow(lp_seminorm(Ω, S, μ, p, f), p) = extended_to_real(«absPowIntegral»(Ω, S, μ, p, f))",
			ByArith(
				reciprocal,
				LpSeminormDef.At(Ω, S, μ, p, f),
				real_rpow.RpowRpow.At(realValue, a.TermAs[Real]("real_inv(p)"), p),
				extended_nonneg_real.ToRealNonneg.At(integral),
				real_rpow.RpowOneExponent.At(realValue)))
		a.Show(
			"|f|^p is integrable, and its integral, a nonnegative "+
				"function's, is the real value of I, which is ‖f‖ₚᵖ",
			By(
				integrable,
				seminorm,
				real_rpow.RpowNonneg,
				measure_integral.IntegralOfNonneg.At(Ω, S, μ, power)))
	}),
})}

// LpSeminormZeroIffAE — for p > 0 and f in Lᵖ, the seminorm of f is zero
// exactly when f vanishes almost everywhere. ‖f‖ₚ is zero exactly when
// ‖f‖ₚᵖ is, which is the nonnegative integral of |f|^p; that integral of a
// measurable function is zero exactly when the function vanishes almost
// everywhere, and |f(x)|^p vanishes exactly where f(x) does.
var LpSeminormZeroIffAE = lpSeminormZeroIffAEThm{family.Add(registry.ProofEntry{
	Name: "LpSeminormZeroIffAE",
	Reading: "Membership in Lᵖ is load-bearing: for a measurable f with ∫|f|^p = ∞ the seminorm " +
		"reads extended_to_real(∞) = 0, so it is 0 although f need not vanish almost everywhere.",
	Key: "prop_2ee6ed0c77acd6e9",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀f:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"&0 < p",
			"f ∈ lp_functions(Ω, S, μ, p)",
		},
		Conclusion: "lp_seminorm(Ω, S, μ, p, f) = &0 ⇔ measure_ae(Ω, S, μ, λx:A. f(x) = &0)",
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		p *Expr[Real],
		f *Arrow[A, Complex],
		measure, positive, inLp Fact,
	) {
		power := a.TermAs[Fun[A, Real]]("«absPow»(p, f)")
		embedded := a.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(«absPow»(p, f, x))")
		zero := a.TermAs[Real]("&0")
		norm := a.TermAs[Real]("lp_seminorm(Ω, S, μ, p, f)")
		sigma := a.Have(
			"μ's measurable sets form a σ-algebra",
			"sigma_algebra_on(Ω, S)",
			By(measure, measure_space.MeasureOn))
		powerFacts := a.Conjuncts(
			GroupPremises(sigma, positive, inLp, LpPowerIntegral.At(Ω, S, μ, p, f)),
			"|f|^p is integrable",
			"with integral ‖f‖ₚᵖ")
		measurableEmbedded := a.Have(
			"so |f|^p, embedded in the extended reals, is measurable",
			"extended_measurable(Ω, S, λx:A. extended_of_real(«absPow»(p, f, x)))",
			By(
				sigma,
				powerFacts[0],
				measure_integral.RealIntegrableDef.At(Ω, S, μ, power),
				measurable_function.ExtendedMeasurableOfReal.At(Ω, S, power)))
		value := a.Have(
			"and its nonnegative integral I is ‖f‖ₚᵖ",
			"«absPowIntegral»(Ω, S, μ, p, f) = extended_of_real(real_rpow(lp_seminorm(Ω, S, μ, p, f), p))",
			By(
				powerFacts[0],
				powerFacts[1],
				real_rpow.RpowNonneg,
				measure_integral.IntegralNonnegEmbedding.At(Ω, S, μ, power)))
		vanishing := a.Have(
			"|f(x)|^p embeds as 0 exactly where f(x) = 0",
			"(λx:A. extended_of_real(«absPow»(p, f, x)) = &0) = (λx:A. f(x) = &0)",
			Funext(),
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				absF := b.TermAs[Real]("|f(x)|")
				b.Iff()
				b.Forward(
					"a nonnegative power that embeds as 0 is 0, and |f(x)|^p is 0 only where |f(x)| is",
					func(c *Argument, embedsZero Fact) {
						c.Show(
							"so |f(x)| = 0, and so f(x) = 0",
							ByArith(
								embedsZero,
								positive,
								real_rpow.RpowNonneg.At(absF, p),
								extended_nonneg_real.OfRealInjective.At(c.TermAs[Real]("«absPow»(p, f, x)"), zero),
								real_rpow.RpowEqZero.At(absF, p)))
					})
				b.Backward(
					"0 to the power p is 0",
					func(c *Argument, vanishes Fact) {
						c.Show(
							"so |f(x)|^p = 0",
							ByArith(vanishes, positive, real_rpow.RpowZeroBase.At(p)))
					})
			}))
		nonneg := LpSeminormNonneg.At(Ω, S, μ, p, f)
		scalar := a.Have(
			"‖f‖ₚ is 0 exactly when ‖f‖ₚᵖ embeds as 0",
			"lp_seminorm(Ω, S, μ, p, f) = &0 ⇔ extended_of_real(real_rpow(lp_seminorm(Ω, S, μ, p, f), p)) = &0",
			Derive(func(b *Argument) {
				b.Iff()
				b.Forward(
					"0 to the power p is 0",
					func(c *Argument, normZero Fact) {
						c.Show(
							"so ‖f‖ₚᵖ embeds as 0",
							ByArith(normZero, positive, real_rpow.RpowZeroBase.At(p)))
					})
				b.Backward(
					"a nonnegative power that embeds as 0 is 0, and ‖f‖ₚᵖ is 0 only where ‖f‖ₚ is",
					func(c *Argument, embedsZero Fact) {
						c.Show(
							"so ‖f‖ₚ = 0",
							ByArith(
								embedsZero,
								nonneg,
								positive,
								real_rpow.RpowNonneg.At(norm, p),
								extended_nonneg_real.OfRealInjective.At(
									c.TermAs[Real]("real_rpow(lp_seminorm(Ω, S, μ, p, f), p)"), zero),
								real_rpow.RpowEqZero.At(norm, p)))
					})
			}))
		a.Show(
			"I is 0 exactly when its integrand vanishes almost everywhere",
			By(
				scalar,
				value,
				vanishing,
				measurableEmbedded,
				measure,
				nonneg_integral.IntegralZeroIffAE.At(Ω, S, μ, embedded)))
	}),
})}

// LpHolder — Hölder's inequality: for conjugate exponents p, q > 1, the
// product of f in Lᵖ and g in L^q is integrable, and the integral of |fg|
// is at most ‖f‖ₚ·‖g‖_q. Young's inequality at |f(x)| and |g(x)| bounds
// |fg| by the integrable |f|^p/p + |g|^q/q. If a seminorm is zero its
// function vanishes almost everywhere, and so does |fg|, whose integral is
// then 0. Otherwise both are positive, and Young's inequality at
// |f(x)|/‖f‖ₚ and |g(x)|/‖g‖_q bounds |fg|/(‖f‖ₚ‖g‖_q) by the normalized
// Young bound h = |f|^p/(p‖f‖ₚᵖ) + |g|^q/(q‖g‖_q^q), the power of a
// quotient being the quotient of the powers. Integrated, h has integral
// ‖f‖ₚᵖ/(p‖f‖ₚᵖ) + ‖g‖_q^q/(q‖g‖_q^q) = 1/p + 1/q = 1.
var LpHolder = lpHolderThm{family.Add(registry.ProofEntry{
	Name: "LpHolder",
	Reading: "The exponents are strictly above one and there is no " +
		"infinite exponent, so the pairing of L1 with L-infinity is not covered.",
	Key: "prop_12571aab6c3d24c0",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p q:real. " +
			"∀f g:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"&1 < p",
			"&1 < q",
			"real_inv(p) + real_inv(q) = &1",
			"f ∈ lp_functions(Ω, S, μ, p)",
			"g ∈ lp_functions(Ω, S, μ, q)",
		},
		Conclusion: "complex_integrable(Ω, S, μ, λx:A. f(x) * g(x)) ∧ " +
			"measure_integral(Ω, S, μ, λx:A. |f(x) * g(x)|) ≤ " +
			"lp_seminorm(Ω, S, μ, p, f) * lp_seminorm(Ω, S, μ, q, g)",
		Abbrev: Abbrev{
			{Name: "‖f‖_p", Text: "lp_seminorm(Ω, S, μ, p, f)"},
			{Name: "‖g‖_q", Text: "lp_seminorm(Ω, S, μ, q, g)"},
			{Name: "|fg|", Text: "λx:A. |f(x) * g(x)|"},
			{Name: "h", Text: "λx:A. " +
				"    real_inv(p * real_rpow(«‖f‖_p», p)) * «absPow»(p, f, x) + " +
				"    real_inv(q * real_rpow(«‖g‖_q», q)) * «absPow»(q, g, x)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		p, q *Expr[Real],
		f, g *Arrow[A, Complex],
		measure, pAbove, qAbove, conjugate, fIn, gIn Fact,
	) {
		fPowerTerm := a.TermAs[Fun[A, Real]]("«absPow»(p, f)")
		gPowerTerm := a.TermAs[Fun[A, Real]]("«absPow»(q, g)")
		absProduct := a.TermAs[Fun[A, Real]]("«|fg|»")
		product := a.TermAs[Fun[A, Complex]]("λx:A. f(x) * g(x)")
		inverseP := a.TermAs[Real]("real_inv(p)")
		inverseQ := a.TermAs[Real]("real_inv(q)")
		sigma := a.Have(
			"μ's measurable sets form a σ-algebra",
			"sigma_algebra_on(Ω, S)",
			By(measure, measure_space.MeasureOn))
		positive := a.Have(
			"the exponents are positive",
			"&0 < p ∧ &0 < q",
			ByArith(pAbove, qAbove))
		fPower := a.Conjuncts(
			GroupPremises(sigma, positive, fIn, LpPowerIntegral.At(Ω, S, μ, p, f)),
			"|f|^p is integrable",
			"with integral ‖f‖ₚᵖ")
		gPower := a.Conjuncts(
			GroupPremises(sigma, positive, gIn, LpPowerIntegral.At(Ω, S, μ, q, g)),
			"|g|^q is integrable",
			"with integral ‖g‖_q^q")
		measurable := a.Have(
			"f and g are measurable",
			"complex_measurable(Ω, S, f) ∧ complex_measurable(Ω, S, g)",
			BySets(
				fIn,
				gIn,
				LpFunctionsDef.At(Ω, S, μ, p),
				LpFunctionsDef.At(Ω, S, μ, q),
				almost_everywhere_function.MeasurableFunctionsDef.At(Ω, S)))
		productMeasurable := a.Have(
			"so are fg and |fg|",
			"complex_measurable(Ω, S, λx:A. f(x) * g(x)) ∧ real_measurable(Ω, S, «|fg|»)",
			By(
				sigma,
				measurable,
				complex_measure_integral.ComplexMeasurableMul.At(Ω, S, f, g),
				complex_measure_integral.ComplexMeasurableAbs.At(Ω, S, product)))
		young := a.Have(
			"Young's inequality at |f(x)| and |g(x)| bounds |fg| by |f|^p/p + |g|^q/q",
			"∀x:A. x ∈ Ω ⇒ ||f(x) * g(x)|| ≤ real_inv(p) * «absPow»(p, f, x) + real_inv(q) * «absPow»(q, g, x)",
			Derive(func(b *Argument) {
				b.FixAs[A]("x")
				b.Assume()
				b.Show(
					"|f(x)g(x)| = |f(x)|·|g(x)|, its own absolute value",
					ByArith(
						conjugate,
						pAbove,
						qAbove,
						real_convex.Young.At(b.TermAs[Real]("|f(x)|"), b.TermAs[Real]("|g(x)|"), p, q)))
			}))
		scaledFPower := a.TermAs[Fun[A, Real]]("λx:A. real_inv(p) * «absPow»(p, f, x)")
		scaledGPower := a.TermAs[Fun[A, Real]]("λx:A. real_inv(q) * «absPow»(q, g, x)")
		integrable := a.Have(
			"so |fg| is integrable, dominated by the integrable |f|^p/p + |g|^q/q",
			"real_integrable(Ω, S, μ, «|fg|»)",
			By(
				young,
				productMeasurable,
				measure,
				fPower[0],
				gPower[0],
				measure_integral.IntegrableScale.At(Ω, S, μ, fPowerTerm, inverseP),
				measure_integral.IntegrableScale.At(Ω, S, μ, gPowerTerm, inverseQ),
				measure_integral.IntegrableAdd.At(Ω, S, μ, scaledFPower, scaledGPower),
				measure_integral.IntegrableDominated.At(
					Ω,
					S,
					μ,
					absProduct,
					a.TermAs[Fun[A, Real]]("λx:A. real_inv(p) * «absPow»(p, f, x) + real_inv(q) * «absPow»(q, g, x)"))))
		bound := a.Have(
			"Hölder's inequality",
			"measure_integral(Ω, S, μ, «|fg|») ≤ «‖f‖_p» * «‖g‖_q»",
			Derive(func(b *Argument) {
				fNorm := b.TermAs[Real]("«‖f‖_p»")
				gNorm := b.TermAs[Real]("«‖g‖_q»")
				nonneg := b.Have(
					"the seminorms are nonnegative",
					"&0 ≤ «‖f‖_p» ∧ &0 ≤ «‖g‖_q»",
					By(LpSeminormNonneg.At(Ω, S, μ, p, f), LpSeminormNonneg.At(Ω, S, μ, q, g)))
				b.Cases(b.Term("«‖f‖_p» = &0 ∨ «‖g‖_q» = &0"))
				b.When(
					"a zero seminorm makes its function, and with it |fg|, vanish almost everywhere",
					func(c *Argument, zero Fact) {
						productZero := c.TermAs[Fun[A, Bool]]("λx:A. |f(x) * g(x)| = &0")
						zeroFunction := c.TermAs[Fun[A, Real]]("λx:A. &0")
						vanishes := c.Have(
							"f or g vanishes almost everywhere",
							"measure_ae(Ω, S, μ, λx:A. f(x) = &0) ∨ measure_ae(Ω, S, μ, λx:A. g(x) = &0)",
							By(
								zero,
								measure,
								positive,
								fIn,
								gIn,
								LpSeminormZeroIffAE.At(Ω, S, μ, p, f),
								LpSeminormZeroIffAE.At(Ω, S, μ, q, g)))
						pointwise := c.Have(
							"|fg| is 0 wherever f or g is",
							"∀x:A. (f(x) = &0 ⇒ |f(x) * g(x)| = &0) ∧ (g(x) = &0 ⇒ |f(x) * g(x)| = &0)",
							ByArith())
						productVanishes := c.Have(
							"so |fg| vanishes almost everywhere",
							"measure_ae(Ω, S, μ, λx:A. |f(x) * g(x)| = &0)",
							By(
								vanishes,
								pointwise,
								measure_space.AEMono.At(Ω, S, μ, c.TermAs[Fun[A, Bool]]("λx:A. f(x) = &0"), productZero),
								measure_space.AEMono.At(Ω, S, μ, c.TermAs[Fun[A, Bool]]("λx:A. g(x) = &0"), productZero)))
						integralZero := c.Have(
							"so its integral is that of 0, which is 0",
							"measure_integral(Ω, S, μ, «|fg|») = &0",
							ByArith(
								productVanishes,
								measure,
								measure_integral.IntegralAE.At(Ω, S, μ, absProduct, zeroFunction),
								measure_space.AEEqualDef.At(Ω, S, μ, absProduct, zeroFunction),
								measure_integral.IntegralZero.At(Ω, S, μ)))
						c.Show(
							"and ‖f‖ₚ·‖g‖_q is nonnegative",
							ByArith(integralZero, nonneg))
					})
				b.Otherwise(
					"both seminorms are positive: integrate Young's inequality at |f|/‖f‖ₚ and |g|/‖g‖_q",
					func(c *Argument, nonzero Fact) {
						positiveNorms := c.Have(
							"‖f‖ₚ and ‖g‖_q are positive",
							"&0 < «‖f‖_p» ∧ &0 < «‖g‖_q»",
							ByArith(nonzero, nonneg))
						termwise := c.Have(
							"Young's inequality at |f(x)|/‖f‖ₚ and |g(x)|/‖g‖_q",
							"∀x:A. real_inv(«‖f‖_p» * «‖g‖_q») * |f(x) * g(x)| ≤ «h»(x)",
							Derive(func(d *Argument) {
								d.FixAs[A]("x")
								fQuotient := d.TermAs[Real]("real_inv(«‖f‖_p») * |f(x)|")
								gQuotient := d.TermAs[Real]("real_inv(«‖g‖_q») * |g(x)|")
								fPowerQuotient := d.Have(
									"the pth power of |f(x)|/‖f‖ₚ is |f(x)|^p/‖f‖ₚᵖ",
									"real_rpow(real_inv(«‖f‖_p») * |f(x)|, p) = real_inv(real_rpow(«‖f‖_p», p)) * «absPow»(p, f, x)",
									ByArith(
										positiveNorms,
										real_rpow.RpowMulBase.At(d.TermAs[Real]("real_inv(«‖f‖_p»)"), d.TermAs[Real]("|f(x)|"), p),
										real_rpow.RpowInvBase.At(fNorm, p)))
								gPowerQuotient := d.Have(
									"and the qth power of |g(x)|/‖g‖_q is |g(x)|^q/‖g‖_q^q",
									"real_rpow(real_inv(«‖g‖_q») * |g(x)|, q) = real_inv(real_rpow(«‖g‖_q», q)) * «absPow»(q, g, x)",
									ByArith(
										positiveNorms,
										real_rpow.RpowMulBase.At(d.TermAs[Real]("real_inv(«‖g‖_q»)"), d.TermAs[Real]("|g(x)|"), q),
										real_rpow.RpowInvBase.At(gNorm, q)))
								d.Show(
									"(|f(x)|/‖f‖ₚ)(|g(x)|/‖g‖_q) ≤ (|f(x)|/‖f‖ₚ)^p/p + (|g(x)|/‖g‖_q)^q/q",
									ByArith(
										conjugate,
										pAbove,
										qAbove,
										positiveNorms,
										Scaled(inverseP, fPowerQuotient),
										Scaled(inverseQ, gPowerQuotient),
										real_convex.Young.At(fQuotient, gQuotient, p, q)))
							}))
						fCoefficient := c.TermAs[Real]("real_inv(p * real_rpow(«‖f‖_p», p))")
						gCoefficient := c.TermAs[Real]("real_inv(q * real_rpow(«‖g‖_q», q))")
						scaledF := c.TermAs[Fun[A, Real]]("λx:A. real_inv(p * real_rpow(«‖f‖_p», p)) * «absPow»(p, f, x)")
						scaledG := c.TermAs[Fun[A, Real]]("λx:A. real_inv(q * real_rpow(«‖g‖_q», q)) * «absPow»(q, g, x)")
						normalizer := c.TermAs[Real]("real_inv(«‖f‖_p» * «‖g‖_q»)")
						linear := c.Have(
							"h is integrable, and its integral is the same combination of the integrals of |f|^p and |g|^q",
							"real_integrable(Ω, S, μ, «h») ∧ "+
								"measure_integral(Ω, S, μ, «h») = "+
								"real_inv(p * real_rpow(«‖f‖_p», p)) * measure_integral(Ω, S, μ, «absPow»(p, f)) + "+
								"real_inv(q * real_rpow(«‖g‖_q», q)) * measure_integral(Ω, S, μ, «absPow»(q, g))",
							By(
								measure,
								fPower[0],
								gPower[0],
								measure_integral.IntegrableScale.At(Ω, S, μ, fPowerTerm, fCoefficient),
								measure_integral.IntegrableScale.At(Ω, S, μ, gPowerTerm, gCoefficient),
								measure_integral.IntegrableAdd.At(Ω, S, μ, scaledF, scaledG),
								measure_integral.IntegralAdd.At(Ω, S, μ, scaledF, scaledG),
								measure_integral.IntegralScale.At(Ω, S, μ, fPowerTerm, fCoefficient),
								measure_integral.IntegralScale.At(Ω, S, μ, gPowerTerm, gCoefficient)))
						integrated := c.Have(
							"integrating the termwise bound bounds ∫|fg|/(‖f‖ₚ‖g‖_q)",
							"real_inv(«‖f‖_p» * «‖g‖_q») * measure_integral(Ω, S, μ, «|fg|») ≤ "+
								"real_inv(p * real_rpow(«‖f‖_p», p)) * measure_integral(Ω, S, μ, «absPow»(p, f)) + "+
								"real_inv(q * real_rpow(«‖g‖_q», q)) * measure_integral(Ω, S, μ, «absPow»(q, g))",
							By(
								linear,
								measure,
								integrable,
								termwise,
								measure_integral.IntegrableScale.At(Ω, S, μ, absProduct, normalizer),
								measure_integral.IntegralMono.At(
									Ω,
									S,
									μ,
									c.TermAs[Fun[A, Real]]("λx:A. real_inv(«‖f‖_p» * «‖g‖_q») * «|fg|»(x)"),
									c.TermAs[Fun[A, Real]]("«h»")),
								measure_integral.IntegralScale.At(Ω, S, μ, absProduct, normalizer)))
						normalized := c.Have(
							"with ∫|f|^p = ‖f‖ₚᵖ and ∫|g|^q = ‖g‖_q^q the right side is 1/p + 1/q = 1",
							"real_inv(«‖f‖_p» * «‖g‖_q») * measure_integral(Ω, S, μ, «|fg|») ≤ &1",
							ByArith(
								integrated,
								fPower[1],
								gPower[1],
								conjugate,
								pAbove,
								qAbove,
								positiveNorms,
								real_rpow.RpowPositive.At(fNorm, p),
								real_rpow.RpowPositive.At(gNorm, q)))
						integralTerm := c.TermAs[Real]("measure_integral(Ω, S, μ, «|fg|»)")
						normProduct := c.TermAs[Real]("«‖f‖_p» * «‖g‖_q»")
						c.Show(
							"clear the positive divisor ‖f‖ₚ·‖g‖_q",
							ByArith(
								normalized,
								positiveNorms,
								real_order_ring.MulPos.At(fNorm, gNorm),
								real_order_field.LessEqDivMulRight.At(integralTerm, c.TermAs[Real]("&1"), normProduct),
								real_field.RealDivDef.At(integralTerm, normProduct)))
					})
			}))
		a.Show(
			"fg is integrable, its modulus |fg| being integrable, and Hölder's inequality bounds ∫|fg|",
			By(
				productMeasurable,
				integrable,
				complex_measure_integral.ComplexIntegrableDef.At(Ω, S, μ, product),
				bound))
	}),
})}
