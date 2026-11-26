package density_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_simple"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/registry"
)

// DensityMeasureNonnegIntegral — integrating f against the measure with
// density ρ is integrating ρ·f against the original measure. On the level
// sets of a simple function the identity is scaling, and the two integrals
// take the same supremum along a simple approximation.
var DensityMeasureNonnegIntegral = densityMeasureNonnegIntegralThm{family.Add(registry.ProofEntry{
	Name: "DensityMeasureNonnegIntegral",
	Key:  "prop_4119dca581b19e96",
	Reading: "The product is that of ⟦0, ∞⟧, where 0 · ∞ = 0: where the " +
		"density is 0 the value of f, infinite or not, adds nothing to either side.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀ρ f:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"extended_measurable(Ω, S, ρ)",
			"extended_measurable(Ω, S, f)",
		},
		Conclusion: "nonneg_integral(Ω, S, density_measure(Ω, S, μ, ρ), f) = " +
			"nonneg_integral(Ω, S, μ, λx:A. ρ(x) * f(x))",
		Abbrev: Abbrev{
			{Name: "ν", Text: "density_measure(Ω, S, μ, ρ)"},
			{Name: "weightedReal", Text: "λv:(A → real). λx:A. ρ(x) * extended_of_real(v(x))"},
			{Name: "weightedSequence", Text: "λn:num. «weightedReal»(s(n))"},
			{Name: "weightedLimit", Text: "λx:A. extended_sup(image(λn:num. «weightedSequence»(n, x), 𝕌))"},
			{Name: "simpleIntegrals", Text: "λn:num. measure_simple_integral(Ω, «ν», s(n))"},
			{Name: "weightedIntegrals", Text: "λn:num. nonneg_integral(Ω, S, μ, «weightedSequence»(n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		scaleLimit := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀ρ f:(A → extended_nonneg_real). ∀s:(num → A → real).",
			Hypotheses: []string{
				"∀x:A. x ∈ Ω ⇒ f(x) = extended_sup(image(λn:num. extended_of_real(s(n, x)), 𝕌))",
			},
			Conclusion: "∀x:A. x ∈ Ω ⇒ ρ(x) * f(x) = «weightedLimit»(x)",
		}, func(
			b *Argument,
			Ω *Expr[Set[A]],
			ρ, f *Arrow[A, ExtendedNonnegReal],
			s *Arrow2[Nat, A, Real],
			limit Fact,
		) {
			x := b.FixAs[A]("x")
			in := b.Assume()
			b.Show(
				"multiplication by the density at x commutes with the supremum",
				By(
					limit.At(x),
					in,
					extended_nonneg_real.SupSequenceScaleExtended.At(ρ.Apply(x),
						b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(s(n, x))"))))
		})

		weightedMeasurable := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀ρ:(A → extended_nonneg_real). ∀g:(A → real).",
			Hypotheses: []string{
				"sigma_algebra_on(Ω, S)",
				"extended_measurable(Ω, S, ρ)",
				"real_measurable(Ω, S, g)",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ g(x)",
			},
			Conclusion: "extended_measurable(Ω, S, «weightedReal»(g))",
			Abbrev: Abbrev{
				{Name: "realProducts", Text: "λn:num. λx:A. extended_of_real(g(x) * t(n, x))"},
				{Name: "realProductLimit", Text: "λx:A. extended_sup(image(λn:num. «realProducts»(n, x), 𝕌))"},
			},
		}, func(
			b *Argument,
			Ω *Expr[Set[A]],
			S *Expr[Set[Set[A]]],
			ρ *Arrow[A, ExtendedNonnegReal],
			g *Arrow[A, Real],
			sigma, densityMeasurable, measurable, nonnegative Fact,
		) {
			_, approximation := b.UnpackAs[Fun2[Nat, A, Real]](
				GroupPremises(sigma, densityMeasurable, measure_simple.SimpleApproximation.At(Ω, S, ρ)), "t")
			parts := b.Conjuncts(
				approximation,
				"each approximant is simple",
				"the approximants increase",
				"the approximants lie below the density",
				"their supremum on Ω is the density")
			products := b.Have(
				"each real product with a density approximant embeds measurably",
				"∀n:num. extended_measurable(Ω, S, «realProducts»(n))",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					tn := c.TermAs[Fun[A, Real]]("t(n)")
					realProduct := c.TermAs[Fun[A, Real]]("λx:A. g(x) * t(n, x)")
					realMeasurable := c.Have(
						"the two real factors are measurable",
						"real_measurable(Ω, S, λx:A. g(x) * t(n, x))",
						By(
							sigma,
							measurable,
							parts[0].At(n),
							measure_simple.NonnegSimpleDef.At(Ω, S, tn),
							measurable_function.RealMeasurableMul.At(Ω, S, g, tn)))
					c.Show(
						"embed the measurable product",
						By(sigma, realMeasurable, measurable_function.ExtendedMeasurableOfReal.At(Ω, S, realProduct)))
				}))
			supMeasurable := b.Have(
				"the pointwise supremum of these products is measurable",
				"extended_measurable(Ω, S, «realProductLimit»)",
				By(
					sigma,
					products,
					measurable_function.ExtendedMeasurableSup.At(Ω, S,
						b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«realProducts»"))))
			same := b.Have(
				"on Ω the supremum is the desired product",
				"∀x:A. x ∈ Ω ⇒ «realProductLimit»(x) = «weightedReal»(g, x)",
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					in := c.Assume()
					sameSequence := c.Have(
						"embedding preserves each nonnegative real product",
						"(λn:num. «realProducts»(n, x)) = λn:num. extended_of_real(g(x)) * extended_of_real(t(n, x))",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[Nat]("n")
							d.Show(
								"apply multiplicativity of the embedding at the nonnegative weight",
								By(nonnegative.At(x), in, extended_nonneg_real.OfRealMul.At(g.Apply(x), d.TermAs[Real]("t(n, x)"))))
						}))
					gx := c.TermAs[ExtendedNonnegReal]("extended_of_real(g(x))")
					c.Show(
						"take the fixed factor through the supremum",
						sameSequence.Rw(),
						By(
							parts[3].At(x),
							in,
							extended_nonneg_real.SupSequenceScaleExtended.At(gx,
								c.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. extended_of_real(t(n, x))")),
							extended_nonneg_real.MulComm.At(gx, ρ.Apply(x))))
				}))
			limitFn := b.TermAs[Fun[A, ExtendedNonnegReal]]("«realProductLimit»")
			product := b.TermAs[Fun[A, ExtendedNonnegReal]]("«weightedReal»(g)")
			b.Show(
				"measurability transfers across agreement on Ω",
				By(
					supMeasurable,
					same,
					measurable_function.ExtendedMeasurableDef.At(Ω, S, limitFn),
					measurable_space.MeasurableCongruence.At(Ω, S,
						b.TermAs[Set[ExtendedNonnegReal]]("𝕌"),
						b.TermAs[Set[Set[ExtendedNonnegReal]]]("extended_borel"), limitFn, product),
					measurable_function.ExtendedMeasurableDef.At(Ω, S, product)))
		})

		levelScaling := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀ρ:(A → extended_nonneg_real). " +
				"∀r:(A → real). " +
				"∀y:real.",
			Hypotheses: []string{"measure_on(Ω, S, μ)", "&0 ≤ y"},
			Conclusion: "«weightedMass»(y) = «scaledMass»(y)",
			Abbrev: Abbrev{
				{Name: "level", Text: "λy:real. {x:A | x ∈ Ω ∧ r(x) = y}"},
				{Name: "weightedMeasure", Text: "density_measure(Ω, S, μ, «weightedReal»(r))"},
				{Name: "scaledMass", Text: "λy:real. extended_of_real(y) * «ν»(«level»(y))"},
				{Name: "weightedMass", Text: "λy:real. «weightedMeasure»(«level»(y))"},
			},
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ *Arrow[A, ExtendedNonnegReal],
			r *Arrow[A, Real], y *Expr[Real], measure, nonnegative Fact) {
			b.Do(Simp(Fwd(DensityMeasureDef)))
			same := b.Have(
				"on the level set the new density scales the old one by y",
				Statement{
					Binders:    "∀x:A.",
					Hypotheses: []string{"x ∈ Ω"},
					Conclusion: "COND(x ∈ «level»(y), «weightedReal»(r, x), &0) = " +
						"extended_of_real(y) * COND(x ∈ «level»(y), ρ(x), &0)",
				},
				BySets(extended_nonneg_real.MulComm, extended_nonneg_real.MulZero))
			cut := b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. COND(x ∈ «level»(y), ρ(x), &0)")
			newCut := b.TermAs[Fun[A, ExtendedNonnegReal]](
				"λx:A. COND(x ∈ «level»(y), «weightedReal»(r, x), &0)")
			scaledCut := b.TermAs[Fun[A, ExtendedNonnegReal]](
				"λx:A. extended_of_real(y) * COND(x ∈ «level»(y), ρ(x), &0)")
			b.Show(
				"the integral of the new cut scales by the same coefficient",
				By(
					same,
					nonnegative,
					measure,
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, newCut, scaledCut),
					nonneg_integral.NonnegIntegralScale.At(Ω, S, μ, cut, y)))
		})

		simpleCase := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀ρ:(A → extended_nonneg_real). " +
				"∀r:(A → real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"extended_measurable(Ω, S, ρ)",
				"measure_simple(Ω, S, r)",
			},
			Conclusion: "measure_simple_integral(Ω, «ν», r) = nonneg_integral(Ω, S, μ, «weightedReal»(r))",
			Abbrev: Abbrev{
				{Name: "level", Text: "λy:real. {x:A | x ∈ Ω ∧ r(x) = y}"},
				{Name: "weightedMeasure", Text: "density_measure(Ω, S, μ, «weightedReal»(r))"},
				{Name: "scaledMass", Text: "λy:real. extended_of_real(y) * «ν»(«level»(y))"},
				{Name: "weightedMass", Text: "λy:real. «weightedMeasure»(«level»(y))"},
			},
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ *Arrow[A, ExtendedNonnegReal],
			r *Arrow[A, Real], measure, densityMeasurable, simple Fact) {
			parts := b.Conjuncts(
				b.Unfolded(simple, measure_simple.NonnegSimpleDef),
				"r is measurable",
				"r takes finitely many values on Ω",
				"r is nonnegative on Ω")
			b.Do(Simp(Fwd(measure_simple.SimpleIntegralDef)))
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			weighted := b.TermAs[Fun[A, ExtendedNonnegReal]]("«weightedReal»(r)")
			productMeasurable := b.Have(
				"the density times the simple function is measurable",
				"extended_measurable(Ω, S, «weightedReal»(r))",
				By(sigma, densityMeasurable, parts[0], parts[2], At(weightedMeasurable, Ω, S, ρ, r)))
			termwise := b.Have(
				"each term of the simple integral is the new mass of that level set",
				"∀y:real. y ∈ image(r, Ω) ⇒ «scaledMass»(y) = «weightedMass»(y)",
				Derive(func(c *Argument) {
					y := c.FixAs[Real]("y")
					value := c.Assume()
					nonnegative := c.Have(
						"the level is a value of r on Ω so it is nonnegative",
						"&0 ≤ y",
						BySets(value, parts[2]))
					c.Show(
						"scale the density on this level",
						By(measure, nonnegative, At(levelScaling, Ω, S, μ, ρ, r, y)))
				}))
			values := b.TermAs[Set[Real]]("image(r, Ω)")
			byLevels := b.Have(
				"the simple integral sums the new masses of the level sets",
				"Σ_{y∈image(r, Ω)} «scaledMass»(y) = Σ_{y∈image(r, Ω)} «weightedMass»(y)",
				By(
					termwise,
					monoidal.Congruence.Read(extended_nonneg_real.MonoidalAdd).At(values,
						b.TermAs[Fun[Real, ExtendedNonnegReal]]("«scaledMass»"),
						b.TermAs[Fun[Real, ExtendedNonnegReal]]("«weightedMass»")),
					extended_nonneg_real.ExtendedSumDef))
			events := b.Have(
				"each level set is measurable",
				"∀y:real. y ∈ image(r, Ω) ⇒ «level»(y) ∈ S",
				By(sigma, simple, At(measure_simple.SimpleLevelSets, Ω, S, r)))
			disjoint := b.Have(
				"different levels are disjoint",
				"∀y z:real. y ∈ image(r, Ω) ∧ z ∈ image(r, Ω) ∧ y ≠ z ⇒ disjoint(«level»(y), «level»(z))",
				BySets())
			cover := b.Have(
				"the level sets cover Ω",
				"⋃image(«level», image(r, Ω)) = Ω",
				BySets())
			total := b.Have(
				"finite additivity sums the new masses to the mass of Ω",
				"«weightedMeasure»(Ω) = Σ_{y∈image(r, Ω)} «weightedMass»(y)",
				By(
					measure,
					productMeasurable,
					parts[1],
					events,
					disjoint,
					cover,
					DensityMeasure.At(Ω, S, μ, weighted),
					measure_space.MeasureFiniteAdditive.At(Ω, S,
						b.TermAs[Fun[Set[A], ExtendedNonnegReal]]("«weightedMeasure»"),
						b.TermAs[Fun2[Real, A, Bool]]("«level»"), values)))
			uncut := b.Have(
				"on Ω the cut to Ω agrees with the product",
				"∀x:A. x ∈ Ω ⇒ COND(x ∈ Ω, «weightedReal»(r, x), &0) = «weightedReal»(r, x)",
				BySets())
			b.Show(
				"the new mass of Ω is the integral of the product",
				By(
					byLevels,
					total,
					uncut,
					DensityMeasureDef.At(Ω, S, μ, weighted, Ω),
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ,
						b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. COND(x ∈ Ω, «weightedReal»(r, x), &0)"), weighted)))
		})

		return ctx.Theorem(headline, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ, f *Arrow[A, ExtendedNonnegReal],
			measure, densityMeasurable, measurable Fact) {
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			ν := b.TermAs[Fun[Set[A], ExtendedNonnegReal]]("«ν»")
			densityMeasure := b.Have(
				"the density defines a measure on S",
				"measure_on(Ω, S, «ν»)",
				By(measure, densityMeasurable, DensityMeasure.At(Ω, S, μ, ρ)))
			s, approximation := b.UnpackAs[Fun2[Nat, A, Real]](
				GroupPremises(sigma, measurable, measure_simple.SimpleApproximation.At(Ω, S, f)), "s")
			parts := b.Conjuncts(
				approximation,
				"each approximant is simple",
				"the approximants increase",
				"the approximants lie below f",
				"their supremum on Ω is f")
			left := b.Have(
				"the density integral is the supremum of the simple integrals",
				"nonneg_integral(Ω, S, «ν», f) = extended_sup(image(«simpleIntegrals», 𝕌))",
				By(
					densityMeasure,
					parts[0],
					parts[1],
					parts[3],
					nonneg_integral.MonotoneConvergenceSimple.At(Ω, S, ν, s, f)))
			products := b.Have(
				"each weighted approximant is measurable",
				"∀n:num. extended_measurable(Ω, S, «weightedSequence»(n))",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					sn := c.TermAs[Fun[A, Real]]("s(n)")
					c.Show(
						"use measurability of a weighted nonnegative real function",
						By(
							sigma,
							densityMeasurable,
							parts[0].At(n),
							measure_simple.NonnegSimpleDef.At(Ω, S, sn),
							At(weightedMeasurable, Ω, S, ρ, sn)))
				}))
			rising := b.Have(
				"multiplying by the density preserves the increase",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ «weightedSequence»(n, x) ≤ «weightedSequence»(n + 1, x)",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					x := c.FixAs[A]("x")
					in := c.Assume()
					c.Show(
						"embed the real inequality and multiply",
						By(
							parts[1].At(n, x),
							in,
							extended_nonneg_real.OfRealMono.At(c.TermAs[Real]("s(n, x)"), c.TermAs[Real]("s(n + 1, x)")),
							extended_nonneg_real.MulLeMono.At(
								c.TermAs[ExtendedNonnegReal]("extended_of_real(s(n, x))"),
								c.TermAs[ExtendedNonnegReal]("extended_of_real(s(n + 1, x))"), ρ.Apply(x))))
				}))
			right := b.Have(
				"the integral of ρ·f is the supremum of the weighted integrals",
				"nonneg_integral(Ω, S, μ, λx:A. ρ(x) * f(x)) = extended_sup(image(«weightedIntegrals», 𝕌))",
				By(
					parts[3],
					At(scaleLimit, Ω, ρ, f, s),
					measure,
					products,
					rising,
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ,
						b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. ρ(x) * f(x)"),
						b.TermAs[Fun[A, ExtendedNonnegReal]]("«weightedLimit»")),
					nonneg_integral.MonotoneConvergence.At(Ω, S, μ,
						b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«weightedSequence»"))))
			same := b.Have(
				"the simple and weighted integrals agree term by term",
				"«simpleIntegrals» = «weightedIntegrals»",
				Funext(),
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					c.Show(
						"apply the simple-function formula to this approximant",
						By(
							measure,
							densityMeasurable,
							parts[0].At(n),
							At(simpleCase, Ω, S, μ, ρ, c.TermAs[Fun[A, Real]]("s(n)"))))
				}))
			b.Show(
				"the two suprema coincide",
				By(left, right, same))
		})
	}),
})}

// DensityMeasureIntegral — a nonnegative real density transfers
// integrability and the real integral by multiplication. Apply the
// nonnegative formula to the absolute value and to both parts separately.
var DensityMeasureIntegral = densityMeasureIntegralThm{family.Add(registry.ProofEntry{
	Name: "DensityMeasureIntegral",
	Key:  "prop_b7c1d683761fdcc2",
	Reading: "g ≥ 0 on Ω is load-bearing: extended_of_real reads a negative " +
		"value of the density as 0. The equality of the integrals holds without " +
		"integrability, the positive and the negative part agreeing separately.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀g f:(A → real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"real_measurable(Ω, S, g)",
			"∀x:A. x ∈ Ω ⇒ &0 ≤ g(x)",
			"real_measurable(Ω, S, f)",
		},
		Conclusion: "(real_integrable(Ω, S, density_measure(Ω, S, μ, λx:A. extended_of_real(g(x))), f) ⇔ " +
			"    real_integrable(Ω, S, μ, λx:A. g(x) * f(x))) ∧ " +
			"measure_integral(Ω, S, density_measure(Ω, S, μ, λx:A. extended_of_real(g(x))), f) = " +
			"measure_integral(Ω, S, μ, λx:A. g(x) * f(x))",
		Abbrev: Abbrev{
			{Name: "embedded", Text: "λu:(A → real). λx:A. extended_of_real(u(x))"},
			{Name: "weight", Text: "λu:(A → real). λx:A. g(x) * u(x)"},
			{Name: "ν", Text: "density_measure(Ω, S, μ, «embedded»(g))"},
			{Name: "densityPart", Text: "λu:(A → real). nonneg_integral(Ω, S, «ν», «embedded»(u))"},
			{Name: "originalPart", Text: "λu:(A → real). nonneg_integral(Ω, S, μ, «embedded»(u))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		transferPart := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀g h:(A → real).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"real_measurable(Ω, S, g)",
				"∀x:A. x ∈ Ω ⇒ &0 ≤ g(x)",
				"real_measurable(Ω, S, h)",
			},
			Conclusion: "«densityPart»(h) = «originalPart»(«weight»(h))",
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], g, h *Arrow[A, Real],
			measure, densityMeasurable, nonnegative, measurable Fact) {
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			pointwise := b.Have(
				"on Ω the product of the embeddings is the embedded product",
				"∀x:A. x ∈ Ω ⇒ «embedded»(g, x) * «embedded»(h, x) = «embedded»(«weight»(h), x)",
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					in := c.Assume()
					c.Show(
						"the density is nonnegative at this point",
						By(nonnegative.At(x), in, extended_nonneg_real.OfRealMul.At(g.Apply(x), h.Apply(x))))
				}))
			density := b.TermAs[Fun[A, ExtendedNonnegReal]]("«embedded»(g)")
			part := b.TermAs[Fun[A, ExtendedNonnegReal]]("«embedded»(h)")
			product := b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. «embedded»(g, x) * «embedded»(h, x)")
			weighted := b.TermAs[Fun[A, ExtendedNonnegReal]]("«embedded»(«weight»(h))")
			b.Show(
				"transfer the embedded function and identify the weighted integrand",
				By(
					measure,
					sigma,
					densityMeasurable,
					measurable,
					pointwise,
					measurable_function.ExtendedMeasurableOfReal.At(Ω, S, g),
					measurable_function.ExtendedMeasurableOfReal.At(Ω, S, h),
					DensityMeasureNonnegIntegral.At(Ω, S, μ, density, part),
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, product, weighted)))
		})

		return ctx.Theorem(headline, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], g, f *Arrow[A, Real],
			measure, densityMeasurable, nonnegative, measurable Fact) {
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			productMeasurable := b.Have(
				"the real product is measurable",
				"real_measurable(Ω, S, «weight»(f))",
				By(sigma, densityMeasurable, measurable, measurable_function.RealMeasurableMul.At(Ω, S, g, f)))
			positive := b.Have(
				"the integrals of the positive parts agree",
				"«densityPart»(f) = «originalPart»(«weight»(f))",
				By(measure, densityMeasurable, nonnegative, measurable, At(transferPart, Ω, S, μ, g, f)))
			negative := b.Have(
				"the integrals of the negative parts agree: the "+
					"negative part of g·f is g times the negative part of f",
				"«densityPart»(λx:A. -f(x)) = «originalPart»(λx:A. -(«weight»(f, x)))",
				Simp(Rev(real_ring.MulRightNeg)),
				By(
					measure,
					sigma,
					densityMeasurable,
					nonnegative,
					measurable,
					measurable_function.RealMeasurableNeg.At(Ω, S, f),
					At(transferPart, Ω, S, μ, g, b.TermAs[Fun[A, Real]]("λx:A. -f(x)"))))
			absoluteProduct := b.Have(
				"on Ω the absolute value of the product is g times the absolute value",
				"∀x:A. x ∈ Ω ⇒ extended_of_real(g(x) * |f(x)|) = extended_of_real(|g(x) * f(x)|)",
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					in := c.Assume()
					c.Show(
						"g equals its absolute value on Ω",
						By(
							Normalized,
							nonnegative.At(x),
							in,
							real_sgn_abs.AbsFixedIffNonneg.At(g.Apply(x)),
							real_sgn_abs.AbsMul.At(g.Apply(x), f.Apply(x))))
				}))
			absolute := b.Have(
				"the integrals of the absolute values agree",
				"«densityPart»(λx:A. |f(x)|) = «originalPart»(λx:A. |«weight»(f, x)|)",
				By(
					measure,
					sigma,
					densityMeasurable,
					nonnegative,
					measurable,
					absoluteProduct,
					measurable_function.RealMeasurableAbs.At(Ω, S, f),
					At(transferPart, Ω, S, μ, g, b.TermAs[Fun[A, Real]]("λx:A. |f(x)|")),
					nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ,
						b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(g(x) * |f(x)|)"),
						b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(|g(x) * f(x)|)"))))
			b.Show(
				"the real integrability and integral formulas follow",
				SplitConj(
					Case(
						"integrability tests the common absolute integral for finiteness",
						Simp(Fwd(measure_integral.RealIntegrableDef)),
						By(measurable, productMeasurable, absolute)),
					Case(
						"both signed integrals subtract the same two values",
						Simp(Fwd(measure_integral.RealIntegralDef)),
						By(positive, negative))))
		})
	}),
})}
