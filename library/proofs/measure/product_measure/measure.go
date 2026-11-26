package product_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/measurable_space"
	"github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductMeasureOn — integrating section masses defines a measure. The
// masses add over two disjoint events, and the integral inherits continuity
// along increasing sequences from ν by monotone convergence.
var ProductMeasureOn = productMeasureOnThm{family.Add(registry.ProofEntry{
	Name:    "ProductMeasureOn",
	Key:     "prop_8656666156d9641a",
	Reading: "μ need only be a measure; ν σ-finite makes the integrand measurable.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀V:set(B). " +
			"∀T:set(set(B)). " +
			"∀ν:(set(B) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "sigma_finite_on(V, T, ν)"},
		Conclusion: "measure_on(set_cross(Ω, V), product_sigma(Ω, S, V, T), product_measure(Ω, S, μ, ν))",
		Abbrev: Abbrev{
			{Name: "section", Text: "λE:set(prod(A, B)). λx:A. {y:B | (x, y) ∈ E}"},
			{Name: "sectionMass", Text: "λE:set(prod(A, B)). λx:A. ν(«section»(E, x))"},
			{Name: "mass", Text: "product_measure(Ω, S, μ, ν)"},
			{Name: "P", Text: "product_sigma(Ω, S, V, T)"},
			{Name: "masses", Text: "λn:num. «mass»(a(n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		disjointAdditivity := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀E F:set(prod(A, B)).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"sigma_finite_on(V, T, ν)",
				"E ∈ «P»",
				"F ∈ «P»",
				"E ∩ F = ∅",
			},
			Conclusion: "«mass»(E ∪ F) = «mass»(E) + «mass»(F)",
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal],
			E, F *Expr[Set[Prod[A, B]]], measure, sigmaFinite, eMeas, fMeas, apart Fact) {
			factors := b.Have(
				"the factors have sigma algebras and ν is a measure",
				"sigma_algebra_on(Ω, S) ∧ measure_on(V, T, ν) ∧ sigma_algebra_on(V, T)",
				By(
					measure,
					sigmaFinite,
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measure_space.SigmaFiniteDef.At(V, T, ν)))
			sectionAdd := b.Have(
				"the section mass of the disjoint union is the pointwise sum",
				"«sectionMass»(E ∪ F) = λx:A. «sectionMass»(E, x) + «sectionMass»(F, x)",
				Funext(),
				Derive(func(c *Argument) {
					x := c.FixAs[A]("x")
					measurable := c.Have(
						"both sections are measurable",
						"«section»(E, x) ∈ T ∧ «section»(F, x) ∈ T",
						By(
							eMeas,
							fMeas,
							factors,
							sigma_algebra.SigmaAlgebraOnDef.At(Ω, S),
							ProductSectionMeasurable.At(Ω, S, V, T, E, x),
							ProductSectionMeasurable.At(Ω, S, V, T, F, x)))
					union := c.Have(
						"the section of the union is the union of disjoint sections",
						"«section»(E ∪ F, x) = «section»(E, x) ∪ «section»(F, x) ∧ «section»(E, x) ∩ «section»(F, x) = ∅",
						BySets(apart))
					c.Show(
						"ν adds the masses of the disjoint sections",
						By(
							factors,
							measurable,
							union,
							measure_space.MeasureAdditive.At(V, T, ν,
								c.TermAs[Set[B]]("«section»(E, x)"),
								c.TermAs[Set[B]]("«section»(F, x)"))))
				}))
			measurable := b.Have(
				"both section mass functions are measurable",
				"extended_measurable(Ω, S, «sectionMass»(E)) ∧ extended_measurable(Ω, S, «sectionMass»(F))",
				By(
					eMeas,
					fMeas,
					factors,
					sigmaFinite,
					ProductSectionMassMeasurable.At(Ω, S, V, T, ν, E),
					ProductSectionMassMeasurable.At(Ω, S, V, T, ν, F)))
			b.Show(
				"the nonnegative integral adds the two section mass functions",
				Simp(Fwd(ProductMeasureDef)),
				By(
					measure,
					sectionAdd,
					measurable,
					nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ,
						b.TermAs[Fun[A, ExtendedNonnegReal]]("«sectionMass»(E)"),
						b.TermAs[Fun[A, ExtendedNonnegReal]]("«sectionMass»(F)"))))
		})

		continuousFromBelow := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀V:set(B). " +
				"∀T:set(set(B)). " +
				"∀ν:(set(B) → extended_nonneg_real). " +
				"∀a:(num → set(prod(A, B))).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"sigma_finite_on(V, T, ν)",
				"∀n:num. a(n) ∈ «P»",
				"∀n:num. a(n) ⊆ a(n + 1)",
			},
			Conclusion: "«mass»(⋃image(a, 𝕌)) = extended_sup(image(«masses», 𝕌))",
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]], μ *Arrow[Set[A], ExtendedNonnegReal],
			V *Expr[Set[B]], T *Expr[Set[Set[B]]], ν *Arrow[Set[B], ExtendedNonnegReal],
			a *Arrow[Nat, Set[Prod[A, B]]], measure, sigmaFinite, events, rising Fact) {
			factors := b.Have(
				"the factors have sigma algebras and ν is a measure",
				"sigma_algebra_on(Ω, S) ∧ measure_on(V, T, ν) ∧ sigma_algebra_on(V, T)",
				By(
					measure,
					sigmaFinite,
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measure_space.SigmaFiniteDef.At(V, T, ν)))
			sections := b.Have(
				"all the sections are measurable for ν",
				"∀n:num. ∀x:A. «section»(a(n), x) ∈ T",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					x := c.FixAs[A]("x")
					c.Show(
						"take a section of a measurable product event",
						By(
							events.At(n),
							factors,
							sigma_algebra.SigmaAlgebraOnDef.At(Ω, S),
							ProductSectionMeasurable.At(Ω, S, V, T, a.Apply(n), x)))
				}))
			nested := b.Have(
				"the sections increase with the events",
				"∀n:num. ∀x:A. «section»(a(n), x) ⊆ «section»(a(n + 1), x)",
				BySets(rising))
			measurable := b.Have(
				"each section mass function is measurable for μ",
				"∀n:num. extended_measurable(Ω, S, «sectionMass»(a(n)))",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					c.Show(
						"ν is σ-finite",
						By(events.At(n), factors, sigmaFinite, ProductSectionMassMeasurable.At(Ω, S, V, T, ν, a.Apply(n))))
				}))
			pointwiseIncreasing := b.Have(
				"the section masses are pointwise increasing on Ω",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ «sectionMass»(a(n), x) ≤ «sectionMass»(a(n + 1), x)",
				Derive(func(c *Argument) {
					n := c.FixAs[Nat]("n")
					x := c.FixAs[A]("x")
					c.Assume()
					c.Show(
						"ν is monotone on the increasing measurable sections",
						By(
							factors,
							sections.At(n, x),
							sections.At(c.TermAs[Nat]("n + 1"), x),
							nested.At(n, x),
							measure_space.MeasureMono.At(V, T, ν,
								c.TermAs[Set[B]]("«section»(a(n), x)"),
								c.TermAs[Set[B]]("«section»(a(n + 1), x)"))))
				}))
			limit := b.Have(
				"the section mass of the union is the pointwise supremum",
				"«sectionMass»(⋃image(a, 𝕌)) = λx:A. extended_sup(image(λn:num. «sectionMass»(a(n), x), 𝕌))",
				Funext(),
				Derive(func(c *Argument) {
					c.FixAs[A]("x")
					union := c.Have(
						"taking a section commutes with forming the union",
						"«section»(⋃image(a, 𝕌), x) = ⋃image(λn:num. «section»(a(n), x), 𝕌)",
						BySets())
					c.Show(
						"apply continuity from below to ν",
						By(
							factors,
							sections,
							nested,
							union,
							measure_space.MeasureContinuousIncreasing.At(V, T, ν,
								c.TermAs[Fun[Nat, Set[B]]]("λn:num. «section»(a(n), x)"))))
				}))
			b.Show(
				"monotone convergence passes the pointwise supremum through the integral",
				Simp(Fwd(ProductMeasureDef)),
				By(
					measure,
					measurable,
					pointwiseIncreasing,
					limit,
					nonneg_integral.MonotoneConvergence.At(Ω, S, μ,
						b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. «sectionMass»(a(n))"))))
		})

		return ctx.Theorem(headline, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], V *Expr[Set[B]], T *Expr[Set[Set[B]]],
			ν *Arrow[Set[B], ExtendedNonnegReal], measure, sigmaFinite Fact) {
			factors := b.Have(
				"the factor sigma algebras and the empty mass of ν",
				"sigma_algebra_on(Ω, S) ∧ sigma_algebra_on(V, T) ∧ ν(∅) = &0",
				By(
					measure,
					sigmaFinite,
					measure_space.MeasureOn.At(Ω, S, μ),
					measure_space.MeasureOn.At(V, T, ν),
					measure_space.SigmaFiniteDef.At(V, T, ν)))
			carrier := b.TermAs[Set[Prod[A, B]]]("set_cross(Ω, V)")
			productSigma := b.TermAs[Set[Set[Prod[A, B]]]]("«P»")
			mass := b.TermAs[Fun[Set[Prod[A, B]], ExtendedNonnegReal]]("«mass»")
			sigma := b.Have(
				"the measurable rectangles generate a sigma algebra on the product carrier",
				"sigma_algebra_on(set_cross(Ω, V), «P»)",
				By(factors, measurable_space.ProductSigmaProjections.At(Ω, S, V, T)))
			zero := b.Have(
				"the empty event has zero product mass",
				"«mass»(∅) = &0",
				Derive(func(c *Argument) {
					zeroSections := c.Have(
						"the empty event has zero section mass at each point",
						"«sectionMass»(∅) = λx:A. &0",
						Funext(),
						Derive(func(d *Argument) {
							d.FixAs[A]("x")
							empty := d.Have(
								"the section is empty",
								"«section»(∅, x) = ∅",
								BySets())
							d.Show(
								"ν vanishes on the empty set",
								By(factors, empty))
						}))
					c.Show(
						"integrate the zero function",
						Simp(Fwd(ProductMeasureDef)),
						By(zeroSections, nonneg_integral.NonnegIntegralZero.At(Ω, S, μ)))
				}))
			additive := b.Have(
				"the product masses add over two disjoint measurable events",
				"∀E F:set(prod(A, B)). E ∈ «P» ∧ F ∈ «P» ∧ E ∩ F = ∅ ⇒ «mass»(E ∪ F) = «mass»(E) + «mass»(F)",
				Derive(func(c *Argument) {
					E := c.FixAs[Set[Prod[A, B]]]("E")
					F := c.FixAs[Set[Prod[A, B]]]("F")
					given := c.Assume()
					c.Show(
						"the section masses of the two events add",
						By(measure, sigmaFinite, given, At(disjointAdditivity, Ω, S, μ, V, T, ν, E, F)))
				}))
			continuous := b.Have(
				"the product mass is continuous along increasing sequences",
				Statement{
					Binders:    "∀a:(num → set(prod(A, B))).",
					Hypotheses: []string{"∀n:num. a(n) ∈ «P»", "∀n:num. a(n) ⊆ a(n + 1)"},
					Conclusion: "«mass»(⋃image(a, 𝕌)) = extended_sup(image(λn:num. «mass»(a(n)), 𝕌))",
				},
				Derive(func(c *Argument) {
					a := c.FixAs[Fun[Nat, Set[Prod[A, B]]]]("a")
					given := c.Assume()
					c.Show(
						"monotone convergence passes the supremum of the section masses through the integral",
						By(measure, sigmaFinite, given, At(continuousFromBelow, Ω, S, μ, V, T, ν, a)))
				}))
			b.Show(
				"an additive set function continuous from below is a measure",
				By(
					sigma,
					zero,
					additive,
					continuous,
					measure_space.MeasureFromContinuousIncreasing.At(carrier, productSigma, mass)))
		})
	}),
})}

// ProductMeasureRectangle — a rectangle s × t has product mass μ(s)·ν(t):
// its section mass is the cut of the height ν(t) to s.
var ProductMeasureRectangle = productMeasureRectangleThm{family.Add(registry.ProofEntry{
	Name: "ProductMeasureRectangle",
	Key:  "prop_c887809848cbb193",
	Reading: "No σ-finiteness, and t need not be measurable. An infinite " +
		"factor against a null one gives 0, as the integral of ∞ on a null set does.",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀ν:(set(B) → extended_nonneg_real). " +
			"∀s:set(A). " +
			"∀t:set(B).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"ν(∅) = &0",
			"s ∈ S",
		},
		Conclusion: "product_measure(Ω, S, μ, ν, set_cross(s, t)) = μ(s) * ν(t)",
		Abbrev: Abbrev{
			{Name: "cut", Text: "λz:extended_nonneg_real. λx:A. COND(x ∈ s, z, &0)"},
		},
	}, func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		ν *Arrow[Set[B], ExtendedNonnegReal],
		s *Expr[Set[A]],
		t *Expr[Set[B]],
		measureμ, emptyν, sMeasurable Fact,
	) {
		// By definition the mass is ∫ ν(E_x) dμ.
		a.Do(Simp(Fwd(ProductMeasureDef)))
		sections := a.Have(
			"the section is t on s and empty elsewhere",
			"∀x:A. {y:B | (x, y) ∈ set_cross(s, t)} = COND(x ∈ s, t, ∅)",
			BySets(set_product.InCross.Inst(TypeBinder.BindA[A](), TypeBinder.BindB[B]())))
		sectionMass := a.Have(
			"the section mass is the cut of ν(t) to s",
			"(λx:A. ν({y:B | (x, y) ∈ set_cross(s, t)})) = «cut»(ν(t))",
			By(sections, emptyν))
		a.Show(
			"the cut of the height ν(t) to s integrates to ν(t) times μ(s)",
			By(
				sectionMass,
				measureμ,
				sMeasurable,
				nonneg_integral.NonnegIntegralIndicator.At(Ω, S, μ, s, ν.Apply(t)),
				extended_nonneg_real.MulComm.At(ν.Apply(t), μ.Apply(s))))
	}),
})}
