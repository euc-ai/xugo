package density_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

// DensityMeasure — integrating a measurable nonnegative density over
// measurable sets defines a measure. The cuts to two disjoint sets add, and
// monotone convergence makes the mass continuous along increasing sequences.
var DensityMeasure = densityMeasureThm{family.Add(registry.ProofEntry{
	Name: "DensityMeasure",
	Key:  "prop_33a5cf0356f9fcc2",
	Reading: "ρ may take the value ∞ and μ need not be σ-finite: the density measure may give a " +
		"set of S infinite mass. Only sets of S are spoken of, where the cut density is measurable.",
	Build: family.Sections(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀ρ:(A → extended_nonneg_real).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"extended_measurable(Ω, S, ρ)",
		},
		Conclusion: "measure_on(Ω, S, density_measure(Ω, S, μ, ρ))",
		Abbrev: Abbrev{
			{Name: "ν", Text: "density_measure(Ω, S, μ, ρ)"},
			{Name: "cut", Text: "λD:set(A). λx:A. COND(x ∈ D, ρ(x), &0)"},
			{Name: "cuts", Text: "λn:num. «cut»(a(n))"},
			{Name: "cutLimit", Text: "λx:A. extended_sup(image(λn:num. «cuts»(n, x), 𝕌))"},
			{Name: "masses", Text: "λn:num. «ν»(a(n))"},
		},
	}, func(ctx *Script, headline string) *GoalStackNode {
		disjointAdditivity := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀ρ:(A → extended_nonneg_real). " +
				"∀E F:set(A).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"extended_measurable(Ω, S, ρ)",
				"E ∈ S",
				"F ∈ S",
				"E ∩ F = ∅",
			},
			Conclusion: "«ν»(E ∪ F) = «ν»(E) + «ν»(F)",
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ *Arrow[A, ExtendedNonnegReal],
			E, F *Expr[Set[A]], measure, measurable, eventE, eventF, apart Fact) {
			b.Do(Simp(Fwd(DensityMeasureDef)))
			pointwise := b.Have(
				"the cut to a disjoint union is the sum of the two cuts",
				"∀x:A. x ∈ Ω ⇒ «cut»(E ∪ F, x) = «cut»(E, x) + «cut»(F, x)",
				BySets(apart, extended_nonneg_real.AddZero, extended_nonneg_real.AddComm))
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			measurableCutE := b.Have(
				"the cut to E is measurable",
				"extended_measurable(Ω, S, «cut»(E))",
				By(sigma, eventE, measurable, measurable_function.ExtendedMeasurableOnEvent.At(Ω, S, E, ρ)))
			measurableCutF := b.Have(
				"the cut to F is measurable",
				"extended_measurable(Ω, S, «cut»(F))",
				By(sigma, eventF, measurable, measurable_function.ExtendedMeasurableOnEvent.At(Ω, S, F, ρ)))
			cutToE := b.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(E)")
			cutToF := b.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(F)")
			union := b.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(E ∪ F)")
			sum := b.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. «cut»(E, x) + «cut»(F, x)")
			integral := b.Have(
				"the cut to the union and the sum have the same integral",
				"nonneg_integral(Ω, S, μ, «cut»(E ∪ F)) = "+
					"nonneg_integral(Ω, S, μ, λx:A. «cut»(E, x) + «cut»(F, x))",
				By(pointwise, nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, union, sum)))
			b.Show(
				"integrate the sum of the two cuts",
				By(
					integral,
					measure,
					measurableCutE,
					measurableCutF,
					nonneg_integral.NonnegIntegralAdd.At(Ω, S, μ, cutToE, cutToF)))
		})

		cutUnion := ctx.Lemma(
			"∀ρ:(A → extended_nonneg_real). ∀a:(num → set(A)). ∀x:A. «cut»(⋃image(a, 𝕌), x) = «cutLimit»(x)",
			func(b *Argument, ρ *Arrow[A, ExtendedNonnegReal], a *Arrow[Nat, Set[A]], x *Expr[A]) {
				values := b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. «cuts»(n, x)")
				whole := b.TermAs[ExtendedNonnegReal]("«cut»(⋃image(a, 𝕌), x)")
				pointwise := b.Have(
					"the cut to the union bounds each cut",
					"∀n:num. «cuts»(n, x) ≤ «cut»(⋃image(a, 𝕌), x)",
					BySets(extended_nonneg_real.LeRefl, extended_nonneg_real.ZeroLe))
				upper := b.Have(
					"so it bounds their supremum",
					"«cutLimit»(x) ≤ «cut»(⋃image(a, 𝕌), x)",
					By(pointwise, extended_nonneg_real.SupSequenceLeast.At(values, whole)))
				lower := b.Have(
					"the supremum also bounds the cut to the union",
					"«cut»(⋃image(a, 𝕌), x) ≤ «cutLimit»(x)",
					Derive(func(c *Argument) {
						inside := c.Assuming(
							c.TermAs[Bool]("x ∈ ⋃image(a, 𝕌)"),
							"outside the union the cut is zero",
							Derive(func(d *Argument) {
								outside := d.Hyp("x ∉ ⋃image(a, 𝕌)")
								d.Show(
									"zero is a lower bound",
									By(outside, extended_nonneg_real.ZeroLe))
							}))
						n, member := c.ObtainAs[Nat](
							"some set in the sequence contains the point",
							"∃n:num. x ∈ a(n)",
							BySets(inside))
						c.Show(
							"this term of the sequence reaches the value on the union",
							By(member, inside, extended_nonneg_real.SupSequenceUpper.At(values, n)))
					}))
				b.Show(
					"the two bounds identify the supremum",
					By(upper, lower, extended_nonneg_real.LeAntisym))
			})

		continuousFromBelow := ctx.Lemma(Statement{
			Binders: "∀Ω:set(A). " +
				"∀S:set(set(A)). " +
				"∀μ:(set(A) → extended_nonneg_real). " +
				"∀ρ:(A → extended_nonneg_real). " +
				"∀a:(num → set(A)).",
			Hypotheses: []string{
				"measure_on(Ω, S, μ)",
				"extended_measurable(Ω, S, ρ)",
				"∀n:num. a(n) ∈ S",
				"∀n:num. a(n) ⊆ a(n + 1)",
			},
			Conclusion: "«ν»(⋃image(a, 𝕌)) = extended_sup(image(«masses», 𝕌))",
		}, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ *Arrow[A, ExtendedNonnegReal],
			a *Arrow[Nat, Set[A]], measure, measurable, events, increasing Fact) {
			b.Do(Simp(Fwd(DensityMeasureDef)))
			sigma := b.Have(
				"the measurable sets form a sigma algebra",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			measurableCuts := b.Have(
				"each cut is measurable",
				"∀n:num. extended_measurable(Ω, S, «cuts»(n))",
				b.ForEach(func(n *Expr[Nat]) Action {
					return By(
						events.At(n),
						sigma,
						measurable,
						measurable_function.ExtendedMeasurableOnEvent.At(Ω, S, a.Apply(n), ρ))
				}))
			risingCuts := b.Have(
				"the cuts to the increasing sets increase pointwise",
				"∀n:num. ∀x:A. x ∈ Ω ⇒ «cuts»(n, x) ≤ «cuts»(n + 1, x)",
				BySets(increasing, extended_nonneg_real.LeRefl, extended_nonneg_real.ZeroLe))
			b.Show(
				"monotone convergence passes the supremum through the integral",
				By(
					measure,
					measurableCuts,
					risingCuts,
					cutUnion,
					nonneg_integral.MonotoneConvergence.At(
						Ω, S, μ, b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«cuts»"))))
		})

		return ctx.Theorem(headline, func(b *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
			μ *Arrow[Set[A], ExtendedNonnegReal], ρ *Arrow[A, ExtendedNonnegReal], measure, measurable Fact) {
			sigma := b.Have(
				"the density mass lives on the σ-algebra of the original measure",
				"sigma_algebra_on(Ω, S)",
				By(measure, measure_space.MeasureOn.At(Ω, S, μ)))
			zero := b.Have(
				"the empty cut integrates to zero",
				"«ν»(∅) = &0",
				Simp(Fwd(DensityMeasureDef)),
				Derive(func(c *Argument) {
					empty := c.Have(
						"the cut to the empty set vanishes",
						"∀x:A. x ∈ Ω ⇒ «cut»(∅, x) = &0",
						BySets())
					f := c.TermAs[Fun[A, ExtendedNonnegReal]]("«cut»(∅)")
					zero := c.TermAs[Fun[A, ExtendedNonnegReal]]("λx:A. extended_of_real(&0)")
					c.Show(
						"integrate the zero function",
						By(
							empty,
							nonneg_integral.NonnegIntegralEqOn.At(Ω, S, μ, f, zero),
							nonneg_integral.NonnegIntegralZero.At(Ω, S, μ)))
				}))
			additive := b.Have(
				"the density masses add over two disjoint measurable sets",
				"∀E F:set(A). E ∈ S ∧ F ∈ S ∧ E ∩ F = ∅ ⇒ «ν»(E ∪ F) = «ν»(E) + «ν»(F)",
				Derive(func(c *Argument) {
					E := c.FixAs[Set[A]]("E")
					F := c.FixAs[Set[A]]("F")
					given := c.Assume()
					c.Show(
						"the cuts to the two sets add",
						By(measure, measurable, given, At(disjointAdditivity, Ω, S, μ, ρ, E, F)))
				}))
			continuous := b.Have(
				"the density mass is continuous along increasing sequences",
				Statement{
					Binders:    "∀a:(num → set(A)).",
					Hypotheses: []string{"∀n:num. a(n) ∈ S", "∀n:num. a(n) ⊆ a(n + 1)"},
					Conclusion: "«ν»(⋃image(a, 𝕌)) = extended_sup(image(λn:num. «ν»(a(n)), 𝕌))",
				},
				Derive(func(c *Argument) {
					a := c.FixAs[Fun[Nat, Set[A]]]("a")
					given := c.Assume()
					c.Show(
						"monotone convergence passes the supremum through the integral",
						By(measure, measurable, given, At(continuousFromBelow, Ω, S, μ, ρ, a)))
				}))
			b.Show(
				"an additive set function continuous from below is a measure",
				By(
					sigma,
					zero,
					additive,
					continuous,
					measure_space.MeasureFromContinuousIncreasing.At(
						Ω, S, b.TermAs[Fun[Set[A], ExtendedNonnegReal]]("«ν»"))))
		})
	}),
})}
