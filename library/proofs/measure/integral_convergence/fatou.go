// fatou.go — Fatou's lemma on a measure space: the integral of the lower
// limit of a sequence of measurable [0, ∞]-valued functions is at most the
// lower limit of their integrals. The lower limit is the supremum of the
// infima of the tails, and monotone convergence carries the integral
// through that supremum.

package integral_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/measure/measurable_function"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/set_image"
	"github.com/euc-ai/xugo/library/registry"
)

// Fatou — Fatou's lemma: for measurable [0, ∞]-valued functions f(n), the
// integral of their pointwise lower limit is at most the lower limit of
// their integrals. The lower limit is the supremum of the tail infima. The
// infimum from k is measurable (measurable_function.ExtendedMeasurableInf) and
// rises with k, a tail from k + 1 being part of the tail from k, so monotone
// convergence makes the integral of the lower limit the supremum of the
// integrals of the tail infima. The infimum from k lies below every
// f(k + n), so its integral lies below the infimum of theirs, and so below
// the lower limit of the integrals.
var Fatou = fatouThm{family.Add(registry.ProofEntry{
	Name: "Fatou",
	Key:  "prop_d49b34da95448ace",
	Build: family.Theorem(measure_space.MeasureOn.Statement(Statement{
		Binders:    "∀f:(num → A → extended_nonneg_real).",
		Hypotheses: []string{"∀n:num. extended_measurable(Ω, S, f(n))"},
		Conclusion: "nonneg_integral(Ω, S, μ, λx:A. extended_liminf(λn:num. f(n, x))) ≤ " +
			"extended_liminf(λn:num. nonneg_integral(Ω, S, μ, f(n)))",
		Abbrev: Abbrev{
			{Name: "tail", Text: "λk:num. λx:A. extended_inf(image(λn:num. f(k + n, x), 𝕌))"},
			{Name: "lowerLimit", Text: "extended_sup( " +
				"    image(λk:num. extended_inf(image(λn:num. nonneg_integral(Ω, S, μ, f(k + n)), 𝕌)), 𝕌))"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		measure Fact,
		f *Arrow2[Nat, A, ExtendedNonnegReal],
		measurable Fact,
	) {
		sigma := a.Conjuncts(
			a.Unfolded(measure, measure_space.MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")[0]
		tails := a.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("«tail»")
		lowerLimit := a.TermAs[ExtendedNonnegReal]("«lowerLimit»")
		tailMeasurable := a.Have(
			"each tail infimum is measurable, an infimum of the measurable f(k + n)",
			"∀k:num. extended_measurable(Ω, S, «tail»(k))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				b.Show(
					"the infimum of a measurable sequence",
					By(
						sigma,
						measurable,
						measurable_function.ExtendedMeasurableInf.At(
							Ω,
							S,
							b.TermAs[Fun2[Nat, A, ExtendedNonnegReal]]("λn:num. f(k + n)"))))
			}))
		tailBelow := a.Have(
			"the infimum of a tail lies below each of its terms",
			"∀k:num. ∀n:num. ∀x:A. extended_inf(image(λj:num. f(k + j, x), 𝕌)) ≤ f(k + n, x)",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				n := b.FixAs[Nat]("n")
				b.FixAs[A]("x")
				b.Show(
					"f(k + n, x) is one of its values",
					By(
						extended_nonneg_real.InfLower.At(
							b.TermAs[Set[ExtendedNonnegReal]]("image(λj:num. f(k + j, x), 𝕌)"),
							b.TermAs[ExtendedNonnegReal]("f(k + n, x)")),
						set_image.FunInRange.At(b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λj:num. f(k + j, x)"), n)))
			}))
		tailRising := a.Have(
			"the tail infima rise, the tail from k + 1 being part of the tail from k",
			"∀k:num. ∀x:A. "+
				"    extended_inf(image(λn:num. f(k + n, x), 𝕌)) ≤ extended_inf(image(λn:num. f(k + 1 + n, x), 𝕌))",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				x := b.FixAs[A]("x")
				shifted := b.Have(
					"the infimum from k lies below every term from k + 1 on",
					"∀n:num. extended_inf(image(λj:num. f(k + j, x), 𝕌)) ≤ f(k + 1 + n, x)",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						c.Show(
							"f(k + 1 + n, x) is the term k + (1 + n) of the tail from k",
							ByArith(tailBelow.At(k, c.TermAs[Nat]("1 + n"), x)))
					}))
				b.Show(
					"so it lies below their infimum",
					By(
						shifted,
						extended_nonneg_real.InfSequenceGreatest.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. f(k + 1 + n, x)"),
							b.TermAs[ExtendedNonnegReal]("extended_inf(image(λj:num. f(k + j, x), 𝕌))"))))
			}))
		integralsBelow := a.Have(
			"the integral of the infimum from k lies below the integrals of its tail, so below their infimum",
			"∀k:num. "+
				"    nonneg_integral(Ω, S, μ, «tail»(k)) ≤ "+
				"    extended_inf(image(λn:num. nonneg_integral(Ω, S, μ, f(k + n)), 𝕌))",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("k")
				tail := b.TermAs[Fun[A, ExtendedNonnegReal]]("«tail»(k)")
				each := b.Have(
					"the infimum from k lies below f(k + n), and its integral below that of f(k + n)",
					"∀n:num. nonneg_integral(Ω, S, μ, «tail»(k)) ≤ nonneg_integral(Ω, S, μ, f(k + n))",
					Derive(func(c *Argument) {
						c.FixAs[Nat]("n")
						c.Show(
							"the integral is monotone",
							By(
								tailBelow,
								nonneg_integral.NonnegIntegralMono.At(
									Ω,
									S,
									μ,
									tail,
									c.TermAs[Fun[A, ExtendedNonnegReal]]("f(k + n)"))))
					}))
				b.Show(
					"a lower bound of the integrals lies below their infimum",
					By(
						each,
						extended_nonneg_real.InfSequenceGreatest.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. nonneg_integral(Ω, S, μ, f(k + n))"),
							b.TermAs[ExtendedNonnegReal]("nonneg_integral(Ω, S, μ, «tail»(k))"))))
			}))
		belowLowerLimit := a.Have(
			"so each integral of a tail infimum lies below the lower limit of the integrals",
			"∀k:num. nonneg_integral(Ω, S, μ, «tail»(k)) ≤ «lowerLimit»",
			Derive(func(b *Argument) {
				k := b.FixAs[Nat]("k")
				b.Show(
					"the infimum of the integrals from k lies below the supremum of those infima",
					By(
						integralsBelow.At(k),
						extended_nonneg_real.SupSequenceUpper.At(
							b.TermAs[Fun[Nat, ExtendedNonnegReal]](
								"λj:num. extended_inf(image(λn:num. nonneg_integral(Ω, S, μ, f(j + n)), 𝕌))"),
							k),
						extended_nonneg_real.LeTrans))
			}))
		a.Do(Unfold(extended_nonneg_real.ExtendedLiminfDef))
		a.Show(
			"monotone convergence makes the integral of the lower "+
				"limit the supremum of the integrals of the tail infima",
			By(
				measure,
				tailMeasurable,
				tailRising,
				belowLowerLimit,
				nonneg_integral.MonotoneConvergence.At(Ω, S, μ, tails),
				extended_nonneg_real.SupSequenceLeast.At(
					a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λk:num. nonneg_integral(Ω, S, μ, «tail»(k))"),
					lowerLimit)))
	}),
})}
