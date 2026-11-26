package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasureAdditive — the measure of a disjoint union of two measurable sets is
// the sum of their measures. Pad the pair with empty sets and apply countable
// additivity; the resulting series has only its first two terms.
var MeasureAdditive = measureAdditiveThm{family.Add(registry.ProofEntry{
	Name: "MeasureAdditive",
	Key:  "prop_44d8464fef296c8f",
	Build: family.Theorem(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀E D:set(A).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"E ∈ S",
			"D ∈ S",
			"E ∩ D = ∅",
		},
		Conclusion: "μ(E ∪ D) = μ(E) + μ(D)",
		Abbrev: Abbrev{
			{Name: "pair", Text: "λn:num. {x:A | n = 0 ∧ x ∈ E ∨ n = 1 ∧ x ∈ D}"},
		},
	}, func(a *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], extended_nonneg_real.ExtendedNonnegReal], E, D *Expr[Set[A]], h Fact) {
		premises := a.Conjuncts(
			h,
			"The measure axioms hold",
			"E is measurable",
			"D is measurable",
			"E and D are disjoint")
		measurableE, measurableD, disjointED := premises[1], premises[2], premises[3]
		laws := a.Conjuncts(
			a.Unfolded(premises[0], MeasureOn),
			"The measurable sets form a sigma algebra",
			"The empty set has measure zero",
			"Countable disjoint unions have the series of their measures")
		sigma, emptyMass, countable := laws[0], laws[1], laws[2]
		pair := a.TermAs[Fun[Nat, Set[A]]]("«pair»")
		measures := a.TermAs[Fun[Nat, extended_nonneg_real.ExtendedNonnegReal]](
			"λn:num. μ(«pair»(n))")
		measurable := a.Have(
			"Every term of the padded pair is measurable",
			"∀n:num. «pair»(n) ∈ S",
			Derive(func(b *Argument) {
				values := b.Have(
					"The sequence takes E, D, and then the empty set",
					"∀n:num. «pair»(n) = COND(n = 0, E, COND(n = 1, D, ∅))",
					BySets(nat_arith.OneNotZero))
				empty := b.Have(
					"The padding set is measurable",
					"∅ ∈ S",
					By(sigma, sigma_algebra.SigmaFiniteOperations.At(Ω, S)))
				b.Show(
					"Each of the three possible values belongs to the sigma algebra",
					By(values, measurableD, measurableE, empty))
			}))
		disjoint := a.Have(
			"Distinct terms of the padded pair are disjoint",
			"∀i j:num. i ≠ j ⇒ «pair»(i) ∩ «pair»(j) = ∅",
			BySets(disjointED))
		union := a.Have(
			"Padding leaves the union unchanged",
			"⋃image(«pair», 𝕌) = E ∪ D",
			BySets())
		tail := a.Have(
			"Every measure after index one vanishes",
			"∀n:num. 1 < n ⇒ μ(«pair»(n)) = &0",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				past := b.Assume()
				neither := b.Have(
					"A later index is neither zero nor one",
					"n ≠ 0 ∧ n ≠ 1",
					ByArith(past))
				empty := b.Have(
					"The corresponding set is empty",
					"«pair»(n) = ∅",
					BySets(neither))
				b.Show(
					"Its measure is zero",
					By(emptyMass, empty))
			}))
		truncated := a.Have(
			"The series is its partial sum through index one",
			"extended_series(λn:num. μ(«pair»(n))) = Σ_{i∈0 .. 1} μ(«pair»(i))",
			By(tail, extended_nonneg_real.SeriesEventuallyZero))
		twoTerms := a.Have(
			"The partial sum has exactly the first two terms",
			"Σ_{i∈0 .. 1} μ(«pair»(i)) = μ(«pair»(0)) + μ(«pair»(1))",
			By(
				extended_nonneg_real.SumSegmentPeel.At(measures, a.TermAs[Nat]("0")),
				extended_nonneg_real.SumSegmentZero.At(measures),
				nat_arith.AddLeftZeroClause.At(a.TermAs[Nat]("1"))))
		firstTwo := a.Have(
			"The first two sets are E and D",
			"«pair»(0) = E ∧ «pair»(1) = D",
			BySets(nat_arith.OneNotZero))
		a.Show(
			"Countable additivity reduces to the sum of the two measures",
			By(measurable, disjoint, countable.At(pair), union, truncated, twoTerms, firstTwo))
	}),
})}
