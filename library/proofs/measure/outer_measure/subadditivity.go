package outer_measure

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/registry"
)

// Subadditive — an outer measure is finitely subadditive on its carrier:
// the measure of the union of two of its subsets is at most the sum of
// their measures. The sequence s, t, ∅, ∅, … lies in the carrier and its
// union is s ∪ t; past its first two terms its measures vanish, so
// countable subadditivity bounds μ(s ∪ t) by μ(s) + μ(t).
var Subadditive = subadditiveThm{family.Add(registry.ProofEntry{
	Name: "Subadditive",
	Key:  "prop_88a4e05e16496b60",
	Build: family.Theorem(OuterMeasureOn.Statement(Statement{
		Binders:    "∀s t:set(A).",
		Hypotheses: []string{"s ⊆ Ω", "t ⊆ Ω"},
		Conclusion: "μ(s ∪ t) ≤ μ(s) + μ(t)",
		Abbrev: Abbrev{
			{Name: "pair", Text: "λn:num. {y:A | n = 0 ∧ y ∈ s ∨ n = 1 ∧ y ∈ t}"},
		},
	}), func(
		a *Argument,
		Ω *Expr[Set[A]],
		μ *Arrow[Set[A], ExtendedNonnegReal],
		outer Fact,
		s, t *Expr[Set[A]],
		sInside, tInside Fact,
	) {
		laws := a.Conjuncts(
			a.Unfolded(outer, OuterMeasureOn),
			"the empty set has measure 0",
			"inclusion increases the measure",
			"a countable union has measure at most the series of the measures")
		emptyMass, countable := laws[0], laws[2]
		pair := a.TermAs[Fun[Nat, Set[A]]]("«pair»")
		measures := a.TermAs[Fun[Nat, ExtendedNonnegReal]]("λn:num. μ(«pair»(n))")
		inside := a.Have(
			"every set of the sequence s, t, ∅, ∅, … lies in Ω",
			"∀n:num. «pair»(n) ⊆ Ω",
			BySets(sInside, tInside))
		union := a.Have(
			"the union of the sequence is s ∪ t",
			"⋃image(«pair», 𝕌) = s ∪ t",
			BySets())
		tail := a.Have(
			"past index 1 the sets are empty, of measure 0",
			"∀n:num. 1 < n ⇒ μ(«pair»(n)) = &0",
			Derive(func(b *Argument) {
				b.FixAs[Nat]("n")
				past := b.Assume()
				neither := b.Have(
					"n is neither 0 nor 1",
					"n ≠ 0 ∧ n ≠ 1",
					ByArith(past))
				empty := b.Have(
					"so the n-th set is empty",
					"«pair»(n) = ∅",
					BySets(neither))
				b.Show(
					"and ∅ has measure 0",
					By(emptyMass, empty))
			}))
		truncated := a.Have(
			"so the series of their measures is its partial sum up to 1",
			"extended_series(λn:num. μ(«pair»(n))) = Σ_{i∈0 .. 1} μ(«pair»(i))",
			By(tail, extended_nonneg_real.SeriesEventuallyZero))
		twoTerms := a.Have(
			"which is the sum of its first two terms",
			"Σ_{i∈0 .. 1} μ(«pair»(i)) = μ(«pair»(0)) + μ(«pair»(1))",
			By(
				extended_nonneg_real.SumSegmentPeel.At(measures, a.TermAs[Nat]("0")),
				extended_nonneg_real.SumSegmentZero.At(measures),
				nat_arith.AddLeftZeroClause.At(a.TermAs[Nat]("1"))))
		firstTwo := a.Have(
			"the first two sets are s and t",
			"«pair»(0) = s ∧ «pair»(1) = t",
			BySets(nat_arith.OneNotZero))
		sum := a.Have(
			"so the series is μ(s) + μ(t)",
			"extended_series(λn:num. μ(«pair»(n))) = μ(s) + μ(t)",
			truncated.Rw(),
			twoTerms.Rw(),
			By(firstTwo))
		a.Show(
			"countable subadditivity bounds the measure of the union, which is s ∪ t",
			By(inside, union, sum, countable.At(pair)))
	}),
})}
