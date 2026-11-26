package measure_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/extended_nonneg_real"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/sigma_algebra"
	"github.com/euc-ai/xugo/library/registry"
)

// MeasureFiniteAdditive — the measure of the union of finitely many
// disjoint measurable sets is the sum of their measures. By induction over
// the finite index set, carrying the measurability of the union along: a
// new index a brings the set E(a), which meets none of the earlier ones, so
// the union over insert(a, u) is the disjoint union of E(a) and the union
// over u, and additivity adds the new term to the sum.
var MeasureFiniteAdditive = measureFiniteAdditiveThm{family.Add(registry.ProofEntry{
	Name: "MeasureFiniteAdditive",
	Key:  "prop_46549c95d36db9ce",
	Build: family.Theorem(MeasureOn.Statement(Statement{
		Binders: "∀E:(B → set(A)). ∀k:set(B).",
		Hypotheses: []string{
			"finite(k)",
			"∀i:B. i ∈ k ⇒ E(i) ∈ S",
			"∀i j:B. i ∈ k ∧ j ∈ k ∧ i ≠ j ⇒ disjoint(E(i), E(j))",
		},
		Conclusion: "μ(⋃image(E, k)) = Σ_{i∈k} μ(E(i))",
	}), func(arg *Argument, Ω *Expr[Set[A]], S *Expr[Set[Set[A]]],
		μ *Arrow[Set[A], ExtendedNonnegReal], measure Fact,
		E *Arrow[B, Set[A]], k *Expr[Set[B]], finite, measurable, disjoint Fact) {
		laws := arg.Conjuncts(
			arg.Unfolded(measure, MeasureOn),
			"the measurable sets form a sigma algebra",
			"the empty set has measure zero",
			"countable disjoint unions have the series of their measures")
		sigma, emptyMass := laws[0], laws[1]
		operations := sigma_algebra.SigmaFiniteOperations.At(Ω, S)
		whole := arg.Have(
			"over every finite index set of disjoint measurable sets "+
				"the union is measurable and measures the sum, and so over k",
			"⋃image(E, k) ∈ S ∧ μ(⋃image(E, k)) = Σ_{i∈k} μ(E(i))",
			ByInduction(finite_set.FiniteInductFresh, finite, Generalizing(measurable, disjoint), Case(
				"over ∅ the union is empty and the sum is 0",
				Derive(func(b *Argument) {
					empty := b.Have(
						"no index, no point of the union",
						"⋃image(E, ∅) = ∅",
						BySets())
					b.Show(
						"the empty set is measurable, of measure 0",
						By(Normalized, empty, sigma, operations, emptyMass, extended_nonneg_real.SumClauses))
				})),
				Case(
					"a new index a brings a set E(a) disjoint from the union so far",
					Derive(func(b *Argument) {
						a := b.FixAs[B]("a")
						b.FixAs[Set[B]]("u")
						previous := b.Assume()
						onInsert := b.Assume()
						restricted := b.Have(
							"the hypotheses hold on u, which lies inside insert(a, u)",
							"(∀i:B. i ∈ u ⇒ E(i) ∈ S) ∧ (∀i j:B. i ∈ u ∧ j ∈ u ∧ i ≠ j ⇒ disjoint(E(i), E(j)))",
							BySets(onInsert))
						earlier := b.Have(
							"so the union over u is measurable and measures the sum over u",
							"⋃image(E, u) ∈ S ∧ μ(⋃image(E, u)) = Σ_{i∈u} μ(E(i))",
							By(restricted, previous))
						apart := b.Have(
							"a is new, so E(a) meets none of the sets indexed by u",
							"∀i:B. i ∈ u ⇒ disjoint(E(i), E(a))",
							BySets(onInsert, previous))
						pieces := b.Have(
							"the union over insert(a, u) is E(a) together with the union over u, disjointly",
							"⋃image(E, insert(a, u)) = E(a) ∪ ⋃image(E, u) ∧ E(a) ∩ ⋃image(E, u) = ∅",
							BySets(apart))
						newMeasurable := b.Have(
							"E(a) is measurable",
							"E(a) ∈ S",
							By(onInsert, set_basic.InInsert))
						b.Show(
							"so the union is measurable, and additivity adds the new term to the sum",
							By(
								pieces,
								earlier,
								newMeasurable,
								previous,
								sigma,
								operations,
								MeasureAdditive.At(Ω, S, μ, E.Apply(a), b.TermAs[Set[A]]("⋃image(E, u)")),
								measure,
								extended_nonneg_real.SumClauses,
								set_basic.InInsert))
					}))))
		arg.Show(
			"the measure equation",
			By(whole))
	}),
})}
