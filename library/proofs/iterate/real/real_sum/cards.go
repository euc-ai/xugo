package real_sum

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/monoidal"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

var SubsetsSumToggleOdd = subsetsSumToggleOddThm{family.Add(registry.ProofEntry{
	Name: "SubsetsSumToggleOdd",
	Key:  "prop_8088f67c21e1e242",
	Reading: "i ∈ S is load-bearing: toggling a point outside S leaves the subsets of S, and " +
		"with S empty a function odd under the toggle can be 1 at ∅. The function is asked to be odd " +
		"at the subsets of S only. S may be infinite: the toggle preserves the set where f is not 0.",
	Deps: []registry.EntryLike{monoidal.Reindex, set_basic.ToggleInvolution},
	Build: family.Card(Statement{
		Binders: "∀S:set(A). ∀i:A. ∀f:(set(A) → real).",
		Hypotheses: []string{
			"i ∈ S",
			"∀X:set(A). X ⊆ S ⇒ f(set_toggle(i, X)) = -f(X)",
		},
		Conclusion: "Σ_{X∈{X:set(A) | X ⊆ S}} f(X) = &0",
	},
		"A function on the subsets of a set that changes sign when one point of the set is toggled "+
			"sums to 0. Toggling i is an involution of the subsets of S (ToggleInvolution, InToggle), "+
			"so the sum is unchanged when f is read after it (monoidal's Reindex, along the toggle as "+
			"its own inverse, with no finiteness asked), and that sum is the negative of the first."),
})}

var SubsetsSumDisjointUnion = subsetsSumDisjointUnionThm{family.Add(registry.ProofEntry{
	Name: "SubsetsSumDisjointUnion",
	Key:  "prop_f767ca77ecbb60d4",
	Reading: "Disjointness is load-bearing: a point of both sets is in Y ∪ Z for " +
		"three of the four choices, and the right side counts a subset more than once. " +
		"So is finiteness: with K infinite an inner sum heard at infinitely many " +
		"subsets reads 0. With K one point the inner sum is f(Y) + f(insert(i, Y)).",
	Deps: []registry.EntryLike{monoidal.Reindex, monoidal.Fubini},
	Build: family.Card(Statement{
		Binders: "∀J K:set(A). ∀f:(set(A) → real).",
		Hypotheses: []string{
			"finite(J)",
			"finite(K)",
			"disjoint(J, K)",
		},
		Conclusion: "Σ_{X∈{X:set(A) | X ⊆ J ∪ K}} f(X) = " +
			"Σ_{Y∈{Y:set(A) | Y ⊆ J}} Σ_{Z∈{Z:set(A) | Z ⊆ K}} f(Y ∪ Z)",
	},
		"A sum over the subsets of a disjoint union is the double sum over the subsets of the two parts. "+
			"A subset X of J ∪ K is Y ∪ Z for exactly one pair, Y = X ∩ J and Z = X ∩ K: the iterated sum is "+
			"a sum over the pairs (monoidal's Fubini), reindexed along these mutual inverses (Reindex)."),
})}
