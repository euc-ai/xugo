package d_separation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/registry"
)

var DSeparatedAncestralRestrict = dSeparatedAncestralRestrictThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedAncestralRestrict",
	Key:  "prop_190be98fb55d3cdc",
	Reading: "The parent-closure of P is load-bearing: it keeps every ancestor of the " +
		"three groups, and every common child in their ancestral set, inside P. Deleting edges " +
		"keeps P parent-closed, so the lemma applies to the edge-deleted graphs the rules read.",
	Deps: []registry.EntryLike{dag.AncestorsUpperBound},
	Build: family.Card(Statement{
		Binders: "∀E:(A → A → bool). ∀P X Y Z:set(A).",
		Hypotheses: []string{
			"dag_ancestral(E, P)",
			"X ∪ Y ∪ Z ⊆ P",
		},
		Conclusion: "d_separated(relation_on(P, E), X, Y, Z) ⇔ d_separated(E, X, Y, Z)",
	},
		"Separation of groups inside a parent-closed set P is the same in the graph and in its "+
			"restriction to P: the ancestors of X ∪ Y ∪ Z lie in P (AncestorsUpperBound) and are "+
			"the same in both graphs, and so are the edges among them and their common children."),
})}

var DSeparatedRemoveIntervene = dSeparatedRemoveInterveneThm{family.Add(registry.ProofEntry{
	Name: "DSeparatedRemoveIntervene",
	Key:  "prop_fd4c7307889e0bbf",
	Reading: "D disjoint from the three groups is load-bearing. With the edges into D deleted, " +
		"a point of D is a root: it is reached by no path from outside D, so the ancestors outside " +
		"D are those of the graph without D, and conditioning on D removes it from the moral graph.",
	Deps: []registry.EntryLike{dag.AncestorsUpperBound, dag.AncestorsRootUnion},
	Build: family.Card(Statement{
		Binders:    "∀E:(A → A → bool). ∀D X Y W:set(A).",
		Hypotheses: []string{"D ∩ (X ∪ Y ∪ W) = ∅"},
		Conclusion: "d_separated(relation_on(𝕌 ∖ D, E), X, Y, W) ⇔ " +
			"d_separated(dag_delete_in(E, D), X, Y, D ∪ W)",
	},
		"Removing D from the graph is intervening on D and conditioning on it: in the graph with the "+
			"edges into D deleted, the ancestors of X ∪ Y ∪ W ∪ D outside D are reached by paths avoiding "+
			"D, so they are the ancestors in the graph without D; a common child in that set lies outside "+
			"D, its parents outside D the same in both graphs; and D, conditioned on, is removed. The moral "+
			"graphs restricted outside the conditioning sets coincide. This is the bridge the transfer of a "+
			"derivation from G[V ∖ D] to G reads, edge deletions inside the rules commuting with both sides."),
})}
