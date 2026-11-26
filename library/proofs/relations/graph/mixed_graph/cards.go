package mixed_graph

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/closure"
	"github.com/euc-ai/xugo/library/registry"
)

var DistrictsPartition = districtsPartitionThm{family.Add(registry.ProofEntry{
	Name: "DistrictsPartition",
	Key:  "prop_7049128a1ebda07e",
	Reading: "Symmetry of B is load-bearing: a one-way edge would make reachability inside " +
		"S a preorder, not an equivalence, and two districts could overlap without being equal.",
	Deps: []registry.EntryLike{closure.ReflexiveTransitiveClosureEquivalenceOn},
	Build: family.Card(Statement{
		Binders:    "∀B:(A → A → bool). ∀S:set(A).",
		Hypotheses: []string{"∀u v:A. B(u, v) ⇒ B(v, u)"},
		Conclusion: "(∀C:set(A). C ∈ mixed_graph_districts(B, S) ⇒ C ≠ ∅ ∧ C ⊆ S) ∧ " +
			"(∀C C':set(A). " +
			"    C ∈ mixed_graph_districts(B, S) ∧ C' ∈ mixed_graph_districts(B, S) ∧ C ∩ C' ≠ ∅ ⇒ C = C') ∧ " +
			"⋃mixed_graph_districts(B, S) = S ∧ " +
			"(finite(S) ⇒ finite(mixed_graph_districts(B, S)))",
	},
		"The districts of S partition it: bidirected reachability inside S is an "+
			"equivalence on S, B being symmetric, and the districts are its classes, each "+
			"holding its own vertex; a finite S has finitely many, as the image of S."),
})}

var HedgeRootsWhole = hedgeRootsWholeThm{family.Add(registry.ProofEntry{
	Name: "HedgeRootsWhole",
	Key:  "prop_ab0ce464b5357d3d",
	Reading: "No acyclicity and no finiteness is used. The smaller forest serves " +
		"as the root set: its vertices reach the roots inside it, off X, so each is " +
		"an ancestor of Y once the edges into X are deleted. F′ ∩ X = ∅ is the " +
		"clause that gives this. With an empty smaller forest both sides are false.",
	Deps: []registry.EntryLike{HedgeDef, CForestDef},
	Build: family.Card(Statement{
		Binders: "∀D B:(A → A → bool). ∀X Y F F':set(A).",
		Conclusion: "mixed_graph_hedge(D, B, X, Y, F, F') ⇔ " +
			"mixed_graph_c_forest(D, B, F, F') ∧ " +
			"mixed_graph_c_forest(D, B, F', F') ∧ " +
			"F ∩ X ≠ ∅ ∧ " +
			"F' ∩ X = ∅ ∧ " +
			"F' ⊆ dag_ancestors(dag_delete_in(D, X), Y)",
	},
		"A hedge is one whose root set is the smaller forest. ⇒: the roots R lie in F′, so reaching "+
			"R is reaching F′, and a vertex of F′ reaches itself; a vertex of F′ reaches a root along "+
			"edges inside F′, none of which enters X, and the root reaches Y. ⇐: take R = F′."),
})}
