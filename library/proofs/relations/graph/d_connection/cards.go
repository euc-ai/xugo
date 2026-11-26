package d_connection

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/d_separation"
	"github.com/euc-ai/xugo/library/proofs/relations/graph/dag"
	"github.com/euc-ai/xugo/library/registry"
)

var DConnectionIff = dConnectionIffThm{family.Add(registry.ProofEntry{
	Name: "DConnectionIff",
	Key:  "prop_4f5c3476cd6d638d",
	Reading: "The disjointness is load-bearing: a point of X ∩ Z is separated from " +
		"everything, while a path from it may be open, a path's endpoints never being tested. " +
		"Acyclicity is what lets a collider's directed path down to Z be spliced into the path. A " +
		"point of X or Y outside the vertex set has no edge, so it starts no path and is separated.",
	Deps: []registry.EntryLike{
		d_separation.DSeparatedDef,
		dag.AncestorsClosed,
		dag.DagWellfounded,
	},
	Build: family.Card(Statement{
		Binders: "∀V:set(A). ∀E:(A → A → bool). ∀X Y Z:set(A).",
		Hypotheses: []string{
			"dag_on(V, E)",
			"X ∩ Y = ∅",
			"X ∩ Z = ∅",
			"Y ∩ Z = ∅",
		},
		Conclusion: "d_separated(E, X, Y, Z) ⇔ " +
			"¬(∃x y:A. ∃l:list(A). x ∈ X ∧ y ∈ Y ∧ d_open_path(E, Z, cons(x, list_append(l, cons(y, nil)))))",
	},
		"Pearl's reading of separation: Z separates X from Y exactly when no path from a point of "+
			"X to a point of Y is open given Z (Lauritzen, Dawid, Larsen and Leimer, 1990). ⇒: an "+
			"open path lies in the ancestors of X ∪ Y ∪ Z, its colliders being ancestors of Z and "+
			"every other vertex an ancestor of an endpoint or of a collider; replacing each collider "+
			"by the moral edge between its neighbours gives a chain in the moral graph avoiding Z. ⇐: "+
			"a moral chain avoiding Z lifts to a path, a moral edge through a common child w becoming "+
			"the collider w, which is an ancestor of X ∪ Y ∪ Z; a collider that is an ancestor of X "+
			"or Y only is bypassed along its directed path there, and the shortest such path is open."),
})}
