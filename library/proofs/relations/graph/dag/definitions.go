// definitions.go — a finite directed acyclic graph as a vertex set and
// an edge relation, and the operations on the edge relation that the
// causal chapters read: parents, ancestors and descendants, ancestral
// sets, deleting the edges into or out of a set, and adding one root above
// a set.

package dag

import (
	"github.com/euc-ai/xugo/library/registry"
)

// DagOn — `dag_on(V, E)`: V is finite, every edge has both ends in V,
// and no vertex reaches itself along the edges.
var DagOn = dagOnThm{family.DefineStructure(registry.DefEntry{
	Name:    "DagOn",
	Key:     "prop_98dc1bbc4c6ee553",
	Const:   "dag_on",
	Subject: "V",
	Type:    "set(A) → (A → A → bool) → bool",
	Equations: []string{
		"∀V:set(A). ∀E:(A → A → bool). " +
			"    dag_on(V, E) ⇔ " +
			"    finite(V) ∧ (∀x y:A. E(x, y) ⇒ x ∈ V ∧ y ∈ V) ∧ (∀x:A. ¬transitive_closure(E, x, x))",
	},
})}

// ParentsDef — the parents of v are the tails of the edges into v.
var ParentsDef = parentsDefThm{family.Define(registry.DefEntry{
	Name:           "ParentsDef",
	Key:            "prop_2cecbd75fb014e18",
	Const:          "dag_parents",
	Type:           "(A → A → bool) → A → set(A)",
	MembershipRead: true,
	Equations: []string{
		"∀E:(A → A → bool). ∀v:A. dag_parents(E, v) = {u:A | E(u, v)}",
	},
})}

// AncestorsDef — the ancestors of a set X are the points that reach X
// along the edges in zero or more steps, so X lies among its own
// ancestors.
var AncestorsDef = ancestorsDefThm{family.Define(registry.DefEntry{
	Name:           "AncestorsDef",
	Key:            "prop_840584bd72512eb6",
	Const:          "dag_ancestors",
	Type:           "(A → A → bool) → set(A) → set(A)",
	MembershipRead: true,
	Equations: []string{
		"∀E:(A → A → bool). ∀X:set(A). " +
			"    dag_ancestors(E, X) = {u:A | ∃x:A. x ∈ X ∧ reflexive_transitive_closure(E, u, x)}",
	},
})}

// AncestralDef — U is ancestral when every parent of a point of U lies
// in U, so a walk that ends in U runs inside U.
var AncestralDef = ancestralDefThm{family.Define(registry.DefEntry{
	Name:  "AncestralDef",
	Key:   "prop_5846eaf2671626d7",
	Const: "dag_ancestral",
	Type:  "(A → A → bool) → set(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀U:set(A). dag_ancestral(E, U) ⇔ ∀u v:A. E(u, v) ∧ v ∈ U ⇒ u ∈ U",
	},
})}

// DescendantsDef — the descendants of a set X are the points X reaches
// along the edges in zero or more steps, X itself included.
var DescendantsDef = descendantsDefThm{family.Define(registry.DefEntry{
	Name:           "DescendantsDef",
	Key:            "prop_c0d6f008f3ac62fd",
	Const:          "dag_descendants",
	Type:           "(A → A → bool) → set(A) → set(A)",
	MembershipRead: true,
	Equations: []string{
		"∀E:(A → A → bool). ∀X:set(A). " +
			"    dag_descendants(E, X) = {u:A | ∃x:A. x ∈ X ∧ reflexive_transitive_closure(E, x, u)}",
	},
})}

// DeleteInDef — deleting the edges into X keeps the edges whose head is
// outside X: the graph an intervention on X leaves.
var DeleteInDef = deleteInDefThm{family.Define(registry.DefEntry{
	Name:  "DeleteInDef",
	Key:   "prop_a4abc5119ec3758a",
	Const: "dag_delete_in",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀X:set(A). ∀u v:A. dag_delete_in(E, X, u, v) ⇔ E(u, v) ∧ v ∉ X",
	},
})}

// DeleteOutDef — deleting the edges out of Z keeps the edges whose tail
// is outside Z.
var DeleteOutDef = deleteOutDefThm{family.Define(registry.DefEntry{
	Name:  "DeleteOutDef",
	Key:   "prop_11268de4fe1ab88c",
	Const: "dag_delete_out",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀Z:set(A). ∀u v:A. dag_delete_out(E, Z, u, v) ⇔ E(u, v) ∧ u ∉ Z",
	},
})}

// AddRootDef — `dag_add_root(E, Z)` is the graph on option(A) with an
// edge some(u) → some(v) for each edge u → v and an edge none → some(z)
// for each z ∈ Z: the old vertices embedded by some, and none a new
// root pointing at Z. Its vertex set is image(some, V) with none added.
var AddRootDef = addRootDefThm{family.Define(registry.DefEntry{
	Name:  "AddRootDef",
	Key:   "prop_1296d4cd0018db84",
	Const: "dag_add_root",
	Type:  "(A → A → bool) → set(A) → option(A) → option(A) → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀Z:set(A). ∀p q:option(A). " +
			"    dag_add_root(E, Z, p, q) ⇔ " +
			"    (∃u v:A. p = some(u) ∧ q = some(v) ∧ E(u, v)) ∨ (∃z:A. p = none ∧ q = some(z) ∧ z ∈ Z)",
	},
})}

// PairRelationDef — the relation whose steps are the members of a set of
// ordered pairs. A concrete graph is written with an enumerated datatype
// for its vertices and a finite set literal of pairs for its edges.
var PairRelationDef = pairRelationDefThm{family.Define(registry.DefEntry{
	Name:  "PairRelationDef",
	Key:   "prop_462087b1e4f9376",
	Const: "pair_relation",
	Type:  "set(prod(A, A)) → A → A → bool",
	Equations: []string{
		"∀P:set(prod(A, A)). ∀x y:A. pair_relation(P, x, y) ⇔ (x, y) ∈ P",
	},
})}
