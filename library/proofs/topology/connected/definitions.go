// definitions.go — the chapter's definitional layer: a subset of a space
// is connected when two open sets that cover it and each meet it share a
// point of it, and the component of a point is the union of the
// connected sets holding it. The topology is the first argument and is
// implicit under a law over it, as it is for `closed_in`.

package connected

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ConnectedInDef — `connected_in(T, k)`: k lies in the space ⋃T, and
// two open sets that cover k and each meet it share a point of k. The
// contrapositive is the textbook sentence, that k is not split by two
// open sets each meeting it and disjoint on k (disjoint on k, not
// disjoint outright: two open sets may overlap outside k and still
// split it); the positive form is a Horn clause, which is what a proof
// applies. The empty set is connected. The topology is implicit under
// a law over it.
var ConnectedInDef = connectedInDefThm{family.Define(registry.DefEntry{
	Name:     "ConnectedInDef",
	Key:      "prop_3cf2865f2fa533ef",
	Const:    "connected_in",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀k:set(A). " +
			"    connected_in(T, k) ⇔ " +
			"    k ⊆ ⋃T ∧ " +
			"    ∀u v:set(A). u ∈ T ∧ v ∈ T ∧ k ⊆ u ∪ v ∧ ¬(k ∩ u = ∅) ∧ ¬(k ∩ v = ∅) ⇒ ¬(k ∩ u ∩ v = ∅)",
	},
})}

// ConnectedComponentDef — `connected_component(T, x)`: the union of the
// connected sets holding x — the largest of them, x's component. Empty
// when x is not a point of the space. The topology is implicit under a
// law over it.
var ConnectedComponentDef = connectedComponentDefThm{family.Define(registry.DefEntry{
	Name:     "ConnectedComponentDef",
	Key:      "prop_5e46f838bced3008",
	Const:    "connected_component",
	Type:     "set(set(A)) → A → set(A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀x:A. connected_component(T, x) = ⋃{s:set(A) | connected_in(T, s) ∧ x ∈ s}",
	},
	Deps: []registry.EntryLike{ConnectedInDef},
})}

// LocallyConnectedSpaceDef — `locally_connected_space(T)`: every open
// neighbourhood of a point holds a connected open neighbourhood of it. A
// property of the space, so the topology is its one argument and is
// spelled.
var LocallyConnectedSpaceDef = locallyConnectedSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "LocallyConnectedSpaceDef",
	Key:   "prop_9ade121d9e2d8cf4",
	Const: "locally_connected_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    locally_connected_space(T) ⇔ " +
			"    ∀u:set(A). ∀x:A. u ∈ T ∧ x ∈ u ⇒ ∃v:set(A). v ∈ T ∧ connected_in(T, v) ∧ x ∈ v ∧ v ⊆ u",
	},
	Deps: []registry.EntryLike{ConnectedInDef},
})}
