// definitions.go — the chapter's definitional layer beyond the
// structure: what a closed set is, the largest open set inside a set
// and the smallest closed set around one, the topology a subset
// inherits, the separation property a space may have, and the two
// properties a subset of a space may have — compactness and
// connectedness.
//
// Every constant here but `hausdorff` reads the topology as its first
// argument and declares it implicit: where a binder named `T` is in
// scope — a law over `is_topology(T)` — a statement writes
// `closed_in(c)` or `interior(s)` and the parser completes the family
// from that binder. The chapter spells the family wherever no axiom
// enters, though the parser would accept the short form there too: the
// spelling is a convention the reader checks, not the parser. The
// definitions themselves spell it, as every definition does.

package topological_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ClosedInDef — `closed_in(T, c)`: c lies in the space, and its
// complement in the space is open.
var ClosedInDef = closedInDefThm{family.Define(registry.DefEntry{
	Name:      "ClosedInDef",
	Key:       "prop_cce7946558a90f34",
	Const:     "closed_in",
	Type:      "set(set(A)) → set(A) → bool",
	Implicit:  []string{"T"},
	Equations: []string{"∀T:set(set(A)). ∀c:set(A). closed_in(T, c) ⇔ c ⊆ ⋃T ∧ ⋃T ∖ c ∈ T"},
	// The mints of the constants the definiens spells: inclusion, the
	// union of a family, difference and membership.
})}

// InteriorDef — `interior(T, s)`: the union of the open sets inside s,
// the largest open set s contains.
var InteriorDef = interiorDefThm{family.Define(registry.DefEntry{
	Name:      "InteriorDef",
	Key:       "prop_12b24d8c4599806a",
	Const:     "interior",
	Type:      "set(set(A)) → set(A) → set(A)",
	Implicit:  []string{"T"},
	Equations: []string{"∀T:set(set(A)). ∀s:set(A). interior(T, s) = ⋃{u:set(A) | u ∈ T ∧ u ⊆ s}"},
})}

// ClosureDef — `closure(T, s)`: the intersection of the closed sets
// around s, the smallest closed set containing s. For s inside the
// space the space itself is one of those sets; for s outside it the
// family is empty and its intersection is everything, so a law about
// the closure carries `s ⊆ ⋃T`.
var ClosureDef = closureDefThm{family.Define(registry.DefEntry{
	Name: "ClosureDef",
	Key:  "prop_d24d23fca7823e64",
	Reading: "The intersection of no closed sets is the whole type: for s outside the " +
		"space no closed set is around it and closure(T, s) = 𝕌. A law about the closure " +
		"therefore carries s ⊆ ⋃T, under which the space itself is a closed set around s.",
	Const:    "closure",
	Type:     "set(set(A)) → set(A) → set(A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). closure(T, s) = ⋂{c:set(A) | closed_in(T, c) ∧ s ⊆ c}",
	},
	Deps: []registry.EntryLike{ClosedInDef},
})}

// SubtopologyDef — `subtopology(T, s)`: the open sets of s as a
// subspace, each open set of T cut down to s.
var SubtopologyDef = subtopologyDefThm{family.Define(registry.DefEntry{
	Name:      "SubtopologyDef",
	Key:       "prop_e7ce4a1875d76d7d",
	Const:     "subtopology",
	Type:      "set(set(A)) → set(A) → set(set(A))",
	Implicit:  []string{"T"},
	Equations: []string{"∀T:set(set(A)). ∀s:set(A). subtopology(T, s) = image(λu:set(A). u ∩ s, T)"},
})}

// HausdorffDef — `hausdorff(T)`: two distinct points of the space lie
// in disjoint open sets. A property of the space, so the topology is
// its one argument and is spelled.
var HausdorffDef = hausdorffDefThm{family.Define(registry.DefEntry{
	Name:  "HausdorffDef",
	Key:   "prop_5f5f8c9411588344",
	Const: "hausdorff",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    hausdorff(T) ⇔ " +
			"    ∀x y:A. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅",
	},
})}

// TopologyBaseDef — `topology_base(T, b)`: b is a family of open sets, and
// every point of an open set lies in a member of b inside that open set.
// The topology is implicit under a law over it.
var TopologyBaseDef = topologyBaseDefThm{family.Define(registry.DefEntry{
	Name:     "TopologyBaseDef",
	Key:      "prop_9815c1c1d646324a",
	Const:    "topology_base",
	Type:     "set(set(A)) → set(set(A)) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T b:set(set(A)). " +
			"    topology_base(T, b) ⇔ " +
			"    b ⊆ T ∧ ∀u:set(A). ∀x:A. u ∈ T ∧ x ∈ u ⇒ ∃v:set(A). v ∈ b ∧ x ∈ v ∧ v ⊆ u",
	},
})}

// TopologyGeneratedDef — `topology_generated(b)`: the intersection of the
// topologies containing b, the smallest of them.
var TopologyGeneratedDef = topologyGeneratedDefThm{family.Define(registry.DefEntry{
	Name:  "TopologyGeneratedDef",
	Key:   "prop_bcf44b43cf794ce2",
	Const: "topology_generated",
	Type:  "set(set(A)) → set(set(A))",
	Equations: []string{
		"∀b:set(set(A)). topology_generated(b) = ⋂{T:set(set(A)) | is_topology(T) ∧ b ⊆ T}",
	},
	Deps: []registry.EntryLike{IsTopology},
})}

// DerivedSetDef — `derived_set(T, s)`: the limit points of s, the points of
// the space every open neighbourhood of which holds a point of s other
// than the point itself. The topology is implicit under a law over it.
var DerivedSetDef = derivedSetDefThm{family.Define(registry.DefEntry{
	Name:     "DerivedSetDef",
	Key:      "prop_ad52a70d5b64a867",
	Const:    "derived_set",
	Type:     "set(set(A)) → set(A) → set(A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). " +
			"    derived_set(T, s) = {x:A | x ∈ ⋃T ∧ ∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ∃y:A. y ≠ x ∧ y ∈ s ∧ y ∈ u}",
	},
})}

// FrontierDef — `frontier(T, s)`: the closure of s less its interior. As
// for the closure, a law about it carries `s ⊆ ⋃T`. The topology is
// implicit under a law over it.
var FrontierDef = frontierDefThm{family.Define(registry.DefEntry{
	Name:     "FrontierDef",
	Key:      "prop_a727454e4f8e9307",
	Const:    "frontier",
	Type:     "set(set(A)) → set(A) → set(A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). frontier(T, s) = closure(T, s) ∖ interior(T, s)",
	},
	Deps: []registry.EntryLike{ClosureDef, InteriorDef},
})}
