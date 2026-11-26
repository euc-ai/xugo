// definitions.go — the chapter's definitional layer: a path is a
// continuous map from the unit interval, read as a subspace of the line;
// a set is path-connected when any two of its points are joined by a
// path running inside it; two paths join end to end, and a path runs
// backwards.
//
// The notions of a path, a path-connected set and a path component read
// the topology as their first argument and declare it implicit, as the
// one-space notions of topological_space do; joining and reversing read
// no topology.

package path_connected

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PathInDef — `path_in(T, g)`: g is continuous from the unit interval
// ⟦0, 1⟧, with the line's topology cut down to it, into the space.
var PathInDef = pathInDefThm{family.Define(registry.DefEntry{
	Name:     "PathInDef",
	Key:      "prop_2dde2a6bb17d9b8b",
	Const:    "path_in",
	Type:     "set(set(A)) → (real → A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀g:(real → A). " +
			"    path_in(T, g) ⇔ continuous_map(subtopology(real_topology, ⟦&0, &1⟧), T, g)",
	},
})}

// PathConnectedInDef — `path_connected_in(T, s)`: s lies in the space, and
// any two of its points are the two ends of a path whose values on ⟦0, 1⟧
// stay in s.
var PathConnectedInDef = pathConnectedInDefThm{family.Define(registry.DefEntry{
	Name:     "PathConnectedInDef",
	Key:      "prop_31288434938d3d23",
	Const:    "path_connected_in",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀s:set(A). " +
			"    path_connected_in(T, s) ⇔ " +
			"    s ⊆ ⋃T ∧ " +
			"    ∀x y:A. " +
			"        x ∈ s ∧ y ∈ s ⇒ " +
			"        ∃g:(real → A). path_in(T, g) ∧ image(g, ⟦&0, &1⟧) ⊆ s ∧ g(&0) = x ∧ g(&1) = y",
	},
	Deps: []registry.EntryLike{PathInDef},
})}

// PathComponentDef — `path_component(T, x)`: the points a path joins to x.
// Empty when x is not a point of the space. The topology is implicit
// under a law over it.
var PathComponentDef = pathComponentDefThm{family.Define(registry.DefEntry{
	Name:     "PathComponentDef",
	Key:      "prop_289e5aedd7a1b78e",
	Const:    "path_component",
	Type:     "set(set(A)) → A → set(A)",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀x:A. " +
			"    path_component(T, x) = {y:A | ∃g:(real → A). path_in(T, g) ∧ g(&0) = x ∧ g(&1) = y}",
	},
	Deps: []registry.EntryLike{PathInDef},
})}

// LocallyPathConnectedSpaceDef — `locally_path_connected_space(T)`: every
// open neighbourhood of a point holds a path-connected open neighbourhood
// of it.
var LocallyPathConnectedSpaceDef = locallyPathConnectedSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "LocallyPathConnectedSpaceDef",
	Key:   "prop_d8441660eec9b97",
	Const: "locally_path_connected_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    locally_path_connected_space(T) ⇔ " +
			"    ∀u:set(A). ∀x:A. u ∈ T ∧ x ∈ u ⇒ ∃v:set(A). v ∈ T ∧ path_connected_in(T, v) ∧ x ∈ v ∧ v ⊆ u",
	},
	Deps: []registry.EntryLike{PathConnectedInDef},
})}

// PathJoinDef — `path_join(g, h)`: g run at double speed on ⟦0, 1/2⟧,
// then h on ⟦1/2, 1⟧. It is a path when g ends where h begins (PathJoin);
// the definition asks nothing of either map.
var PathJoinDef = pathJoinDefThm{family.Define(registry.DefEntry{
	Name:  "PathJoinDef",
	Key:   "prop_86c7062eeb66d19c",
	Const: "path_join",
	Type:  "(real → A) → (real → A) → real → A",
	Equations: []string{
		"∀g h:(real → A). path_join(g, h) = λt:real. COND(t ≤ &1 / &2, g(&2 * t), h(&2 * t - &1))",
	},
})}

// PathReverseDef — `path_reverse(g)`: g run backwards, from its end to
// its start.
var PathReverseDef = pathReverseDefThm{family.Define(registry.DefEntry{
	Name:      "PathReverseDef",
	Key:       "prop_76677123b262e64f",
	Const:     "path_reverse",
	Type:      "(real → A) → real → A",
	Equations: []string{"∀g:(real → A). path_reverse(g) = λt:real. g(&1 - t)"},
})}
