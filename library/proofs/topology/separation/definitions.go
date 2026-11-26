// definitions.go — the chapter's definitional layer: a space is normal
// when two disjoint closed sets lie in disjoint open sets. A property of
// the space, so the topology is its one argument and is spelled, as
// `hausdorff(T)` is.

package separation

import (
	"github.com/euc-ai/xugo/library/registry"
)

// NormalSpaceDef — `normal_space(T)`: two disjoint closed sets lie in
// disjoint open sets. Points need not be closed: normal is not asked to
// imply Hausdorff.
var NormalSpaceDef = normalSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "NormalSpaceDef",
	Key:   "prop_df3e52122fbc68c4",
	Const: "normal_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    normal_space(T) ⇔ " +
			"    ∀s t:set(A). " +
			"        closed_in(T, s) ∧ closed_in(T, t) ∧ s ∩ t = ∅ ⇒ " +
			"        ∃u v:set(A). u ∈ T ∧ v ∈ T ∧ s ⊆ u ∧ t ⊆ v ∧ u ∩ v = ∅",
	},
})}

// T0SpaceDef — `t0_space(T)`: of two distinct points of the space, some
// open set holds exactly one.
var T0SpaceDef = t0SpaceDefThm{family.Define(registry.DefEntry{
	Name:  "T0SpaceDef",
	Key:   "prop_a51d98bb6639d793",
	Const: "t0_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    t0_space(T) ⇔ ∀x y:A. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u:set(A). u ∈ T ∧ ¬(x ∈ u ⇔ y ∈ u)",
	},
})}

// T1SpaceDef — `t1_space(T)`: of two distinct points of the space, each
// has an open neighbourhood missing the other.
var T1SpaceDef = t1SpaceDefThm{family.Define(registry.DefEntry{
	Name:  "T1SpaceDef",
	Key:   "prop_ba1ed872a7af3e96",
	Const: "t1_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). t1_space(T) ⇔ ∀x y:A. x ∈ ⋃T ∧ y ∈ ⋃T ∧ x ≠ y ⇒ ∃u:set(A). u ∈ T ∧ x ∈ u ∧ y ∉ u",
	},
})}

// RegularSpaceDef — `regular_space(T)`: a closed set and a point of the
// space outside it lie in disjoint open sets. Points need not be closed:
// regular is not asked to imply Hausdorff.
var RegularSpaceDef = regularSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "RegularSpaceDef",
	Key:   "prop_56a96b6800a007bb",
	Const: "regular_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    regular_space(T) ⇔ " +
			"    ∀c:set(A). ∀x:A. " +
			"        closed_in(T, c) ∧ x ∈ ⋃T ∧ x ∉ c ⇒ ∃u v:set(A). u ∈ T ∧ v ∈ T ∧ x ∈ u ∧ c ⊆ v ∧ u ∩ v = ∅",
	},
})}
