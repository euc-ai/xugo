// definitions.go — the chapter's definitional layer: a subset of a space
// is compact when every family of open sets covering it has a finite
// subfamily covering it. The topology is the first argument and is
// implicit under a law over it, as it is for `closed_in`.

package compact

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CompactInDef — `compact_in(T, k)`: k lies in the space, and every
// family of open sets covering k has a finite subfamily covering k.
// The topology is implicit under a law over it.
var CompactInDef = compactInDefThm{family.Define(registry.DefEntry{
	Name:     "CompactInDef",
	Key:      "prop_7cbb2005509a97ae",
	Const:    "compact_in",
	Type:     "set(set(A)) → set(A) → bool",
	Implicit: []string{"T"},
	Equations: []string{
		"∀T:set(set(A)). ∀k:set(A). " +
			"    compact_in(T, k) ⇔ " +
			"    k ⊆ ⋃T ∧ ∀c:set(set(A)). c ⊆ T ∧ k ⊆ ⋃c ⇒ ∃d:set(set(A)). d ⊆ c ∧ finite(d) ∧ k ⊆ ⋃d",
	},
})}

// LocallyCompactSpaceDef — `locally_compact_space(T)`: every point of the
// space has an open neighbourhood inside a compact set. A property of the
// space, so the topology is its one argument and is spelled.
var LocallyCompactSpaceDef = locallyCompactSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "LocallyCompactSpaceDef",
	Key:   "prop_21f29bb6bce4e584",
	Const: "locally_compact_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    locally_compact_space(T) ⇔ " +
			"    ∀x:A. x ∈ ⋃T ⇒ ∃u k:set(A). u ∈ T ∧ compact_in(T, k) ∧ x ∈ u ∧ u ⊆ k",
	},
	Deps: []registry.EntryLike{CompactInDef},
})}
