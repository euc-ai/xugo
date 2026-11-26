// definitions.go — the chapter's definitional layer: a space is
// completely regular when a continuous real function separates a point
// from a closed set not holding it. A property of the space, so the
// topology is its one argument and is spelled.

package real_valued

import (
	"github.com/euc-ai/xugo/library/registry"
)

// CompletelyRegularSpaceDef — `completely_regular_space(T)`: a closed set
// and a point of the space outside it are separated by a continuous
// function into ⟦0, 1⟧, 0 at the point and 1 on the set.
var CompletelyRegularSpaceDef = completelyRegularSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "CompletelyRegularSpaceDef",
	Key:   "prop_2b906dc36795069d",
	Const: "completely_regular_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    completely_regular_space(T) ⇔ " +
			"    ∀c:set(A). ∀x:A. " +
			"        closed_in(T, c) ∧ x ∈ ⋃T ∧ x ∉ c ⇒ " +
			"        ∃f:(A → real). " +
			"            continuous_map(T, real_topology, f) ∧ " +
			"            (∀y:A. y ∈ ⋃T ⇒ &0 ≤ f(y) ∧ f(y) ≤ &1) ∧ " +
			"            f(x) = &0 ∧ " +
			"            (∀y:A. y ∈ c ⇒ f(y) = &1)",
	},
})}
