// definitions.go — the chapter's definitional layer: the four ways a
// space can be small in the countable sense — a countable base, a
// countable base at each point, a countable dense set, and a countable
// subcover of every open cover. Each is a property of the space, so the
// topology is its one argument and is spelled.

package countability

import (
	"github.com/euc-ai/xugo/library/registry"
)

// SecondCountableSpaceDef — `second_countable_space(T)`: the topology has
// a countable base.
var SecondCountableSpaceDef = secondCountableSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "SecondCountableSpaceDef",
	Key:   "prop_c8604d5880d6e6b2",
	Const: "second_countable_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). second_countable_space(T) ⇔ ∃b:set(set(A)). countable(b) ∧ topology_base(T, b)",
	},
})}

// FirstCountableSpaceDef — `first_countable_space(T)`: each point of the
// space has countably many open sets among which every open neighbourhood
// of the point holds one that holds the point.
var FirstCountableSpaceDef = firstCountableSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "FirstCountableSpaceDef",
	Key:   "prop_1e4c1805a6695e85",
	Const: "first_countable_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    first_countable_space(T) ⇔ " +
			"    ∀x:A. " +
			"        x ∈ ⋃T ⇒ " +
			"        ∃b:set(set(A)). " +
			"            countable(b) ∧ b ⊆ T ∧ ∀u:set(A). u ∈ T ∧ x ∈ u ⇒ ∃v:set(A). v ∈ b ∧ x ∈ v ∧ v ⊆ u",
	},
})}

// SeparableSpaceDef — `separable_space(T)`: a countable set of points of
// the space is dense, its closure the whole space.
var SeparableSpaceDef = separableSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "SeparableSpaceDef",
	Key:   "prop_cd4e706e3ff959f0",
	Const: "separable_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). separable_space(T) ⇔ ∃c:set(A). countable(c) ∧ c ⊆ ⋃T ∧ closure(T, c) = ⋃T",
	},
})}

// LindelofSpaceDef — `lindelof_space(T)`: every family of open sets
// covering the space has a countable subfamily covering it — compactness
// of the space with countable for finite.
var LindelofSpaceDef = lindelofSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "LindelofSpaceDef",
	Key:   "prop_455afd01b6d0995e",
	Const: "lindelof_space",
	Type:  "set(set(A)) → bool",
	Equations: []string{
		"∀T:set(set(A)). " +
			"    lindelof_space(T) ⇔ " +
			"    ∀c:set(set(A)). c ⊆ T ∧ ⋃T ⊆ ⋃c ⇒ ∃d:set(set(A)). d ⊆ c ∧ countable(d) ∧ ⋃T ⊆ ⋃d",
	},
})}
