package borel_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

// BorelSetsDef — The smallest sigma algebra on the space containing its open sets.
var BorelSetsDef = borelSetsDefThm{family.Define(registry.DefEntry{
	Name:  "BorelSetsDef",
	Key:   "prop_e02de2a257b724d0",
	Const: "borel_sets",
	Type:  "set(set(A)) → set(set(A))",
	Equations: []string{
		"∀T:set(set(A)). borel_sets(T) = ⋂{S:set(set(A)) | sigma_algebra_on(⋃T, S) ∧ T ⊆ S}",
	},
	Reading: "The smallest sigma algebra on the space containing its open sets.",
})}

// BorelMapDef — Only the values of f on the source carrier enter measurability.
var BorelMapDef = borelMapDefThm{family.Define(registry.DefEntry{
	Name:  "BorelMapDef",
	Key:   "prop_57e70d0463361c8f",
	Const: "borel_map",
	Type:  "set(set(A)) → set(set(B)) → (A → B) → bool",
	Equations: []string{
		"∀T:set(set(A)). ∀U:set(set(B)). ∀f:(A → B). " +
			"    borel_map(T, U, f) ⇔ " +
			"    is_topology(T) ∧ is_topology(U) ∧ measurable_map(⋃T, borel_sets(T), ⋃U, borel_sets(U), f)",
	},
	Deps:    []registry.EntryLike{BorelSetsDef},
	Reading: "Only the values of f on the source carrier enter measurability.",
})}
