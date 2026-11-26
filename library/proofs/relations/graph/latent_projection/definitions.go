// definitions.go — the latent projection of a DAG onto its observed
// vertices.

package latent_projection

import (
	"github.com/euc-ai/xugo/library/registry"
)

// LatentReachDef — `latent_reach(E, O, u, v)`: v is reached from u along
// a directed path of at least one edge whose interior lies outside O.
var LatentReachDef = latentReachDefThm{family.Define(registry.DefEntry{
	Name:  "LatentReachDef",
	Key:   "prop_8b147e05a4dd1ccb",
	Const: "latent_reach",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Equations: []string{
		"∀E:(A → A → bool). ∀O:set(A). ∀u v:A. " +
			"    latent_reach(E, O, u, v) ⇔ " +
			"    E(u, v) ∨ " +
			"    (∃l l':A. " +
			"        l ∉ O ∧ E(u, l) ∧ reflexive_transitive_closure(relation_on(𝕌 ∖ O, E), l, l') ∧ E(l', v))",
	},
})}

// LatentDirectedDef — the directed edges of the latent projection of E
// onto O: a → b between observed vertices when b is reached from a
// through unobserved vertices only.
var LatentDirectedDef = latentDirectedDefThm{family.Define(registry.DefEntry{
	Name:  "LatentDirectedDef",
	Key:   "prop_b251e47d331e08be",
	Const: "latent_proj_directed",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Deps:  []registry.EntryLike{LatentReachDef},
	Equations: []string{
		"∀E:(A → A → bool). ∀O:set(A). ∀a b:A. " +
			"    latent_proj_directed(E, O, a, b) ⇔ a ∈ O ∧ b ∈ O ∧ latent_reach(E, O, a, b)",
	},
})}

// LatentBidirectedDef — the bidirected edges of the latent projection of
// E onto O: a ↔ b between distinct observed vertices with an unobserved
// common cause reaching both through unobserved vertices only.
var LatentBidirectedDef = latentBidirectedDefThm{family.Define(registry.DefEntry{
	Name:  "LatentBidirectedDef",
	Key:   "prop_dc67c4d1dd520b9",
	Const: "latent_proj_bidirected",
	Type:  "(A → A → bool) → set(A) → A → A → bool",
	Deps:  []registry.EntryLike{LatentReachDef},
	Equations: []string{
		"∀E:(A → A → bool). ∀O:set(A). ∀a b:A. " +
			"    latent_proj_bidirected(E, O, a, b) ⇔ " +
			"    a ∈ O ∧ b ∈ O ∧ a ≠ b ∧ (∃l:A. l ∉ O ∧ latent_reach(E, O, l, a) ∧ latent_reach(E, O, l, b))",
	},
})}
