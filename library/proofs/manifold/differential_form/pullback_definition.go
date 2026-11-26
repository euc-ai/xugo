// Pullback chooses a target chart separately at each source coordinate
// point, and normalizes at both the chart and coordinate-domain levels.

package differential_form

import "github.com/euc-ai/xugo/library/registry"

// PullbackDef — pointwise coordinate pullback through a chosen target chart.
var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_c62c15a670025b6b",
	Const: "manifold_form_pullback",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"(A → B) → " +
		"(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Reading: "The target chart depends on the coordinate point y, not just on the source " +
		"chart. Inside the Jacobian at y that chosen chart is held fixed as the coordinate-map " +
		"argument; it is not differentiated as a function of y. PullbackCoordinate replaces the " +
		"choice by any fixed target chart on an appropriate open source region.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω, c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c), " +
			"        vec_form_pullback⟨n, m⟩(«chart image»(c), " +
			"            k, " +
			"            «coordinate map»(c, «target chart», f), " +
			"            ω(«target chart»), " +
			"            y, " +
			"            P), " +
			"        &0)",
	},
})}
