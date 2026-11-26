package de_rham_comparison

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ComparisonDef = comparisonDefThm{family.Define(registry.DefEntry{
	Name:  "ComparisonDef",
	Key:   "prop_1b29db0cf45e2a2b",
	Const: "de_rham_comparison",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(((num → real) → A) → real)",
	Dimensions: []string{"n"},
	Reading: "The map goes from de Rham to continuous singular cohomology, " +
		"using the inverse of the continuous-to-smooth restriction. Its geometric " +
		"properties are asserted where both intermediate comparison maps are " +
		"isomorphisms. No simplex smoothing or arbitrary extension of a form is used.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_comparison⟨n⟩(T, 𝒜, k)(s) = " +
			"    inverse_on(cohomology_module(singular_cochain_complex(T), k).carrier, " +
			"        singular_cohomology_restriction(smooth_singular_set⟨n⟩(T, 𝒜), k), " +
			"        de_rham_integration_class⟨n⟩(T, 𝒜, k)(s))",
	},
})}
