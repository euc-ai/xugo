// Pullback on cohomology is induced by the degreewise pullback of forms.

package de_rham

import (
	"github.com/euc-ai/xugo/library/registry"
)

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_91bb523fa4e3570a",
	Const: "de_rham_pullback",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"(A → B) → " +
		"set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Deps: []registry.EntryLike{ComplexDef},
	Reading: "Pullback is contravariant: a map from the n-dimensional " +
		"source to the m-dimensional target sends target cohomology to source " +
		"cohomology. Functor laws are asserted on actual cohomology classes.",
	Dimensions: []string{"n", "m"},
	Equations: []string{
		"∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num. " +
			"∀f:(A → B). " +
			"∀s:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f)(s) = " +
			"    cohomology_map(de_rham_complex⟨n⟩(T, 𝒜), " +
			"        λq:num. manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, q, f), " +
			"        k, " +
			"        s)",
	},
})}
