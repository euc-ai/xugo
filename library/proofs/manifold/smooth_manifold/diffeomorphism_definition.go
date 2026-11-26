// A smooth diffeomorphism has a smooth inverse on its target carrier.

package smooth_manifold

import (
	"github.com/euc-ai/xugo/library/registry"
)

var DiffeomorphismDef = diffeomorphismDefThm{family.Define(registry.DefEntry{
	Name:  "DiffeomorphismDef",
	Key:   "prop_d155fcb24d5c7ea2",
	Const: "smooth_manifold_diffeomorphism",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"bool",
	Dimensions: []string{"n"},
	Reading: "Source and target have the same displayed dimension. The " +
		"inverse is the total inverse_on function, whose values are specified " +
		"only on the target carrier; no orientation is part of this predicate.",
	Deps: []registry.EntryLike{SmoothMapDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"    smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f) ⇔ " +
			"    smooth_manifold_map⟨n, n⟩(T, 𝒜, S, ℬ, f) ∧ " +
			"    homeomorphic_map(T, S, f) ∧ " +
			"    smooth_manifold_map⟨n, n⟩(S, ℬ, T, 𝒜, inverse_on(⋃T, f))",
	},
})}
