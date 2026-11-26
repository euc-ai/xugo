package de_rham_thom

import (
	"github.com/euc-ai/xugo/library/registry"
)

var thomFormDef = thomFormDefThm{family.Define(registry.DefEntry{
	Name:  "thomFormDef",
	Key:   "prop_4bdabe1e58c72db7",
	Const: "projection_thom_form",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"    projection_thom_form(n, r, T, 𝒜, P) = " +
			"    ετ:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"            (num → real) → " +
			"            (num → num → real) → " +
			"            real). " +
			"        manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"            projection_total_atlas(n, r, T, 𝒜, P), " +
			"            2 * r, " +
			"            τ) ∧ " +
			"        projection_fiber_proper(n, r, T, 𝒜, P, τ) ∧ " +
			"        manifold_exterior_derivative⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"            projection_total_atlas(n, r, T, 𝒜, P), " +
			"            2 * r, " +
			"            τ) = " +
			"        (λc:prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real). " +
			"        λy:(num → real). " +
			"        λV:(num → num → real). " +
			"            &0) ∧ " +
			"        projection_fiber_integral(n, r, T, 𝒜, P, 0, τ) = manifold_form_unit⟨n⟩(T, 𝒜)",
	},
})}

var ThomMapDef = thomMapDefThm{family.Define(registry.DefEntry{
	Name:  "ThomMapDef",
	Key:   "prop_572d8aca4b7c9b9f",
	Deps:  []registry.EntryLike{thomFormDef},
	Const: "compact_de_rham_thom",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_thom(n, r, T, 𝒜, P, k, a) = " +
			"    induced_map(λω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            compact_de_rham_class(n + 2 * r, " +
			"                projection_total_topology(T, P), " +
			"                projection_total_atlas(n, r, T, 𝒜, P), " +
			"                k + 2 * r, " +
			"                manifold_form_wedge⟨n + 2 * r⟩(projection_total_topology(T, P), " +
			"                    projection_total_atlas(n, r, T, 𝒜, P), " +
			"                    k, " +
			"                    2 * r, " +
			"                    manifold_form_pullback⟨n + 2 * r, n⟩(projection_total_topology(T, P), " +
			"                        projection_total_atlas(n, r, T, 𝒜, P), " +
			"                        T, " +
			"                        𝒜, " +
			"                        k, " +
			"                        λp:prod(A, num → complex). fst(p), " +
			"                        ω), " +
			"                    projection_thom_form(n, r, T, 𝒜, P))), " +
			"        a)",
	},
})}

var fiberMapDef = fiberMapDefThm{family.Define(registry.DefEntry{
	Name:  "fiberMapDef",
	Key:   "prop_27aac8cc7da0fa5d",
	Const: "compact_de_rham_fiber",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
		"    (num → real) → " +
		"    (num → num → real) → " +
		"    real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀a:set(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"    compact_de_rham_fiber(n, r, T, 𝒜, P, k, a) = " +
			"    induced_map(λω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"                (num → real) → " +
			"                (num → num → real) → " +
			"                real). " +
			"            compact_de_rham_class(n, T, 𝒜, k, projection_fiber_integral(n, r, T, 𝒜, P, k, ω)), " +
			"        a)",
	},
})}
