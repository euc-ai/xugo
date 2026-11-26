// A manifold form is a normalized family of Euclidean forms whose
// expressions agree by pullback on every compatible-chart overlap.

package differential_form

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/registry"
)

// FormOnDef — normalized compatible coordinate expressions of degree k.
var FormOnDef = formOnDefThm{family.Define(registry.DefEntry{
	Name:  "FormOnDef",
	Key:   "prop_5c5d5bb06c1f35d2",
	Const: "manifold_form_on",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dim: "n",
	Reading: "The ambient dimension n and degree k are separate. Compatible charts " +
		"carry Euclidean forms normalized outside their coordinate images; every incompatible " +
		"chart carries the zero form. Overlap compatibility uses normalized restriction, so " +
		"the equations hold as total functions, including arbitrary matrix tails.",
	Equations: []string{
		"∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, ω) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ⇒ vec_form_on⟨n⟩(«chart image»(c), k, ω(c))) ∧ " +
			"    (∀c:prod(set(A), A → num → real). ¬compatible_chart⟨n⟩(T, 𝒜, c) ⇒ ω(c) = «zero») ∧ " +
			"    (∀c d:prod(set(A), A → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ∧ compatible_chart⟨n⟩(T, 𝒜, d) ⇒ " +
			"        normalize_on(«overlap»(c, d), λP:(num → num → real). &0, ω(c)) = " +
			"        vec_form_pullback⟨n, n⟩(«overlap»(c, d), k, «transition»(c, d), ω(d)))",
	},
})}

// FormModuleDef — the degree carrier with pointwise real module operations.
var FormModuleDef = formModuleDefThm{family.Define(registry.DefEntry{
	Name:  "FormModuleDef",
	Key:   "prop_fa331d5c3034827e",
	Const: "manifold_form_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"module_ops(real, prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{FormOnDef},
	Equations: []string{
		"∀n k:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    manifold_form_module⟨n⟩(T, 𝒜, k) = " +
			"    restrict_module(function_module(function_module( " +
			"                function_module(regular_module(real_ring), 𝕌⟨A:num → num → real⟩), " +
			"                𝕌⟨A:num → real⟩), " +
			"            𝕌⟨A:prod(set(A), A → num → real)⟩), " +
			"        {ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) | " +
			"            manifold_form_on⟨n⟩(T, 𝒜, k, ω)})",
	},
})}

// WedgeDef — the Euclidean wedge on each compatible chart, zero elsewhere.
var WedgeDef = wedgeDefThm{family.Define(registry.DefEntry{
	Name:  "WedgeDef",
	Key:   "prop_6f7e284b3b1785d8",
	Const: "manifold_form_wedge",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Equations: []string{
		"∀n p q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"    manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β, c) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c), " +
			"        vec_form_wedge⟨n⟩(«chart image»(c), p, q, α(c), β(c)), " +
			"        «zero»)",
	},
})}

// ExteriorDerivativeDef — the coordinate exterior derivative, raising k to k+1.
var ExteriorDerivativeDef = exteriorDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "ExteriorDerivativeDef",
	Key:   "prop_d8f5e22c194bd95f",
	Const: "manifold_exterior_derivative",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Equations: []string{
		"∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"    manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω, c) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c), " +
			"        vec_exterior_derivative⟨n⟩(«chart image»(c), k, ω(c)), " +
			"        «zero»)",
	},
})}

// UnitDef — the normalized constant-one zero-form in every compatible chart.
var UnitDef = unitDefThm{family.Define(registry.DefEntry{
	Name:  "UnitDef",
	Key:   "prop_aade04ad0d81a501",
	Const: "manifold_form_unit",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Reading: "The unit is zero on incompatible charts and outside coordinate images. On " +
		"the empty manifold it is the zero family, as required for the trivial form algebra.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀y:(num → real). " +
			"∀P:(num → num → real). " +
			"    manifold_form_unit⟨n⟩(T, 𝒜, c, y, P) = " +
			"    COND(compatible_chart⟨n⟩(T, 𝒜, c) ∧ y ∈ «chart image»(c), &1, &0)",
	},
})}

// RestrictDef — retain exactly the compatible charts lying in the open subset.
var RestrictDef = restrictDefThm{family.Define(registry.DefEntry{
	Name:  "RestrictDef",
	Key:   "prop_fd9823a824f3a8db",
	Const: "manifold_form_restrict",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"prod(set(A), A → num → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim: "n",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_form_restrict⟨n⟩(T, 𝒜, U, ω) = " +
			"    normalize_on(open_submanifold_atlas⟨n⟩(T, 𝒜, U), «zero», ω)",
	},
})}
