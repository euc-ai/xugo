// The de Rham cochain complex and its coset-valued cohomology reuse the general complex machinery.

package de_rham

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ComplexDef = complexDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexDef",
	Key:   "prop_be1486d08fea2b6d",
	Const: "de_rham_complex",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"complex_ops(real, prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim: "n",
	Reading: "All degrees share the normalized manifold-form host type and pointwise " +
		"real operations. The degree-k carrier consists of k-forms and d(k) is their exterior " +
		"derivative. This is a nonnegative cochain complex, so degree-zero coboundaries come " +
		"from the generic zero submodule, not from a truncated negative degree.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    de_rham_complex⟨n⟩(T, 𝒜) = " +
			"    pack_complex(λα:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        λβ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        λc:prod(set(A), A → num → real). " +
			"        λy:(num → real). " +
			"        λP:(num → num → real). " +
			"            α(c, y, P) + β(c, y, P), " +
			"        «zero family», " +
			"        λα:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        λc:prod(set(A), A → num → real). " +
			"        λy:(num → real). " +
			"        λP:(num → num → real). " +
			"            -α(c, y, P), " +
			"        λa:real. " +
			"        λα:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"        λc:prod(set(A), A → num → real). " +
			"        λy:(num → real). " +
			"        λP:(num → num → real). " +
			"            a * α(c, y, P), " +
			"        λk:num. " +
			"            {ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) | " +
			"                manifold_form_on⟨n⟩(T, 𝒜, k, ω)}, " +
			"        λk:num. manifold_exterior_derivative⟨n⟩(T, 𝒜, k))",
	},
})}

var CohomologyModuleDef = cohomologyModuleDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyModuleDef",
	Key:   "prop_c0e268b74e596982",
	Const: "de_rham_cohomology_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"module_ops(real, set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))",
	Dim:  "n",
	Deps: []registry.EntryLike{ComplexDef},
	Reading: "Cohomology is the existing quotient module of cocycles by " +
		"coboundaries. Its elements are sets of whole normalized forms, represented by " +
		"cosets; total functions on other sets are not automatically maps on cohomology.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    de_rham_cohomology_module⟨n⟩(T, 𝒜, k) = cohomology_module(de_rham_complex⟨n⟩(T, 𝒜), k)",
	},
})}

var ClassDef = classDefThm{family.Define(registry.DefEntry{
	Name:  "ClassDef",
	Key:   "prop_e1fba29a2b60328d",
	Const: "de_rham_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Dim:  "n",
	Deps: []registry.EntryLike{ComplexDef},
	Reading: "The coset expression is defined for any host form, but " +
		"it is a cohomology class only when the form lies in the degree " +
		"carrier and is closed. Its zero class is the set of coboundaries.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_class⟨n⟩(T, 𝒜, k, ω) = " +
			"    left_coset(de_rham_complex⟨n⟩(T, 𝒜).add, ω, coboundaries(de_rham_complex⟨n⟩(T, 𝒜), k))",
	},
})}
