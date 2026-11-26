package compact_de_rham

import (
	"github.com/euc-ai/xugo/library/registry"
)

var ComplexDef = complexDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexDef",
	Key:   "prop_63813c731b90f547",
	Const: "compact_de_rham_complex",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"complex_ops(real, prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). " +
			"    compact_de_rham_complex(n, T, 𝒜) = " +
			"    pack_complex((manifold_form_module⟨n⟩(T, 𝒜, 0)).add, " +
			"        (manifold_form_module⟨n⟩(T, 𝒜, 0)).zero, " +
			"        (manifold_form_module⟨n⟩(T, 𝒜, 0)).neg, " +
			"        (manifold_form_module⟨n⟩(T, 𝒜, 0)).smul, " +
			"        λk:num. " +
			"            {ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) | " +
			"                manifold_form_on⟨n⟩(T, 𝒜, k, ω) ∧ " +
			"                compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))}, " +
			"        λk:num. manifold_exterior_derivative⟨n⟩(T, 𝒜, k))",
	},
})}

var ModuleDef = moduleDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleDef",
	Key:   "prop_f1cde5a8e261360f",
	Deps:  []registry.EntryLike{ComplexDef},
	Const: "compact_de_rham_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"module_ops(real, set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀k:num. " +
			"    compact_de_rham_module(n, T, 𝒜, k) = cohomology_module(compact_de_rham_complex(n, T, 𝒜), k)",
	},
})}

var ClassDef = classDefThm{family.Define(registry.DefEntry{
	Name:  "ClassDef",
	Key:   "prop_fc92f4c5cf5de4c5",
	Deps:  []registry.EntryLike{ComplexDef},
	Const: "compact_de_rham_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_class(n, T, 𝒜, k, ω) = " +
			"    left_coset((compact_de_rham_complex(n, T, 𝒜)).add, " +
			"        ω, " +
			"        coboundaries(compact_de_rham_complex(n, T, 𝒜), k))",
	},
})}

var ProductDef = productDefThm{family.Define(registry.DefEntry{
	Name:  "ProductDef",
	Key:   "prop_fbdc3a203986f954",
	Deps:  []registry.EntryLike{ClassDef},
	Const: "compact_de_rham_product",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p q:num. " +
			"∀a b:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_product(n, T, 𝒜, p, q, a, b) = " +
			"    induced_map(λα:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            induced_map(λβ:(prod(set(A), A → num → real) → " +
			"                        (num → real) → " +
			"                        (num → num → real) → " +
			"                        real). " +
			"                    compact_de_rham_class(n, " +
			"                        T, " +
			"                        𝒜, " +
			"                        p + q, " +
			"                        manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β)), " +
			"                b), " +
			"        a)",
	},
})}

var PullbackDef = pullbackDefThm{family.Define(registry.DefEntry{
	Name:  "PullbackDef",
	Key:   "prop_9ee4f3a7964b2a58",
	Deps:  []registry.EntryLike{ClassDef},
	Const: "compact_de_rham_pullback",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"(A → B) → " +
		"num → " +
		"set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀m:num. " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀k:num. " +
			"∀a:set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_pullback(n, T, 𝒜, m, S, ℬ, f, k, a) = " +
			"    induced_map(λω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real). " +
			"            compact_de_rham_class(n, " +
			"                T, " +
			"                𝒜, " +
			"                k, " +
			"                manifold_form_pullback⟨n, m⟩(T, 𝒜, S, ℬ, k, f, ω)), " +
			"        a)",
	},
})}

var ExtensionDef = extensionDefThm{family.Define(registry.DefEntry{
	Name:  "ExtensionDef",
	Key:   "prop_52d53a50bb7e32f7",
	Deps:  []registry.EntryLike{ClassDef},
	Const: "compact_de_rham_extension",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀U:set(A). " +
			"∀k:num. " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_extension(n, T, 𝒜, U, k, a) = " +
			"    induced_map(λω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            compact_de_rham_class(n, T, 𝒜, k, manifold_form_extend_zero⟨n⟩(T, 𝒜, U, ω)), " +
			"        a)",
	},
})}

var IntegralDef = integralDefThm{family.Define(registry.DefEntry{
	Name:  "IntegralDef",
	Key:   "prop_54a9bccc1e39c32e",
	Const: "compact_de_rham_integral",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    compact_de_rham_integral(n, T, 𝒜, a) = induced_map(manifold_form_integral⟨n⟩(T, 𝒜), a)",
	},
})}
