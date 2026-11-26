// A finite homogeneous basis indexes the degreewise Künneth comparison.

package de_rham_kunneth

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/registry"
)

var HomogeneousBasisDef = homogeneousBasisDefThm{family.Define(registry.DefEntry{
	Name:  "HomogeneousBasisDef",
	Key:   "prop_c874ccec97840b72",
	Const: "de_rham_homogeneous_basis",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(prod(num, set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))) → " +
		"bool",
	Dimensions: []string{"n"},
	Reading: "Each element is a pair of a degree and a class of whole " +
		"forms. The degree fibres are bases, and their union E is finite; " +
		"tagging prevents classes in different degrees from being identified.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))). " +
			"    de_rham_homogeneous_basis⟨n⟩(T, 𝒜, E) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    finite(E) ∧ " +
			"    (∀e:prod(num, " +
			"            set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"        e ∈ E ⇒ snd(e) ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, fst(e)).carrier) ∧ " +
			"    (∀q:num. " +
			"        module_basis(real_ring, " +
			"            de_rham_cohomology_module⟨n⟩(T, 𝒜, q), " +
			"            {s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) | " +
			"                (q, s) ∈ E}))",
	},
})}

var KunnethCoefficientModuleDef = kunnethCoefficientModuleDefThm{family.Define(registry.DefEntry{
	Name:  "KunnethCoefficientModuleDef",
	Key:   "prop_2bb990ecfdbd99e5",
	Const: "de_rham_kunneth_module",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))) → " +
		"module_ops(real, " +
		"    prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)) → " +
		"    set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real))",
	Dimensions: []string{"n"},
	Reading: "The same index set E is used in every total degree. A label of degree d>k " +
		"has the singleton zero module cut out of H^0, so natural subtraction never substitutes " +
		"H^0 for a negative-degree summand. Finite E makes this product the finite direct sum.",
	Deps: []registry.EntryLike{},
	Equations: []string{
		"∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))). " +
			"    de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E) = " +
			"    indexed_product_module(E, " +
			"        (λe:prod(num, " +
			"                set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)). " +
			"            COND(fst(e) ≤ k, " +
			"                de_rham_cohomology_module⟨n⟩(T, 𝒜, k - fst(e)), " +
			"                restrict_module(de_rham_cohomology_module⟨n⟩(T, 𝒜, 0), " +
			"                    {de_rham_cohomology_module⟨n⟩(T, 𝒜, 0).zero}))))",
	},
})}

var KunnethMapDef = kunnethMapDefThm{family.Define(registry.DefEntry{
	Name:  "KunnethMapDef",
	Key:   "prop_d0804dafda1fd516",
	Const: "de_rham_kunneth_map",
	Type: "num → " +
		"num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(set(B)) → " +
		"set(prod(set(B), B → num → real)) → " +
		"num → " +
		"set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))) → " +
		"(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)) → " +
		"    set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)) → " +
		"set(prod(set(prod(A, B)), prod(A, B) → num → real) → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n", "m"},
	Reading: "The comparison sends coefficients to the finite sum of their " +
		"external products with the tagged classes. Its laws require finite E and " +
		"valid classes. Labels above the total degree contribute the target zero.",
	Deps: []registry.EntryLike{KunnethCoefficientModuleDef},
	Equations: []string{
		"∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀a:(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)) → " +
			"        set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"    de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E)(a) = " +
			"    module_sum(de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            k).add, " +
			"        de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"            smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"            k).zero, " +
			"        E, " +
			"        (λe:prod(num, " +
			"                set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)). " +
			"            COND(fst(e) ≤ k, " +
			"                de_rham_external_product⟨n, m⟩(T, 𝒜, S, ℬ, k - fst(e), fst(e), a(e), snd(e)), " +
			"                de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"                    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"                    k).zero)))",
	},
})}
