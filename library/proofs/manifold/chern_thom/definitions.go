package chern_thom

import (
	"github.com/euc-ai/xugo/library/registry"
)

var DualDef = dualDefThm{family.Define(registry.DefEntry{
	Name:  "DualDef",
	Key:   "prop_dc602c9baf6a4e1d",
	Const: "projection_dual",
	Type:  "prod(num, A → num → num → complex) → prod(num, A → num → num → complex)",
	Equations: []string{
		"∀P:prod(num, A → num → num → complex). " +
			"    projection_dual(P) = (fst(P), λx:A. λi:num. λj:num. complex_conj(snd(P)(x, i, j)))",
	},
})}

var InverseToddDef = inverseToddDefThm{family.Define(registry.DefEntry{
	Name:  "InverseToddDef",
	Key:   "prop_219303893f14c111",
	Const: "inverse_todd_class",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"    inverse_todd_class(n, T, 𝒜, P) = " +
			"    εb:(num → set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"        (∀k:num. b(k) ∈ (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).carrier) ∧ " +
			"        (∀k:num. " +
			"            module_sum((de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).add, " +
			"                (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero, " +
			"                {j:num | j ≤ k}, " +
			"                λj:num. " +
			"                    de_rham_wedge⟨n⟩(T, " +
			"                        𝒜, " +
			"                        2 * j, " +
			"                        2 * (k - j), " +
			"                        todd_class(n, T, 𝒜, P, j), " +
			"                        b(k - j))) = " +
			"            COND(k = 0, " +
			"                de_rham_class⟨n⟩(T, 𝒜, 0, manifold_form_unit⟨n⟩(T, 𝒜)), " +
			"                (de_rham_cohomology_module⟨n⟩(T, 𝒜, 2 * (k))).zero))",
	},
})}

var correctedCharacterDef = correctedCharacterDefThm{family.Define(registry.DefEntry{
	Name:  "correctedCharacterDef",
	Key:   "prop_fbb4d59597ca67fd",
	Deps:  []registry.EntryLike{DualDef, InverseToddDef},
	Const: "thom_corrected_character",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"prod(num, A → num → num → complex) → " +
		"set(prod(prod(num, A → num → num → complex), " +
		"        prod(prod(num, A → num → num → complex), A → num → num → complex))) → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀a:set(prod(prod(num, A → num → num → complex), " +
			"            prod(prod(num, A → num → num → complex), A → num → num → complex))). " +
			"∀k:num. " +
			"    thom_corrected_character(n, T, 𝒜, P, a, k) = " +
			"    module_sum((compact_de_rham_module(n, T, 𝒜, 2 * k)).add, " +
			"        (compact_de_rham_module(n, T, 𝒜, 2 * k)).zero, " +
			"        {j:num | j ≤ k}, " +
			"        λj:num. " +
			"            compact_de_rham_product(n, " +
			"                T, " +
			"                𝒜, " +
			"                2 * j, " +
			"                2 * (k - j), " +
			"                compact_chern_class(n, T, 𝒜, a, j), " +
			"                inverse_todd_class(n, T, 𝒜, projection_dual(P), k - j)))",
	},
})}
