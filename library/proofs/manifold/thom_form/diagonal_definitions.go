package thom_form

import (
	"github.com/euc-ai/xugo/library/registry"
)

var DiagonalFormDef = diagonalFormDefThm{family.Define(registry.DefEntry{
	Name:  "DiagonalFormDef",
	Key:   "prop_a3e715995c6b71d2",
	Const: "manifold_diagonal_form",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dimensions: []string{"n"},
	Reading: "Support lies inside an open neighbourhood W where the two projection pullbacks " +
		"agree in every degree. Because the support is closed and lies in W, a primitive on W " +
		"multiplied by η extends by zero to M × M; compactness of M is what the fiber-integral laws " +
		"ask of the fiber. The reproducing conclusion is not a defining condition.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀η:(prod(set(prod(A, A)), prod(A, A) → num → real) → (num → real) → (num → num → real) → real). " +
			"    manifold_diagonal_form⟨n⟩(T, 𝒜, η) ⇔ " +
			"    oriented_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    compact_in(T, ⋃T) ∧ " +
			"    η ∈ " +
			"    cocycles(de_rham_complex⟨2 * n⟩(product_topology(T, T), smooth_product_atlas⟨n, n⟩(𝒜, 𝒜)), " +
			"        n) ∧ " +
			"    manifold_fiber_integral⟨n, n⟩(T, 𝒜, T, 𝒜, 0, η) = manifold_form_unit⟨n⟩(T, 𝒜) ∧ " +
			"    (∃W:set(prod(A, A)). " +
			"        W ∈ product_topology(T, T) ∧ " +
			"        manifold_form_support⟨2 * n⟩(product_topology(T, T), " +
			"            smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"            η) ⊆ " +
			"        W ∧ " +
			"        (∀k:num. " +
			"        ∀s:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, k).carrier ⇒ " +
			"            de_rham_pullback⟨2 * n, n⟩(subtopology(product_topology(T, T), W), " +
			"                open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), " +
			"                    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"                    W), " +
			"                T, " +
			"                𝒜, " +
			"                k, " +
			"                fst)(s) = " +
			"            de_rham_pullback⟨2 * n, n⟩(subtopology(product_topology(T, T), W), " +
			"                open_submanifold_atlas⟨2 * n⟩(product_topology(T, T), " +
			"                    smooth_product_atlas⟨n, n⟩(𝒜, 𝒜), " +
			"                    W), " +
			"                T, " +
			"                𝒜, " +
			"                k, " +
			"                snd)(s)))",
	},
})}

var pairingDef = pairingDefThm{family.Define(registry.DefEntry{
	Name:  "pairingDef",
	Key:   "prop_e411b4d12668d537",
	Const: "de_rham_integral_pairing",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real",
	Dimensions: []string{"n"},
	Reading: "Both arguments are zeroed outside their cohomology carriers. Representatives " +
		"are chosen among cocycles, and Stokes makes the value independent of these choices.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p q:num. " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_integral_pairing⟨n⟩(T, 𝒜, p, q, s, t) = " +
			"    COND(p + q = n ∧ " +
			"        s ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, p).carrier ∧ " +
			"        t ∈ de_rham_cohomology_module⟨n⟩(T, 𝒜, q).carrier, " +
			"        manifold_form_integral⟨n⟩(T, " +
			"            𝒜, " +
			"            manifold_form_wedge⟨n⟩(T, " +
			"                𝒜, " +
			"                p, " +
			"                q, " +
			"                (εα:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"                    α ∈ s ∧ α ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), p)), " +
			"                (εβ:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"                    β ∈ t ∧ β ∈ cocycles(de_rham_complex⟨n⟩(T, 𝒜), q)))), " +
			"        &0)",
	},
})}

var DualityMapDef = dualityMapDefThm{family.Define(registry.DefEntry{
	Name:  "DualityMapDef",
	Key:   "prop_2c21a49012716b63",
	Const: "de_rham_duality_map",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"num → " +
		"num → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real) → " +
		"real",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{pairingDef},
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p q:num. " +
			"∀s t:set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"    de_rham_duality_map⟨n⟩(T, 𝒜, p, q, s, t) = de_rham_integral_pairing⟨n⟩(T, 𝒜, p, q, s, t)",
	},
})}
