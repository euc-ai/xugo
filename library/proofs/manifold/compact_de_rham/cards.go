package compact_de_rham

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/form_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var Complex = complexThm{family.Add(registry.ProofEntry{
	Name: "Complex",
	Key:  "prop_f500797a70b206be",
	Deps: []registry.EntryLike{de_rham.Complex},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)"},
		Conclusion: "cochain_complex(real_ring, compact_de_rham_complex(n, T, 𝒜))",
	},
		"Exterior differentiation does not enlarge base support. The compact form "+
			"carriers are submodules, so the ordinary de Rham identities restrict."),
})}

var ClassCarrier = classCarrierThm{family.Add(registry.ProofEntry{
	Name: "ClassCarrier",
	Key:  "prop_5167f3b11d86894e",
	Deps: []registry.EntryLike{Complex},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, k, ω) = " +
				"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
		},
		Conclusion: "compact_de_rham_class(n, T, 𝒜, k, ω) ∈ (compact_de_rham_module(n, T, 𝒜, k)).carrier",
	}, "A compact closed form is a cocycle of the compact-support complex."),
})}

var ClassEquality = classEqualityThm{family.Add(registry.ProofEntry{
	Name: "ClassEquality",
	Key:  "prop_2af125e2867fdb93",
	Deps: []registry.EntryLike{Complex},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀k:num. " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
		},
		Conclusion: "compact_de_rham_class(n, T, 𝒜, k, α) = compact_de_rham_class(n, T, 𝒜, k, β) ⇔ " +
			"(COND(k = 0, " +
			"        α = β, " +
			"        ∃η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"            manifold_form_on⟨n⟩(T, 𝒜, k - 1, η) ∧ " +
			"            compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, η)) ∧ " +
			"            (manifold_form_module⟨n⟩(T, 𝒜, 0)).add(β, " +
			"                manifold_exterior_derivative⟨n⟩(T, 𝒜, k - 1, η)) = " +
			"            α))",
	},
		"Equality means an exact difference with a compact "+
			"primitive; degree zero has only the zero coboundary."),
})}

var ProductClass = productClassThm{family.Add(registry.ProofEntry{
	Name: "ProductClass",
	Key:  "prop_76df965e158b62e6",
	Deps: []registry.EntryLike{ClassEquality},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀p q:num. " +
			"∀α β:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, p, α)",
			"manifold_form_on⟨n⟩(T, 𝒜, q, β)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, α))",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, p, α) = " +
				"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
			"manifold_exterior_derivative⟨n⟩(T, 𝒜, q, β) = " +
				"(λc:prod(set(A), A → num → real). λy:(num → real). λV:(num → num → real). &0)",
		},
		Conclusion: "compact_de_rham_product(n, " +
			"    T, " +
			"    𝒜, " +
			"    p, " +
			"    q, " +
			"    compact_de_rham_class(n, T, 𝒜, p, α), " +
			"    de_rham_class⟨n⟩(T, 𝒜, q, β)) = " +
			"compact_de_rham_class(n, T, 𝒜, p + q, manifold_form_wedge⟨n⟩(T, 𝒜, p, q, α, β))",
	},
		"Leibniz gives closedness and shows both changes "+
			"by exact forms produce compact exact differences."),
})}

var ProperPullback = properPullbackThm{family.Add(registry.ProofEntry{
	Name: "ProperPullback",
	Key:  "prop_2a74110ea9c9a06d",
	Deps: []registry.EntryLike{Complex},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀m:num. " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀k:num.",
		Hypotheses: []string{"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)", "kc_proper_map(T, S, f)"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    compact_de_rham_module(m, S, ℬ, k), " +
			"    compact_de_rham_module(n, T, 𝒜, k), " +
			"    compact_de_rham_pullback(n, T, 𝒜, m, S, ℬ, f, k))",
	},
		"Pullback commutes with d and its support is contained in the "+
			"inverse image of the target support, which is compact by properness."),
})}

var OpenExtension = openExtensionThm{family.Add(registry.ProofEntry{
	Name: "OpenExtension",
	Key:  "prop_3ac2eb0f9c7d5047",
	Deps: []registry.EntryLike{Complex},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀U:set(A). ∀k:num.",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "U ∈ T"},
		Conclusion: "module_homomorphism(real_ring, " +
			"    compact_de_rham_module(n, subtopology(T, U), open_submanifold_atlas⟨n⟩(T, 𝒜, U), k), " +
			"    compact_de_rham_module(n, T, 𝒜, k), " +
			"    compact_de_rham_extension(n, T, 𝒜, U, k))",
	},
		"A compact support in the open submanifold is closed in the ambient Hausdorff "+
			"manifold, so extension is smooth and commutes with differentiation."),
})}

var IntegralClass = integralClassThm{family.Add(registry.ProofEntry{
	Name: "IntegralClass",
	Key:  "prop_3ebe9cc1d217f3fe",
	Deps: []registry.EntryLike{ClassEquality, form_integral.ManifoldStokes},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
		},
		Conclusion: "compact_de_rham_integral(n, T, 𝒜, compact_de_rham_class(n, T, 𝒜, n, ω)) = " +
			"manifold_form_integral⟨n⟩(T, 𝒜, ω)",
	}, "Stokes annihilates compact exact top forms, including the separate degree-zero convention."),
})}
