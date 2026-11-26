// The comparison is linear and natural in its first factor.

package de_rham_kunneth

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_product"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/registry"
)

var KunnethMapHom = kunnethMapHomThm{family.Add(registry.ProofEntry{
	Name: "KunnethMapHom",
	Key:  "prop_b90b89527a3604d1",
	Reading: "The tagged classes need only be valid and finite in " +
		"number; their independence and spanning are not needed for linearity.",
	Deps: []registry.EntryLike{
		KunnethMapDef,
		KunnethCoefficientModule,
		de_rham_product.ExternalProductBilinear,
		function_module.IndexedProductSumHom,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀E:set(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"finite(E)",
			"∀e:prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)). " +
				"    e ∈ E ⇒ snd(e) ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, fst(e)).carrier",
		},
		Conclusion: "module_homomorphism(real_ring, " +
			"    de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E), " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k), " +
			"    de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E))",
	},
		"At each active degree, fix the second argument of ExternalProductBilinear; "+
			"the degree sum equals k. Above k use the zero map out of the zero summand. "+
			"IndexedProductSumHom sums these homomorphisms over E."),
})}

var KunnethNaturality = kunnethNaturalityThm{family.Add(registry.ProofEntry{
	Name: "KunnethNaturality",
	Key:  "prop_96f3d11e68dd143c",
	Reading: "The coefficient pullback is specified on its carrier by the " +
		"component equations. Both families belong to their coefficient modules, " +
		"which forces zero values for negative summands and fixes all values outside E.",
	Deps: []registry.EntryLike{
		KunnethMapDef,
		KunnethMapHom,
		de_rham_product.ExternalProductNaturality,
		de_rham.PullbackHom,
		de_rham.PullbackIdentity,
		module_homomorphism.HomSum,
		smooth_manifold.SmoothMapIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n m l k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀Q:set(set(C)). " +
			"∀𝒞:set(prod(set(C), C → num → real)). " +
			"∀E:set(prod(num, " +
			"            set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real))). " +
			"∀f:(C → A). " +
			"∀a:(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)) → " +
			"        set(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real)). " +
			"∀b:(prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)) → " +
			"        set(prod(set(C), C → num → real) → (num → real) → (num → num → real) → real)).",
		Hypotheses: []string{
			"smooth_manifold_map⟨l, n⟩(Q, 𝒞, T, 𝒜, f)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"finite(E)",
			"∀e:prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)). " +
				"    e ∈ E ⇒ snd(e) ∈ de_rham_cohomology_module⟨m⟩(S, ℬ, fst(e)).carrier",
			"a ∈ de_rham_kunneth_module⟨n⟩(T, 𝒜, k, E).carrier",
			"b ∈ de_rham_kunneth_module⟨l⟩(Q, 𝒞, k, E).carrier",
			"∀e:prod(num, set(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real)). " +
				"    e ∈ E ∧ fst(e) ≤ k ⇒ b(e) = de_rham_pullback⟨l, n⟩(Q, 𝒞, T, 𝒜, k - fst(e), f)(a(e))",
		},
		Conclusion: "de_rham_pullback⟨l + m, n + m⟩(product_topology(Q, S), " +
			"    smooth_product_atlas⟨l, m⟩(𝒞, ℬ), " +
			"    product_topology(T, S), " +
			"    smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"    k, " +
			"    (λz:prod(C, B). (f(fst(z)), snd(z))))(de_rham_kunneth_map⟨n, m⟩(T, 𝒜, S, ℬ, k, E)(a)) = " +
			"de_rham_kunneth_map⟨l, m⟩(Q, 𝒞, S, ℬ, k, E)(b)",
	},
		"Pullback preserves the finite sum. ExternalProductNaturality with the identity on the "+
			"second factor gives the equality term by term at every permitted degree; above k both terms "+
			"are zero. The prescribed normalization determines the inactive coefficient coordinates."),
})}
