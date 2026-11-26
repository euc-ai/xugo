// Finite-basis Künneth gives Betti convolution and Euler multiplicativity for compact products.

package de_rham_betti

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_cover"
	"github.com/euc-ai/xugo/library/proofs/manifold/de_rham_kunneth"
	"github.com/euc-ai/xugo/library/registry"
)

var CompactProductBetti = compactProductBettiThm{family.Add(registry.ProofEntry{
	Name: "CompactProductBetti",
	Key:  "prop_aadabaae3327fdec",
	Reading: "The sum uses only p≤k, so natural subtraction is never used for a negative " +
		"degree. Terms above either factor dimension vanish. Empty factors give zero in " +
		"every degree, and neither factor needs an orientation. Degree tags distinguish the " +
		"coefficient coordinates, and labels above k have zero coefficient modules.",
	Deps: []registry.EntryLike{
		BettiDef,
		BettiBasis,
		BettiHomogeneousBasis,
		de_rham_cover.CompactManifoldFiniteCohomology,
		de_rham_kunneth.CompactManifoldHomogeneousBasis,
		de_rham_kunneth.CompactManifoldKunnethComparison,
		de_rham_kunneth.KunnethCoefficientModuleDef,
		de_rham_kunneth.HomogeneousBasisDegreeBound,
		module_dimension.FiniteDimensionalDef,
		module_dimension.IsomorphismDim,
		function_module.IndexedProductModule,
		nat_sum.NatSumDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀k:num.",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"compact_in(T, ⋃T)",
			"compact_in(S, ⋃S)",
		},
		Conclusion: "finite_dimensional(real_ring, " +
			"    de_rham_cohomology_module⟨n + m⟩(product_topology(T, S), " +
			"        smooth_product_atlas⟨n, m⟩(𝒜, ℬ), " +
			"        k)) ∧ " +
			"de_rham_betti⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ), k) = " +
			"nat_sum({p:num | p ≤ k}, λp:num. de_rham_betti⟨n⟩(T, 𝒜, p) * de_rham_betti⟨m⟩(S, ℬ, k - p))",
	},
		"Choose the finite homogeneous basis of the second factor and finite bases of the first "+
			"factor in every needed degree. Put each first-factor basis vector in one active "+
			"coefficient coordinate and zero in the others: these vectors form a basis of the finite "+
			"indexed coefficient module. Count them degree by degree, with zero modules for labels "+
			"above k. Transport the basis and dimension through CompactManifoldKunnethComparison."),
})}

var EulerCompactProduct = eulerCompactProductThm{family.Add(registry.ProofEntry{
	Name: "EulerCompactProduct",
	Key:  "prop_c08378267e9d07bb",
	Reading: "Both factors are compact smooth manifolds, possibly empty, " +
		"disconnected or nonorientable. This is multiplication of ordinary de Rham " +
		"Euler characteristics and does not use integration or product orientations.",
	Deps: []registry.EntryLike{
		EulerDef,
		CompactProductBetti,
		BettiAboveDimension,
		real_sum.RealOfNatSum,
		real_sum.Swap,
		real_sum.ScalarLeft,
		real_sum.ScalarRight,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨m⟩(S, ℬ)",
			"compact_in(T, ⋃T)",
			"compact_in(S, ⋃S)",
		},
		Conclusion: "de_rham_euler⟨n + m⟩(product_topology(T, S), smooth_product_atlas⟨n, m⟩(𝒜, ℬ)) = " +
			"de_rham_euler⟨n⟩(T, 𝒜) * de_rham_euler⟨m⟩(S, ℬ)",
	},
		"Insert CompactProductBetti into the Euler sum and coerce the finite natural sums to real "+
			"sums. Reindex by p+q=k; all terms outside 0≤p≤n and 0≤q≤m vanish. The sign of p+q is the "+
			"product of the two signs, so the finite double sum factors into the two Euler sums."),
})}
