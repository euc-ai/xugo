// Positive chart changes identify every finite partition integral.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var ChartIntegralChange = chartIntegralChangeThm{family.Add(registry.ProofEntry{
	Name: "ChartIntegralChange",
	Key:  "prop_52895d78d31dada1",
	Reading: "The common support must lie inside both chart domains. Positivity " +
		"supplies the sign: Euclidean change of variables uses an absolute " +
		"Jacobian, while the top-form transition uses its signed determinant.",
	Deps: []registry.EntryLike{
		chartIntegralDef,
		PositiveTransition,
		differential_form.FormOnDef,
		differential_form.ChartCoefficientCompact,
		vec_form.TopDegreeDeterminant,
		vec_form.PullbackDef,
		vec_integral.ChangeOfVariables,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c d:prod(set(A), A → num → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"positive_manifold_chart⟨n⟩(T, 𝒜, c)",
			"positive_manifold_chart⟨n⟩(T, 𝒜, d)",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ fst(c) ∩ fst(d)",
		},
		Conclusion: "manifold_chart_integral⟨n⟩(c, ω) = manifold_chart_integral⟨n⟩(d, ω)",
	},
		"The top-degree overlap equation relates the two identity-frame coefficients by the "+
			"transition determinant. PositiveTransition makes that determinant equal to its "+
			"absolute value. The compact support lies in the overlap, so "+
			"ChartCoefficientCompact and Euclidean ChangeOfVariables identify the two integrals."),
})}

var IntegralPartitionExists = integralPartitionExistsThm{family.Add(registry.ProofEntry{
	Name: "IntegralPartitionExists",
	Key:  "prop_741e331ad222c778",
	Deps: []registry.EntryLike{
		integralPartitionDef,
		AtlasMemberPositive,
		OrientedManifoldDef,
		PositiveChartDef,
		smooth_manifold.PartitionOfUnity,
		smooth_manifold.PartitionOfUnityDef,
		smooth_manifold.ChartDef,
		smooth_manifold.AtlasDef,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K:set(A).",
		Hypotheses: []string{"oriented_manifold⟨n⟩(T, 𝒜)", "compact_in(T, K)"},
		Conclusion: "∃N:num. ∃c:(num → prod(set(A), A → num → real)). ∃ψ:(num → A → real). " +
			"    manifold_integral_partition⟨n⟩(T, 𝒜, K, N, c, ψ)",
	},
		"Positive chart domains form an open cover because they include every original chart domain. "+
			"Apply the compact partition theorem to that cover, then select for each active weight a "+
			"positive chart whose domain contains its support. Inactive indices can be chosen arbitrarily."),
})}

var IntegralPartitionIndependent = integralPartitionIndependentThm{family.Add(registry.ProofEntry{
	Name: "IntegralPartitionIndependent",
	Key:  "prop_b78458e592ef77cf",
	Reading: "No individual partition term is assumed to have support in every other " +
		"chart. Only the doubly weighted term lies in the relevant chart intersection. " +
		"The refinement is finite and uses no measure-theoretic interchange theorem. " +
		"Compactness of the form support is already part of each partition predicate; " +
		"the product-weighted supports are closed subsets of compact scalar supports.",
	Deps: []registry.EntryLike{
		integralPartitionDef,
		ChartIntegralChange,
		chartIntegralDef,
		differential_form.WeightDef,
		differential_form.WeightForm,
		differential_form.WeightSupport,
		differential_form.ChartCoefficientCompact,
		smooth_manifold.PartitionOfUnityDef,
		vec_integral.IntegralSum,
		vec_integral.CcRapid,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀N L:num. " +
			"∀c d:(num → prod(set(A), A → num → real)). " +
			"∀ψ χ:(num → A → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"manifold_integral_partition⟨n⟩(T, 𝒜, manifold_form_support⟨n⟩(T, 𝒜, ω), N, c, ψ)",
			"manifold_integral_partition⟨n⟩(T, 𝒜, manifold_form_support⟨n⟩(T, 𝒜, ω), L, d, χ)",
		},
		Conclusion: "Σ_{i<N} manifold_chart_integral⟨n⟩(c(i), manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω)) = " +
			"Σ_{i<L} manifold_chart_integral⟨n⟩(d(i), manifold_form_weight⟨n⟩(T, 𝒜, χ(i), ω))",
	},
		"Refine both finite decompositions by the products ψ_i χ_j. Each refined form has compact "+
			"support in the intersection of its two assigned positive chart domains, so ChartIntegralChange "+
			"identifies its two coordinate integrals. Linearity and exchange of the finite double sums "+
			"recover the original sums, since both partitions are one on the form support."),
})}

var HasIntegralExists = hasIntegralExistsThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralExists",
	Key:  "prop_dac0794e5c7c7eea",
	Deps: []registry.EntryLike{HasIntegralDef, IntegralPartitionExists},
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
		Conclusion: "∃I:real. has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)",
	},
		"Choose a finite positive-chart partition of the compact support. "+
			"Its coordinate integral sum is a witness for the defining relation."),
})}

var HasIntegralUnique = hasIntegralUniqueThm{family.Add(registry.ProofEntry{
	Name: "HasIntegralUnique",
	Key:  "prop_6b9bbce88f750722",
	Deps: []registry.EntryLike{HasIntegralDef, IntegralPartitionIndependent},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀I J:real.",
		Hypotheses: []string{
			"has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)",
			"has_manifold_form_integral⟨n⟩(T, 𝒜, ω, J)",
		},
		Conclusion: "I = J",
	},
		"Unpack the two witnessed finite partitions from the relation. "+
			"IntegralPartitionIndependent equates their sums, which are I and J."),
})}

var IntegralSpec = integralSpecThm{family.Add(registry.ProofEntry{
	Name: "IntegralSpec",
	Key:  "prop_e46f228a32faa9f1",
	Deps: []registry.EntryLike{IntegralDef, HasIntegralExists},
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
		Conclusion: "has_manifold_form_integral⟨n⟩(T, 𝒜, ω, manifold_form_integral⟨n⟩(T, 𝒜, ω))",
	},
		"HasIntegralExists supplies a witness for the epsilon predicate. "+
			"Choice therefore makes the selected scalar an integral value."),
})}

var IntegralValue = integralValueThm{family.Add(registry.ProofEntry{
	Name: "IntegralValue",
	Key:  "prop_5dcfb0d42713ece2",
	Deps: []registry.EntryLike{HasIntegralDef, IntegralSpec, HasIntegralUnique},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀I:real.",
		Hypotheses: []string{"has_manifold_form_integral⟨n⟩(T, 𝒜, ω, I)"},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, ω) = I",
	},
		"The relation supplies the orientation, form and compactness hypotheses for IntegralSpec. "+
			"Its selected value and I satisfy the same relation, so uniqueness equates them."),
})}

var IntegralByPartition = integralByPartitionThm{family.Add(registry.ProofEntry{
	Name: "IntegralByPartition",
	Key:  "prop_cf57d642e03fbbe9",
	Deps: []registry.EntryLike{
		integralPartitionDef,
		HasIntegralDef,
		IntegralValue,
		differential_form.SupportClosed,
		smooth_manifold.PartitionOfUnityDef,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀K:set(A). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀N:num. " +
			"∀c:(num → prod(set(A), A → num → real)). " +
			"∀ψ:(num → A → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n⟩(T, 𝒜)",
			"manifold_form_on⟨n⟩(T, 𝒜, n, ω)",
			"manifold_integral_partition⟨n⟩(T, 𝒜, K, N, c, ψ)",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ K",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, 𝒜, ω) = " +
			"Σ_{i<N} manifold_chart_integral⟨n⟩(c(i), manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω))",
	},
		"The form support is a closed subset of compact K, hence compact. A partition equal to one "+
			"near K is also a partition near that support, with the same assigned charts and weights. "+
			"Its finite sum witnesses the relation, and IntegralValue identifies it with the operator."),
})}
