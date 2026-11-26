// Positive diffeomorphisms preserve support by preimage and preserve top-form integrals.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var OrientedDiffeomorphismInverse = orientedDiffeomorphismInverseThm{family.Add(registry.ProofEntry{
	Name: "OrientedDiffeomorphismInverse",
	Key:  "prop_2f85e5eba5253fb8",
	Reading: "Only carrier inverse equations are used. Neither inverse_on nor its iterated " +
		"inverse is required to agree with a chosen total map off the relevant carrier.",
	Deps: []registry.EntryLike{
		OrientedDiffeomorphismDef,
		smooth_manifold.SmoothMapCongruence,
		continuous.HomeomorphismInverse,
		vec_smooth.JacobianDeterminantChain,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{"oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)"},
		Conclusion: "oriented_diffeomorphism⟨n⟩(S, ℬ, T, 𝒜, inverse_on(⋃T, f))",
	},
		"The carrier inverse is a homeomorphism and smooth by definition; its inverse "+
			"agrees with f on the carrier. Local coordinate composition with the forward "+
			"map is the identity, so the two Jacobian determinants multiply to one. The "+
			"positive forward determinant therefore gives a positive inverse determinant."),
})}

var DiffeomorphismPullbackSupport = diffeomorphismPullbackSupportThm{family.Add(registry.ProofEntry{
	Name: "DiffeomorphismPullbackSupport",
	Key:  "prop_e716639a63e813b",
	Reading: "Invertibility of the tangent maps gives equality of nonzero loci in every degree; the " +
		"homeomorphism transports their closures. For degrees above the dimension both supports are empty.",
	Deps: []registry.EntryLike{
		OrientedDiffeomorphismDef,
		OrientedDiffeomorphismInverse,
		differential_form.SupportDef,
		differential_form.PullbackCoordinate,
		differential_form.PullbackCompose,
		differential_form.PullbackIdentity,
		function_support.SupportHomeomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀k:num. " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨n⟩(S, ℬ, k, ω)",
		},
		Conclusion: "manifold_form_support⟨n⟩(T, 𝒜, manifold_form_pullback⟨n, n⟩(T, 𝒜, S, ℬ, k, f, ω)) = " +
			"preimage_on(⋃T, f, manifold_form_support⟨n⟩(S, ℬ, ω))",
	},
		"The local pullback formula shows that zero target values give zero source values. "+
			"Pulling back again by the smooth inverse gives the converse, so the nonzero base "+
			"locus is exactly the carrier-relative preimage of the target nonzero locus. The "+
			"base homeomorphism transports its closure by SupportHomeomorphism."),
})}

var IntegralDiffeomorphism = integralDiffeomorphismThm{family.Add(registry.ProofEntry{
	Name: "IntegralDiffeomorphism",
	Key:  "prop_ac14ebc6c7eedd28",
	Reading: "Compactness of the pulled-back support follows from the " +
		"homeomorphism. No properness claim is made for a general smooth map, " +
		"whose pullback of a compactly supported form need not have compact support.",
	Deps: []registry.EntryLike{
		OrientedDiffeomorphismDef,
		DiffeomorphismPullbackSupport,
		IntegralByPartition,
		IntegralPartitionExists,
		PositiveTransition,
		differential_form.PullbackCoordinate,
		differential_form.PullbackWedge,
		differential_form.WeightAsWedge,
		differential_form.ChartCoefficientCompact,
		vec_form.TopDegreeDeterminant,
		vec_integral.ChangeOfVariables,
		continuous.ImageCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀ω:(prod(set(B), B → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)",
			"manifold_form_on⟨n⟩(S, ℬ, n, ω)",
			"compact_in(S, manifold_form_support⟨n⟩(S, ℬ, ω))",
		},
		Conclusion: "manifold_form_integral⟨n⟩(T, " +
			"    𝒜, " +
			"    manifold_form_pullback⟨n, n⟩(T, 𝒜, S, ℬ, n, f, ω)) = " +
			"manifold_form_integral⟨n⟩(S, ℬ, ω)",
	},
		"The inverse homeomorphism makes the pulled-back support compact. Refine a finite partition so "+
			"each source summand and its image lie in positive source and target charts. PullbackCoordinate "+
			"and the top-degree determinant formula turn its integral into Euclidean change of variables "+
			"with a positive Jacobian; summing the local equalities gives the invariant integral."),
})}
