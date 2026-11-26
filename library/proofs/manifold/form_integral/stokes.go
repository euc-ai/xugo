// Compactly supported exact top forms integrate to zero on manifolds without boundary.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ManifoldStokes = manifoldStokesThm{family.Add(registry.ProofEntry{
	Name: "ManifoldStokes",
	Key:  "prop_7b5c630cb978928d",
	Reading: "The manifold has dimension n+1 and the input form degree n, so no natural-number " +
		"subtraction hides a zero-dimensional case. All manifolds here have charts in open Euclidean " +
		"sets and hence no boundary. Partition derivative terms remain inside d(ψ_i η); none is " +
		"discarded individually. ChartCoefficientCompact supplies globally smooth lower-degree " +
		"coefficients. Outside the compact coordinate-support image they vanish locally, so their " +
		"global partials agree there with the normalized exterior-derivative coefficient as well.",
	Deps: []registry.EntryLike{
		IntegralPartitionExists,
		integralPartitionDef,
		IntegralSingleChart,
		IntegralFiniteSum,
		differential_form.FormPartitionDecomposition,
		differential_form.ExteriorDerivativeForm,
		differential_form.ExteriorDerivativeLinear,
		differential_form.ExteriorDerivativeSupport,
		differential_form.ExteriorDerivativeDef,
		differential_form.ChartCoefficientCompact,
		vec_form.ExteriorDerivativeDef,
		vec_integral.IntegralPartialZero,
		vec_integral.CcRapid,
		vec_integral.IntegralSum,
		vec_integral.IntegralScale,
		vec_smooth.SmoothPartial,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n + 1⟩(T, 𝒜)",
			"manifold_form_on⟨n + 1⟩(T, 𝒜, n, η)",
			"compact_in(T, manifold_form_support⟨n + 1⟩(T, 𝒜, η))",
		},
		Conclusion: "manifold_form_integral⟨n + 1⟩(T, " +
			"    𝒜, " +
			"    manifold_exterior_derivative⟨n + 1⟩(T, 𝒜, n, η)) = " +
			"&0",
	},
		"Use a finite positive-chart partition to write η as a sum of compactly supported chart-local "+
			"forms, then differentiate that entire finite identity. Each summand and its derivative stay "+
			"supported in the same chart. At the identity frame the derivative coefficient is an "+
			"alternating sum of coordinate partial derivatives of globally smooth compact coefficients; "+
			"IntegralPartialZero kills their integrals, and finite linearity gives zero."),
})}

var CompactManifoldStokes = compactManifoldStokesThm{family.Add(registry.ProofEntry{
	Name: "CompactManifoldStokes",
	Key:  "prop_e123c6491b7ec794",
	Deps: []registry.EntryLike{
		ManifoldStokes,
		differential_form.SupportClosed,
		compact.ClosedSubsetCompact,
		OrientedManifoldDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀η:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"oriented_manifold⟨n + 1⟩(T, 𝒜)",
			"manifold_form_on⟨n + 1⟩(T, 𝒜, n, η)",
			"compact_in(T, ⋃T)",
		},
		Conclusion: "manifold_form_integral⟨n + 1⟩(T, " +
			"    𝒜, " +
			"    manifold_exterior_derivative⟨n + 1⟩(T, 𝒜, n, η)) = " +
			"&0",
	},
		"The support of η is closed in the compact manifold and therefore "+
			"compact. ManifoldStokes then applies to this n-form in dimension n+1."),
})}
