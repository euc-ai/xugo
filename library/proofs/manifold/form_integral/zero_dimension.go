// Zero-dimensional integration is the finite sum of scalar values on support.

package form_integral

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegralZeroDimension = integralZeroDimensionThm{family.Add(registry.ProofEntry{
	Name: "IntegralZeroDimension",
	Key:  "prop_9f6d318f933104e8",
	Reading: "Every point has the canonical positive sign in this atlas convention. Empty support " +
		"gives the empty sum zero, and no separate negative orientation exists in dimension zero. " +
		"Smooth scalar-function membership includes the underlying manifold and exterior normalization. " +
		"Singleton chart domains make its topology discrete, so compact support is finite.",
	Deps: []registry.EntryLike{
		OrientedZeroDimension,
		IntegralByPartition,
		IntegralPartitionExists,
		chartIntegralDef,
		differential_form.FunctionForm,
		differential_form.FunctionFormDef,
		differential_form.SupportDef,
		smooth_manifold.SmoothFunctionDef,
		smooth_manifold.ChartDef,
		smooth_manifold.AtlasDef,
		smooth_manifold.PartitionOfUnityDef,
		vec_integral.VecIntegralDef,
	},
	Build: family.Card(Statement{
		Binders: "∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real).",
		Hypotheses: []string{
			"smooth_manifold_function⟨0⟩(T, 𝒜, f)",
			"compact_in(T, function_support(T, &0, f))",
		},
		Conclusion: "finite(function_support(T, &0, f)) ∧ " +
			"manifold_form_integral⟨0⟩(T, 𝒜, manifold_function_form⟨0⟩(T, 𝒜, f)) = " +
			"Σ_{x∈function_support(T, &0, f)} f(x)",
	},
		"A zero-dimensional chart has empty or singleton domain, so the manifold is "+
			"discrete and a compact support is finite. The zero-dimensional Euclidean "+
			"integral reads the coefficient at its sole vector. Group the finite partition "+
			"contributions by base point and use that the weights sum to one on the support."),
})}
