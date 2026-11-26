// A finite partition localizes a compactly supported form inside covering opens.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/registry"
)

var FormPartitionDecomposition = formPartitionDecompositionThm{family.Add(registry.ProofEntry{
	Name: "FormPartitionDecomposition",
	Key:  "prop_7b8d95ec8612e764",
	Reading: "For empty K the form is zero and an empty sum is valid. Taking C to be " +
		"chart domains produces compact chart-supported summands for integration and Stokes.",
	Deps: []registry.EntryLike{
		WeightDef,
		WeightForm,
		WeightSupport,
		SupportDef,
		SupportClosed,
		FormOnDef,
		smooth_manifold.PartitionOfUnityDef,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀K:set(A). " +
			"∀C:set(set(A)). " +
			"∀N:num. " +
			"∀ψ:(num → A → real). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"manifold_partition_of_unity⟨n⟩(T, 𝒜, K, C, N, ψ)",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ K",
		},
		Conclusion: "ω = " +
			"(λc:prod(set(A), A → num → real). λy:(num → real). λP:(num → num → real). " +
			"    Σ_{i<N} manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω, c, y, P)) ∧ " +
			"(∀i:num. " +
			"    i < N ⇒ " +
			"    manifold_form_on⟨n⟩(T, 𝒜, k, manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω)) ∧ " +
			"    compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω))) ∧ " +
			"    (∃U:set(A). " +
			"        U ∈ C ∧ manifold_form_support⟨n⟩(T, 𝒜, manifold_form_weight⟨n⟩(T, 𝒜, ψ(i), ω)) ⊆ U))",
	},
		"Where the form is nonzero, its base point belongs to K and the partition sums to "+
			"one; elsewhere every weighted value is zero. This gives literal family equality "+
			"after the finite sum. WeightForm supplies the carriers, while WeightSupport "+
			"bounds each closed support by its compact scalar support inside one covering set."),
})}
