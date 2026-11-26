// Normalized scalar functions and finite partitions near compact subsets.

package smooth_manifold

import (
	_ "github.com/euc-ai/xugo/library/proofs/topology/compact"
	_ "github.com/euc-ai/xugo/library/proofs/topology/function_support"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothFunctionDef = smoothFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "SmoothFunctionDef",
	Key:   "prop_811dfaee9fa94ef",
	Const: "smooth_manifold_function",
	Type:  "num → set(set(A)) → set(prod(set(A), A → num → real)) → (A → real) → bool",
	Dim:   "n",
	Reading: "Scalar functions are normalized to zero outside the manifold " +
		"carrier. Smoothness is required only on each open coordinate image, and says " +
		"nothing about smoothness of a coordinate zero extension across its boundary.",
	Equations: []string{
		"∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀f:(A → real). " +
			"    smooth_manifold_function⟨n⟩(T, 𝒜, f) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    (∀x:A. x ∉ ⋃T ⇒ f(x) = &0) ∧ " +
			"    (∀c:prod(set(A), A → num → real). " +
			"        compatible_chart⟨n⟩(T, 𝒜, c) ⇒ " +
			"        vec_smooth_on⟨n⟩(image(snd(c), fst(c)), f ∘ inverse_on(fst(c), snd(c))))",
	},
})}

var PartitionOfUnityDef = partitionOfUnityDefThm{family.Define(registry.DefEntry{
	Name:  "PartitionOfUnityDef",
	Key:   "prop_f84eaf6325d67259",
	Const: "manifold_partition_of_unity",
	Type: "num → " +
		"set(set(A)) → " +
		"set(prod(set(A), A → num → real)) → " +
		"set(A) → " +
		"set(set(A)) → " +
		"num → " +
		"(num → A → real) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{SmoothFunctionDef},
	Reading: "Only indices i < N are active. Each active function has compact " +
		"support inside one covering open set. The sum is one on an open neighbourhood of " +
		"K and at most one globally. For K empty, N may be zero and the neighbourhood empty.",
	Equations: []string{
		"∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀K:set(A). " +
			"∀C:set(set(A)). " +
			"∀N:num. " +
			"∀ψ:(num → A → real). " +
			"    manifold_partition_of_unity⟨n⟩(T, 𝒜, K, C, N, ψ) ⇔ " +
			"    smooth_manifold⟨n⟩(T, 𝒜) ∧ " +
			"    compact_in(T, K) ∧ " +
			"    C ⊆ T ∧ " +
			"    K ⊆ ⋃C ∧ " +
			"    (∀i:num. " +
			"        i < N ⇒ " +
			"        smooth_manifold_function⟨n⟩(T, 𝒜, ψ(i)) ∧ " +
			"        (∀x:A. &0 ≤ ψ(i, x)) ∧ " +
			"        compact_in(T, function_support(T, &0, ψ(i))) ∧ " +
			"        (∃U:set(A). U ∈ C ∧ function_support(T, &0, ψ(i)) ⊆ U)) ∧ " +
			"    (∀x:A. x ∈ ⋃T ⇒ Σ_{i<N} ψ(i, x) ≤ &1) ∧ " +
			"    (∃V:set(A). V ∈ T ∧ K ⊆ V ∧ (∀x:A. x ∈ V ⇒ Σ_{i<N} ψ(i, x) = &1))",
	},
})}
