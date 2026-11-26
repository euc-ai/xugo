// Compact bumps give finite partitions equal to one on an open neighbourhood.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/function_support"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FunctionBump = functionBumpThm{family.Add(registry.ProofEntry{
	Name: "FunctionBump",
	Key:  "prop_3c793a9e36eb2040",
	Reading: "K may be empty: the zero function and empty neighbourhood work. The support itself " +
		"is compact and contained in U, rather than merely requiring vanishing pointwise outside U.",
	Deps: []registry.EntryLike{
		SmoothFunctionDef,
		FunctionLocal,
		FunctionExtendZero,
		vec_smooth.BumpFunction,
		ChartDef,
		AtlasDef,
		continuous.ImageCompact,
		compact.CompactClosed,
		compact.CompactUnions,
		function_support.SupportClosedBound,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)). ∀K U:set(A).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, K)", "U ∈ T", "K ⊆ U"},
		Conclusion: "∃f:(A → real). " +
			"    smooth_manifold_function⟨n⟩(T, 𝒜, f) ∧ " +
			"    compact_in(T, function_support(T, &0, f)) ∧ " +
			"    function_support(T, &0, f) ⊆ U ∧ " +
			"    (∀x:A. &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ " +
			"    (∃V:set(A). V ∈ T ∧ K ⊆ V ∧ (∀x:A. x ∈ V ⇒ f(x) = &1))",
	},
		"Around each point of K choose nested coordinate balls with compact outer closure "+
			"inside U and pull back a Euclidean bump. Compactness and Hausdorffness keep its "+
			"support closed inside that chart, so FunctionExtendZero applies. A finite inner-ball "+
			"cover of K gives a bump by one minus the product of one minus the local bumps; its "+
			"support lies in their finite compact union and it is one on the inner cover."),
})}

var PartitionOfUnity = partitionOfUnityThm{family.Add(registry.ProofEntry{
	Name: "PartitionOfUnity",
	Key:  "prop_5270aa4903cd3168",
	Reading: "Normalization by s takes place only on O = {x in the carrier | 0 < s(x)}. The " +
		"cutoff has compact support inside O, so zero extension is smooth without dividing at zeros " +
		"of s. Each quotient's relatively closed support lies inside the compact cutoff support, " +
		"hence is ambient closed in this Hausdorff manifold. For empty K an empty partition suffices.",
	Deps: []registry.EntryLike{
		PartitionOfUnityDef,
		FunctionBump,
		FunctionFiniteSum,
		FunctionMul,
		FunctionReciprocal,
		FunctionContinuous,
		FunctionRestrict,
		FunctionExtendZero,
		function_support.SupportProduct,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀K:set(A). " +
			"∀C:set(set(A)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, K)", "C ⊆ T", "K ⊆ ⋃C"},
		Conclusion: "∃N:num. ∃ψ:(num → A → real). manifold_partition_of_unity⟨n⟩(T, 𝒜, K, C, N, ψ)",
	},
		"Choose finitely many nonnegative compact bumps subordinate to C whose positive "+
			"sets cover K. Their sum s is positive on an open neighbourhood O of K; choose "+
			"a compact cutoff χ in O that is one near K. On O use χ times each bump divided "+
			"by s and extend by zero: the supports stay inside the corresponding covering "+
			"sets and the total sum is χ, hence at most one and equal to one near K."),
})}
