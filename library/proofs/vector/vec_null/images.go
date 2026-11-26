// Local Lipschitz maps preserve null sets in equal dimensions; adding
// zero coordinates gives the lower-dimensional image theorem.

package vec_null

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// LocallyLipschitzPreservesNull — a locally Lipschitz map between open
// subsets of equal-dimensional Euclidean spaces sends null sets to null sets.
var LocallyLipschitzPreservesNull = locallyLipschitzPreservesNullThm{family.Add(registry.ProofEntry{
	Name: "LocallyLipschitzPreservesNull",
	Key:  "prop_d391e40d19ec629",
	Deps: []registry.EntryLike{
		NullSubset,
		NullCountableUnion,
		euclidean_topology.EuclideanSecondCountable,
		countability.SecondCountableSubtopology,
		countability.SecondCountableImpLindelof,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀U S:set(num → real). ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"S ⊆ U",
			"vec_null_set⟨n⟩(S)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ " +
				"    ∃V:set(num → real). " +
				"        V ∈ euclidean_topology(n) ∧ " +
				"        x ∈ V ∧ " +
				"        V ⊆ U ∧ " +
				"        lipschitz_map(V, vec_dist⟨n⟩, {y:num → real | vec⟨n⟩(y)}, vec_dist⟨n⟩, f)",
		},
		Conclusion: "vec_null_set⟨n⟩(image(f, S))",
	},
		"For one Lipschitz neighbourhood, choose in S ∩ V a point of each covering cube that "+
			"meets it. The image of that cube's intersection lies in a cube about the chosen image "+
			"point, with radius bounded by a fixed multiple of the original radius; this works even "+
			"if the original cube leaves V. EuclideanSecondCountable, SecondCountableSubtopology "+
			"and SecondCountableImpLindelof select countably many neighbourhoods; NullSubset and "+
			"NullCountableUnion assemble the images. In dimension zero S is empty."),
})}

// LowerDimensionalImageNull — a locally Lipschitz map into a higher
// dimensional Euclidean space has null image.
var LowerDimensionalImageNull = lowerDimensionalImageNullThm{family.Add(registry.ProofEntry{
	Name: "LowerDimensionalImageNull",
	Key:  "prop_44cb033a3145dda3",
	Deps: []registry.EntryLike{NullCoordinateSubspace, NullSubset, LocallyLipschitzPreservesNull},
	Build: family.Card(Statement{
		Binders: "∀a b:num. ∀U:set(num → real). ∀f:((num → real) → (num → real)).",
		Hypotheses: []string{
			"a < b",
			"U ∈ euclidean_topology(a)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ " +
				"    ∃V:set(num → real). " +
				"        V ∈ euclidean_topology(a) ∧ " +
				"        x ∈ V ∧ " +
				"        V ⊆ U ∧ " +
				"        lipschitz_map(V, vec_dist⟨a⟩, {y:num → real | vec⟨b⟩(y)}, vec_dist⟨b⟩, f)",
		},
		Conclusion: "vec_null_set⟨b⟩(image(f, U))",
	},
		"Let p truncate a b-vector after coordinate a and extend f to F = f ∘ p on "+
			"the open cylinder p⁻¹(U) in ℝᵇ. The projection is 1-Lipschitz, so F is "+
			"locally Lipschitz there; U itself is a null subset of the coordinate "+
			"subspace (NullCoordinateSubspace, NullSubset). LocallyLipschitzPreservesNull "+
			"applied to F gives the result, since p fixes U. This includes a = 0."),
})}
