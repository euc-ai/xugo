// Countable coordinate reduction gives manifold Sard and density of all regular values.

package manifold_critical_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_critical_point"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_null"
	"github.com/euc-ai/xugo/library/registry"
)

var ManifoldSard = manifoldSardThm{family.Add(registry.ProofEntry{
	Name: "ManifoldSard",
	Key:  "prop_426c50e90a5c0a6d",
	Reading: "Second countability of the source is the countability input; " +
		"compactness is unnecessary. The claim concerns all critical values, not only " +
		"points in the image of a chosen chart. Fix one target chart at a time and " +
		"restrict every source coordinate expression to its open target-chart preimage " +
		"before applying Euclidean Sard. A zero-dimensional target has no critical values.",
	Deps: []registry.EntryLike{
		NullSetDef,
		CriticalPointCoordinate,
		smooth_manifold.SmoothMapCompatibleCharts,
		smooth_manifold.CountableAtlas,
		vec_critical_point.SmoothSard,
		vec_null.NullSubset,
		vec_null.NullCountableUnion,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
		},
		Conclusion: "manifold_null_set⟨m⟩(S, " +
			"    ℬ, " +
			"    image(f, {x:A | manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, x)}))",
	},
		"Fix a compatible target chart and choose a countable source atlas. In each source chart "+
			"restrict to the open preimage of the target-chart domain; CriticalPointCoordinate "+
			"identifies the relevant critical points and SmoothSard makes their coordinate values "+
			"null. The target-chart critical-value image is a countable union of these null sets, so "+
			"NullCountableUnion gives the conclusion in every target chart."),
})}

var RegularValuesDense = regularValuesDenseThm{family.Add(registry.ProofEntry{
	Name: "RegularValuesDense",
	Key:  "prop_8ad36ff4e7ddae98",
	Reading: "Density is relative to the whole target carrier. Smooth maps need not be onto, and " +
		"target points with empty fibers are included; the empty target satisfies the equality too.",
	Deps: []registry.EntryLike{
		RegularValueIff,
		ManifoldSard,
		NullSubset,
		NullOpenIffEmpty,
		topological_space.DenseMeetsOpen,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
		},
		Conclusion: "closure(S, {y:B | manifold_regular_value⟨n, m⟩(T, 𝒜, S, ℬ, f, y)}) = ⋃S",
	},
		"RegularValueIff identifies the regular values with the complement of the "+
			"critical-value image inside the target carrier. If a nonempty open set missed "+
			"them it would lie in this null image by ManifoldSard, contradicting NullSubset "+
			"and NullOpenIffEmpty. DenseMeetsOpen then gives the closure equation."),
})}
