// Criticality is independent of active charts, while regular values may have empty fibers.

package manifold_critical_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/basis"
	"github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var CriticalPointCoordinate = criticalPointCoordinateThm{family.Add(registry.ProofEntry{
	Name: "CriticalPointCoordinate",
	Key:  "prop_a3ba9c8036d2bd77",
	Reading: "Both chart memberships are essential. A source chart need not map wholly into the " +
		"target chart; the differential comparison takes place near x inside the target-chart preimage.",
	Deps: []registry.EntryLike{
		CriticalPointDef,
		smooth_manifold.SmoothMapCompatibleCharts,
		smooth_manifold.CompatibleTransition,
		vec_smooth.JacobianChain,
		vec_smooth.DiffeomorphismJacobianNonzero,
		matrix.MatrixActAssoc,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A. " +
			"∀c:prod(set(A), A → num → real). " +
			"∀d:prod(set(B), B → num → real).",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compatible_chart⟨m⟩(S, ℬ, d)",
			"x ∈ fst(c)",
			"f(x) ∈ fst(d)",
		},
		Conclusion: "manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, x) ⇔ " +
			"vec_critical_point⟨n, m⟩(«coordinate map»(c, d, f), snd(c)(x))",
	},
		"SmoothMapCompatibleCharts supplies smoothness on the open chart-preimage domain. "+
			"CompatibleTransition and JacobianChain conjugate any two active coordinate "+
			"differentials by invertible transition Jacobians, preserving surjectivity on "+
			"normalized carriers; hence one critical chart pair is equivalent to the displayed pair."),
})}

var RegularPointDimensionBound = regularPointDimensionBoundThm{family.Add(registry.ProofEntry{
	Name: "RegularPointDimensionBound",
	Key:  "prop_585419e4e54130d1",
	Reading: "The bound requires an actual regular source point. It is not inferred " +
		"from a regular target value whose fiber may be empty. When n<m every actual source " +
		"point is critical, while regular target values can still occur through empty fibers.",
	Deps: []registry.EntryLike{
		CriticalPointCoordinate,
		smooth_manifold.AtlasDef,
		matrix.MatrixActLinear,
		basis.StandardBasis,
		basis.IndependentBound,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀x:A.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"x ∈ ⋃T",
			"¬manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, x)",
		},
		Conclusion: "m ≤ n",
	},
		"Choose active source and target charts. By CriticalPointCoordinate the "+
			"coordinate differential is onto the m-vectors; preimages of the m standard basis "+
			"vectors form an independent family of n-vectors, so IndependentBound gives m ≤ n."),
})}

var RegularValueIff = regularValueIffThm{family.Add(registry.ProofEntry{
	Name: "RegularValueIff",
	Key:  "prop_44b5de0749b90602",
	Reading: "Values outside the image of the source carrier are regular " +
		"whenever they lie in the target carrier. This statement asserts neither " +
		"surjectivity nor nonempty regular fibers, and reads no smoothness of f.",
	Deps: []registry.EntryLike{RegularValueDef, CriticalPointDef},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀y:B.",
		Hypotheses: []string{},
		Conclusion: "manifold_regular_value⟨n, m⟩(T, 𝒜, S, ℬ, f, y) ⇔ " +
			"y ∈ ⋃S ∧ y ∉ image(f, {x:A | manifold_critical_point⟨n, m⟩(T, 𝒜, S, ℬ, f, x)})",
	},
		"Unfold RegularValueDef and the image membership condition. "+
			"CriticalPointDef already includes source-carrier membership, so "+
			"excluding all critical preimages is exactly exclusion from this image."),
})}
