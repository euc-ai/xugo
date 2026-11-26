// Regular points admit projection coordinates and regular fibers are embedded submanifolds.

package manifold_critical_point

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/countability"
	"github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/proofs/vector/basis"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var RegularPointCoordinates = regularPointCoordinatesThm{family.Add(registry.ProofEntry{
	Name: "RegularPointCoordinates",
	Key:  "prop_695c5eb90df76294",
	Reading: "The identity is on the whole selected source chart, whose image under f lies in " +
		"the target chart. Append fixed linear functions completing the independent Jacobian rows to " +
		"obtain that source chart by the inverse theorem. No assertion is made outside that chart. " +
		"For m = 0, the target chart is a singleton and the projection is the normalized zero vector.",
	Deps: []registry.EntryLike{
		CriticalPointCoordinate,
		RegularPointDimensionBound,
		smooth_manifold.SmoothMapCompatibleCharts,
		basis.Steinitz,
		determinant.DeterminantZeroIffDependent,
		vec_smooth.LinearSmoothMap,
		vec_smooth.SmoothInverseFunction,
		vec_smooth.SmoothMapCompose,
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
		Conclusion: "∃c:prod(set(A), A → num → real). ∃d:prod(set(B), B → num → real). " +
			"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
			"    compatible_chart⟨m⟩(S, ℬ, d) ∧ " +
			"    x ∈ fst(c) ∧ " +
			"    f(x) ∈ fst(d) ∧ " +
			"    image(f, fst(c)) ⊆ fst(d) ∧ " +
			"    (∀z:A. z ∈ fst(c) ⇒ snd(d)(f(z)) = (λj:num. COND(j < m, snd(c)(z, j), &0)))",
	},
		"At x the coordinate differential is onto. Extend its independent m coordinate rows to a "+
			"basis of the n-dimensional dual by Steinitz, appending fixed linear coordinate functions "+
			"to the coordinate expression of f; the augmented map has invertible square Jacobian. "+
			"SmoothInverseFunction makes these n functions a compatible source chart after shrinking "+
			"inside the target-chart preimage, where f is the displayed coordinate projection."),
})}

var RegularLevelSubmanifold = regularLevelSubmanifoldThm{family.Add(registry.ProofEntry{
	Name: "RegularLevelSubmanifold",
	Key:  "prop_14e24623bd8c489d",
	Reading: "The point type remains A but the carrier is the actual fiber with its " +
		"subspace topology. The explicit m≤n guard prevents truncated subtraction from hiding " +
		"the codimension; it follows automatically if this regular fiber is nonempty. The slice " +
		"coordinate domain is open as the inverse image of the ambient chart image under affine " +
		"insertion of the fixed first m coordinates. Insertion and deletion also give the " +
		"smooth slice transitions and injective inclusion differential, including m=0 and m=n. " +
		"Empty fibers admit an empty atlas and do not assert the existence of a level point.",
	Deps: []registry.EntryLike{
		RegularValueDef,
		RegularPointCoordinates,
		RegularPointDimensionBound,
		smooth_manifold.EmbeddingDef,
		smooth_manifold.EmptyManifold,
		countability.SecondCountableSubtopology,
		topological_space.HausdorffSubtopology,
		vec_smooth.LinearSmoothMap,
		vec_smooth.SmoothMapCompose,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀S:set(set(B)). " +
			"∀ℬ:set(prod(set(B), B → num → real)). " +
			"∀f:(A → B). " +
			"∀y:B.",
		Hypotheses: []string{
			"smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)",
			"manifold_regular_value⟨n, m⟩(T, 𝒜, S, ℬ, f, y)",
			"m ≤ n",
		},
		Conclusion: "∃𝒞:set(prod(set(A), A → num → real)). " +
			"    smooth_manifold_embedding⟨n - m, n⟩(subtopology(T, {x:A | x ∈ ⋃T ∧ f(x) = y}), " +
			"        𝒞, " +
			"        T, " +
			"        𝒜, " +
			"        identity_map)",
	},
		"At every point of the fiber use RegularPointCoordinates and fix the first m coordinates at "+
			"the target value. The remaining coordinates give an open (n−m)-dimensional slice chart, "+
			"and its inverse inserts those fixed coordinates; the induced transitions are smooth. These "+
			"charts give the subspace topology, Hausdorffness and second countability descend from the "+
			"source, and the inclusion has injective coordinate differential, giving EmbeddingDef."),
})}
