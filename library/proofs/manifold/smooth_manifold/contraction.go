// A smooth bounded time parameter contracts a convex Euclidean open set on the whole time line.

package smooth_manifold

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/convex"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ConvexOpenContraction = convexOpenContractionThm{family.Add(registry.ProofEntry{
	Name: "ConvexOpenContraction",
	Key:  "prop_5f0a7f7c0bd4d072",
	Reading: "The straight-line formula with θ(t)=t can leave an open bounded " +
		"convex set for times just beyond [0,1]. The bounded smooth clock gives a " +
		"single open time domain for every x, including points arbitrarily near " +
		"the boundary. The point a ensures U is nonempty; n=0 is allowed.",
	Deps: []registry.EntryLike{
		EuclideanManifold,
		ProductManifold,
		SmoothMapCompatibleCharts,
		vec_smooth.BumpFunction,
		vec_smooth.SmoothAdd,
		vec_smooth.SmoothMul,
		convex.Segment,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀U:set(num → real). ∀a:(num → real).",
		Hypotheses: []string{"U ∈ euclidean_topology(n)", "convex(U)", "a ∈ U"},
		Conclusion: "∃H:(prod(num → real, num → real) → num → real). " +
			"    smooth_manifold_map⟨n + 1, n⟩( " +
			"        product_topology(subtopology(euclidean_topology(n), U), euclidean_topology(1)), " +
			"        smooth_product_atlas⟨n, 1⟩(euclidean_atlas(U), " +
			"            euclidean_atlas({t:num → real | vec⟨1⟩(t)})), " +
			"        subtopology(euclidean_topology(n), U), " +
			"        euclidean_atlas(U), " +
			"        H) ∧ " +
			"    (∀x:(num → real). " +
			"        x ∈ U ⇒ H((x, (λj:num. &0))) = a ∧ H((x, (λj:num. COND(j = 0, &1, &0)))) = x) ∧ " +
			"    (∀t:(num → real). vec⟨1⟩(t) ⇒ H((a, t)) = a)",
	},
		"Take a one-dimensional bump φ about zero, equal to one near zero and zero at "+
			"distance at least one, with 0≤φ≤1. Put θ=1−φ and H(x,t)=(1−θ(t))a+θ(t)x. Convexity "+
			"keeps H in U for every real time, and its coordinate expressions are smooth. The "+
			"endpoint values of the bump give the two endpoints and H fixes a for all times."),
})}
