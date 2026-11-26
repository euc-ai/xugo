// Compactness turns small covers of individual slices into a cover
// that is uniform over short intervals in the last coordinate.

package vec_null

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/registry"
)

// CompactNullSlices — a compact set with null slices is null.
var CompactNullSlices = compactNullSlicesThm{family.Add(registry.ProofEntry{
	Name: "CompactNullSlices",
	Key:  "prop_4446c448922a5f10",
	Deps: []registry.EntryLike{
		euclidean_topology.CompactIffClosedBounded,
		complete_metric.LebesgueNumber,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀K:set(num → real).",
		Hypotheses: []string{
			"0 < n",
			"compact_in(euclidean_topology(n + 1), K)",
			"∀t:real. vec_null_set⟨n⟩({x:num → real | vec⟨n⟩(x) ∧ (λi:num. COND(i = n, t, x(i))) ∈ K})",
		},
		Conclusion: "vec_null_set⟨n + 1⟩(K)",
	},
		"K is bounded (euclidean_topology.CompactIffClosedBounded). Each slice is compact, so retain "+
			"finitely many cubes from a small-volume cover; compactness of K makes the same cubes cover "+
			"every nearby slice, including a neighbourhood of an empty slice. A finite parameter cover and "+
			"complete_metric.LebesgueNumber give a subordinate interval subdivision; cover the resulting "+
			"rectangles by cubes with arbitrarily small volume overhead. The sum is bounded by interval "+
			"length times the slice budget. The hypothesis n > 0 makes the slice-volume argument apply."),
})}
