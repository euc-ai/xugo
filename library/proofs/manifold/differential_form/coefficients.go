// Compact support inside one chart makes every fixed-frame coefficient globally smooth.

package differential_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ChartCoefficientCompact = chartCoefficientCompactThm{family.Add(registry.ProofEntry{
	Name: "ChartCoefficientCompact",
	Key:  "prop_6a19548867237ee0",
	Reading: "This applies in every degree and to arbitrary fixed matrices, including " +
		"unpadded tails. Compact support must lie inside the chart domain; compactness " +
		"alone does not justify smooth zero extension across that chart boundary.",
	Deps: []registry.EntryLike{
		FormOnDef,
		SupportDef,
		SupportCoordinate,
		vec_form.FormOnDef,
		vec_form.FormIndicesDef,
		vec_smooth.SmoothLocal,
		vec_smooth.SmoothSum,
		smooth_manifold.ChartDef,
		continuous.ImageCompact,
		compact.CompactClosed,
		compact.CompactInSubtopology,
		euclidean_topology.EuclideanHausdorff,
	},
	Build: family.Card(Statement{
		Binders: "∀n k:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀ω:(prod(set(A), A → num → real) → (num → real) → (num → num → real) → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀P:(num → num → real).",
		Hypotheses: []string{
			"manifold_form_on⟨n⟩(T, 𝒜, k, ω)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"compact_in(T, manifold_form_support⟨n⟩(T, 𝒜, ω))",
			"manifold_form_support⟨n⟩(T, 𝒜, ω) ⊆ fst(c)",
		},
		Conclusion: "vec_smooth_on⟨n⟩({y:(num → real) | vec⟨n⟩(y)}, λy:(num → real). ω(c, y, P)) ∧ " +
			"vec_compactly_supported_in⟨n⟩(«chart image»(c), λy:(num → real). ω(c, y, P))",
	},
		"For fixed P the finite coordinate-minor expansion is a finite real linear combination "+
			"of smooth coefficient functions on the chart image. The chart image of the compact "+
			"base support is compact and lies inside that open image; outside it all values vanish. "+
			"Its open complement and the chart image cover Euclidean space, so SmoothLocal makes "+
			"the normalized coefficient globally smooth and the compact image witnesses its support."),
})}
