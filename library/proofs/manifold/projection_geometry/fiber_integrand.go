package projection_geometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/differential_form"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

// FiberIntegrandCompact — in a framed chart of the total space, the integrand of the fibre
// integral over a base point is smooth, continuous and compactly supported in the 2r fibre
// coordinates.
var FiberIntegrandCompact = fiberIntegrandCompactThm{family.Add(registry.ProofEntry{
	Name: "FiberIntegrandCompact",
	Key:  "prop_74432d65f9448533",
	Deps: []registry.EntryLike{
		TotalManifold,
		smooth_manifold.AtlasMemberCompatible,
		vec_smooth.SmoothCompose,
		compact.FiniteCompact,
		continuous.ImageCompact,
		differential_form.SupportCoordinate,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀r:num. " +
			"∀P:prod(num, A → num → num → complex). " +
			"∀k:num. " +
			"∀ω:(prod(set(prod(A, num → complex)), prod(A, num → complex) → num → real) → " +
			"        (num → real) → " +
			"        (num → num → real) → " +
			"        real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀F:(A → num → num → complex). " +
			"∀y:(num → real). " +
			"∀V:(num → num → real).",
		Hypotheses: []string{
			"smooth_projection_bundle(n, fst(P), T, 𝒜, snd(P))",
			"∀x:A. x ∈ ⋃T ⇒ projection_rank(P, x) = r",
			"manifold_form_on⟨n + 2 * r⟩(projection_total_topology(T, P), " +
				"    projection_total_atlas(n, r, T, 𝒜, P), " +
				"    k, " +
				"    ω)",
			"projection_fiber_proper(n, r, T, 𝒜, P, ω)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"smooth_projection_frame(n, r, T, 𝒜, P, fst(c), F)",
			"y ∈ image(snd(c), fst(c))",
		},
		Conclusion: "vec_smooth_on⟨2 * r⟩({u:num → real | vec⟨2 * r⟩(&0, u)}, «integrand») ∧ " +
			"continuous_map(euclidean_topology(2 * r), real_topology, «integrand») ∧ " +
			"vec_compactly_supported_in⟨2 * r⟩({u:num → real | vec⟨2 * r⟩(&0, u)}, «integrand»)",
		Abbrev: Abbrev{
			{Name: "integrand", Text: "λz:(num → real). " +
				"    ω(projection_total_chart(n, r, T, 𝒜, P, c, F), " +
				"        λi:num. COND(i < n, y(i), COND(i < n + 2 * r, z(i - n), &0)), " +
				"        V)"},
		},
	},
		"The chart built from c and F is a compatible chart of the total manifold "+
			"(TotalManifold, AtlasMemberCompatible), and since F is a unitary frame its image holds "+
			"y followed by every z. The integrand is ω's chart coefficient composed with the smooth "+
			"map z ↦ (y, z), smooth by vec_form_on and SmoothCompose, hence continuous. Fibre "+
			"properness over the compact set holding the point of c at y (FiniteCompact) makes ω's "+
			"support over it compact; its image in the chart and then in the fibre coordinates "+
			"(ImageCompact) is a compact set off which the integrand vanishes (SupportCoordinate)."),
	Reading: "The frame is load-bearing: with orthonormal columns and FF* = P, " +
		"every padded fibre coordinate is a chart image, so the integrand is the " +
		"chart coefficient on all of ℝ^{2r}. An arbitrary V is harmless, since a " +
		"form pins its value on the whole matrix; at r = 0 the fibre is the point {0}.",
})}
