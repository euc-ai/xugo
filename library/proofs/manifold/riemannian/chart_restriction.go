// Metric and connection expressions restrict with the chart domain and its normalized frame.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var MetricAtlasInvariant = metricAtlasInvariantThm{family.Add(registry.ProofEntry{
	Name: "MetricAtlasInvariant",
	Key:  "prop_8972cab58388c9fd",
	Deps: []registry.EntryLike{MetricDef},
	Reading: "Equality of compatible-chart predicates alone does not assert that the " +
		"second atlas covers the manifold. Both smooth manifold hypotheses are retained.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀ℬ:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"smooth_manifold⟨n⟩(T, ℬ)",
			"∀c:prod(set(A), A → num → real). compatible_chart⟨n⟩(T, 𝒜, c) ⇔ compatible_chart⟨n⟩(T, ℬ, c)",
		},
		Conclusion: "riemannian_metric⟨n⟩(T, 𝒜, g) ⇔ riemannian_metric⟨n⟩(T, ℬ, g)",
	},
		"The two atlases test the same normalized chart family, coordinate smoothness, "+
			"positivity and Jacobian congruence equations. Both underlying manifold "+
			"hypotheses are supplied, so unfolding the metric predicate gives the equivalence."),
})}

var MetricChartRestrict = metricChartRestrictThm{family.Add(registry.ProofEntry{
	Name: "MetricChartRestrict",
	Key:  "prop_391ad0baec84c512",
	Deps: []registry.EntryLike{
		MetricDef,
		smooth_manifold.ChartRestrict,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.PartialDerivativeLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀V:set(A).",
		Hypotheses: []string{
			"riemannian_metric⟨n⟩(T, 𝒜, g)",
			"compatible_chart⟨n⟩(T, 𝒜, c)",
			"V ∈ T",
			"V ⊆ fst(c)",
		},
		Conclusion: "g((V, snd(c))) = normalize_on(image(snd(c), V), «zero real matrix», g(c))",
	},
		"The restricted chart is compatible and its transition to c is the identity "+
			"on its image. Metric compatibility there reduces to equality because the "+
			"Jacobian is the identity; both sides are zero away from the restricted image."),
})}

var PositiveFrameRestrict = positiveFrameRestrictThm{family.Add(registry.ProofEntry{
	Name: "PositiveFrameRestrict",
	Key:  "prop_890bf76e782df6c7",
	Deps: []registry.EntryLike{
		PositiveFrameDef,
		MetricChartRestrict,
		smooth_manifold.ChartRestrict,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.SmoothSubset,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀V:set(A).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "V ∈ T", "V ⊆ fst(c)"},
		Conclusion: "riemannian_positive_frame⟨n⟩(T, " +
			"    𝒜, " +
			"    g, " +
			"    (V, snd(c)), " +
			"    normalize_on(image(snd(c), V), «zero real matrix», E))",
	},
		"Restrict the metric and frame coefficients to the smaller open image. They agree "+
			"locally with the original coefficients, so smoothness and the pointwise orthonormality "+
			"and positive determinant remain; normalize the frame outside that image."),
})}

var CoframeRestrict = coframeRestrictThm{family.Add(registry.ProofEntry{
	Name: "CoframeRestrict",
	Key:  "prop_545c3fa42db345be",
	Deps: []registry.EntryLike{
		coframeDef,
		MetricChartRestrict,
		PositiveFrameRestrict,
		CoframeForm,
		vec_form.FormMatrixPullbackDef,
		vec_form.PullbackDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀V:set(A).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "V ∈ T", "V ⊆ fst(c)"},
		Conclusion: "riemannian_coframe⟨n⟩(g, " +
			"    (V, snd(c)), " +
			"    normalize_on(image(snd(c), V), «zero real matrix», E)) = " +
			"vec_form_matrix_pullback⟨n, n⟩(image(snd(c), V), " +
			"    1, " +
			"    n, " +
			"    1, " +
			"    (λy:(num → real). y), " +
			"    riemannian_coframe⟨n⟩(g, c, E))",
	},
		"On the restricted image the metric-dual coefficient matrices agree, "+
			"and pullback by the identity leaves the active form column unchanged. "+
			"All remaining domain and matrix-index arguments are zero on both sides."),
})}

var ConnectionRestrict = connectionRestrictThm{family.Add(registry.ProofEntry{
	Name: "ConnectionRestrict",
	Key:  "prop_24e1b23be0212430",
	Deps: []registry.EntryLike{
		PositiveFrameRestrict,
		CoframeRestrict,
		ConnectionUnique,
		ConnectionSkew,
		ConnectionTorsionFree,
		vec_form.MatrixPullbackForm,
		vec_form.MatrixPullbackProduct,
		vec_form.MatrixPullbackDerivative,
		vec_form.PullbackLinear,
	},
	Reading: "The connection is normalized to the smaller image. Equality with " +
		"the unrestricted original connection outside that image is not asserted.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀V:set(A).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "V ∈ T", "V ⊆ fst(c)"},
		Conclusion: "riemannian_connection⟨n⟩(g, " +
			"    (V, snd(c)), " +
			"    normalize_on(image(snd(c), V), «zero real matrix», E)) = " +
			"vec_form_matrix_pullback⟨n, n⟩(image(snd(c), V), " +
			"    1, " +
			"    n, " +
			"    n, " +
			"    (λy:(num → real). y), " +
			"    riemannian_connection⟨n⟩(g, c, E))",
	},
		"Identity pullback gives a skew connection on the restricted image and carries the "+
			"original torsion equation to that of the restricted coframe. ConnectionUnique for "+
			"the restricted chart identifies it with its explicit connection."),
})}
