// Coordinate pullback and an orthogonal gauge change compare the two local connections.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var ChartFrameChangeOrthogonal = chartFrameChangeOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "ChartFrameChangeOrthogonal",
	Key:  "prop_7d369ed7ac56c29c",
	Deps: []registry.EntryLike{
		chartFrameChangeDef,
		MetricDef,
		PositiveFrameDef,
		PositiveFrameInverse,
		smooth_manifold.CompatibleTransition,
		vec_form.FormZeroDegree,
		vec_form.FormOrthogonalOnDef,
		vec_smooth.SmoothMapCompose,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
	},
	Reading: "No orientation hypothesis is needed for orthogonality. An empty " +
		"overlap carries the zero matrix as its normalized orthogonal zero-form matrix.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
		},
		Conclusion: "vec_form_orthogonal_on⟨n⟩(«overlap»(c, d), " +
			"    n, " +
			"    riemannian_chart_frame_change⟨n⟩(g, c, d, E, F))",
	},
		"The metric congruence makes J E orthonormal for the target metric, as is F. Their "+
			"overlap transition is therefore orthogonal, and its coefficients are smooth "+
			"compositions, sums and products; the definition supplies zero-form normalization."),
})}

var ChartFrameChangeDeterminant = chartFrameChangeDeterminantThm{family.Add(registry.ProofEntry{
	Name: "ChartFrameChangeDeterminant",
	Key:  "prop_a0a85e03a618d6c8",
	Deps: []registry.EntryLike{
		chartFrameChangeDef,
		ChartFrameChangeOrthogonal,
		PositiveFrameDef,
		PositiveFrameInverse,
		MetricDef,
		smooth_manifold.CompatibleTransition,
		vec_smooth.DiffeomorphismJacobianNonzero,
		determinant.DeterminantMultiplicative,
		determinant.DeterminantTranspose,
	},
	Reading: "The sign is pointwise; a disconnected overlap need not have a single orientation " +
		"sign. Between positive charts it is one, including the empty determinant in dimension zero.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real). " +
			"∀y:(num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
			"y ∈ «overlap»(c, d)",
		},
		Conclusion: "determinant(real_ring, " +
			"    n, " +
			"    (λi:num. λj:num. " +
			"        riemannian_chart_frame_change⟨n⟩(g, c, d, E, F, i, j, y, «empty frame»))) = " +
			"COND(&0 < vec_jacobian_determinant⟨n⟩(«transition»(c, d), y), &1, -&1)",
	},
		"The identity F=J E H and positivity of det(E) and det(F) make the sign "+
			"of det(H) equal to that of det(J). Orthogonality makes det(H) equal to "+
			"plus or minus one, while the coordinate diffeomorphism excludes det(J)=0."),
})}

var CoframeChartChange = coframeChartChangeThm{family.Add(registry.ProofEntry{
	Name: "CoframeChartChange",
	Key:  "prop_a293fd11c2a33904",
	Deps: []registry.EntryLike{
		chartFrameChangeDef,
		coframeDef,
		MetricDef,
		PositiveFrameInverse,
		CoframeForm,
		vec_form.FormMatrixPullbackDef,
		vec_form.PullbackDef,
		vec_form.WedgeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
		},
		Conclusion: "vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"    1, " +
			"    n, " +
			"    1, " +
			"    «transition»(c, d), " +
			"    riemannian_coframe⟨n⟩(g, d, F)) = " +
			"vec_form_matrix_product⟨n⟩(«overlap»(c, d), " +
			"    0, " +
			"    1, " +
			"    n, " +
			"    n, " +
			"    1, " +
			"    transpose(riemannian_chart_frame_change⟨n⟩(g, c, d, E, F)), " +
			"    vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"        1, " +
			"        n, " +
			"        1, " +
			"        (λy:(num → real). y), " +
			"        riemannian_coframe⟨n⟩(g, c, E)))",
	},
		"The pulled-back target coefficient matrix is F-transpose G_d J. Substituting H=(J "+
			"E)-transpose G_d F and E(E-transpose G_c)=I shows that this equals H-transpose E-transpose "+
			"G_c; the normalized zero-form product gives the whole matrix-of-forms equality."),
})}

var ConnectionChartChange = connectionChartChangeThm{family.Add(registry.ProofEntry{
	Name: "ConnectionChartChange",
	Key:  "prop_e7fb5d51cb667f2a",
	Deps: []registry.EntryLike{
		ChartFrameChangeOrthogonal,
		CoframeChartChange,
		PositiveFrameRestrict,
		CoframeRestrict,
		ConnectionRestrict,
		ConnectionUnique,
		ConnectionSkew,
		ConnectionTorsionFree,
		vec_form.GaugeConnectionSkew,
		vec_form.MatrixPullbackProduct,
		vec_form.MatrixPullbackDerivative,
		vec_form.MatrixDerivativeLeibniz,
		vec_form.MatrixProductAssociative,
	},
	Reading: "This also holds for orientation-reversing coordinate changes. Uniqueness " +
		"is applied to the positive source frame after gauging back, so it does not assume " +
		"that the transported target frame is positive in the source coordinates.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
		},
		Conclusion: "vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"    1, " +
			"    n, " +
			"    n, " +
			"    «transition»(c, d), " +
			"    riemannian_connection⟨n⟩(g, d, F)) = " +
			"vec_form_gauge_connection⟨n⟩(«overlap»(c, d), " +
			"    n, " +
			"    riemannian_chart_frame_change⟨n⟩(g, c, d, E, F), " +
			"    vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"        1, " +
			"        n, " +
			"        n, " +
			"        (λy:(num → real). y), " +
			"        riemannian_connection⟨n⟩(g, c, E)))",
	},
		"Pull back the target torsion equation, then gauge that connection back by "+
			"H-transpose to the restricted source coframe. It is skew and torsion-free there, "+
			"so ConnectionUnique in the restricted source chart identifies it with the source "+
			"connection; invert the orthogonal gauge change to obtain the displayed formula."),
})}

var CurvatureChartChange = curvatureChartChangeThm{family.Add(registry.ProofEntry{
	Name: "CurvatureChartChange",
	Key:  "prop_768361c28f1c9d26",
	Deps: []registry.EntryLike{
		ConnectionChartChange,
		ChartFrameChangeOrthogonal,
		ConnectionSkew,
		vec_form.CurvaturePullback,
		vec_form.CurvatureGauge,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c d:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, d, F)",
		},
		Conclusion: "vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"    2, " +
			"    n, " +
			"    n, " +
			"    «transition»(c, d), " +
			"    vec_form_curvature⟨n⟩(«chart image»(d), n, riemannian_connection⟨n⟩(g, d, F))) = " +
			"vec_form_matrix_conjugate⟨n⟩(«overlap»(c, d), " +
			"    2, " +
			"    n, " +
			"    riemannian_chart_frame_change⟨n⟩(g, c, d, E, F), " +
			"    vec_form_matrix_pullback⟨n, n⟩(«overlap»(c, d), " +
			"        2, " +
			"        n, " +
			"        n, " +
			"        (λy:(num → real). y), " +
			"        vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, E))))",
	},
		"Curvature commutes with both coordinate pullback and identity pullback to the overlap. "+
			"Substitute ConnectionChartChange and apply the Euclidean orthogonal gauge law on that overlap."),
})}
