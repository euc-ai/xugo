// Two positive orthonormal frames in one chart have a special orthogonal transition.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var FrameChangeSpecialOrthogonal = frameChangeSpecialOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "FrameChangeSpecialOrthogonal",
	Key:  "prop_177e6ad6d472f22c",
	Deps: []registry.EntryLike{
		frameChangeDef,
		PositiveFrameDef,
		PositiveFrameInverse,
		vec_form.FormZeroDegree,
		vec_form.FormOrthogonalOnDef,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
		determinant.DeterminantMultiplicative,
		determinant.DeterminantTranspose,
	},
	Reading: "The comparison is within a single chart, so both frame " +
		"positivity conditions use the same coordinate orientation. The empty " +
		"matrix has determinant one, including on a nonempty zero-dimensional chart.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "vec_form_orthogonal_on⟨n⟩(«chart image»(c), " +
			"    n, " +
			"    riemannian_frame_change⟨n⟩(g, c, E, F)) ∧ " +
			"(∀y:(num → real). " +
			"    y ∈ «chart image»(c) ⇒ " +
			"    determinant(real_ring, " +
			"        n, " +
			"        (λi:num. λj:num. riemannian_frame_change⟨n⟩(g, c, E, F, i, j, y, «empty frame»))) = " +
			"    &1)",
	},
		"Using the inverse identities, H=E-transpose G F satisfies F=E H and H-transpose "+
			"H=I. Smoothness gives normalized zero-form entries; the determinants of E and F "+
			"are positive, so the orthogonal determinant of H is positive and therefore one."),
})}

var CoframeFrameChange = coframeFrameChangeThm{family.Add(registry.ProofEntry{
	Name: "CoframeFrameChange",
	Key:  "prop_ac2b1e41ab9f167",
	Deps: []registry.EntryLike{
		frameChangeDef,
		coframeDef,
		PositiveFrameInverse,
		FrameChangeSpecialOrthogonal,
		vec_form.FormMatrixProductDef,
		vec_form.WedgeDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "riemannian_coframe⟨n⟩(g, c, F) = " +
			"vec_form_matrix_product⟨n⟩(«chart image»(c), " +
			"    0, " +
			"    1, " +
			"    n, " +
			"    n, " +
			"    1, " +
			"    transpose(riemannian_frame_change⟨n⟩(g, c, E, F)), " +
			"    riemannian_coframe⟨n⟩(g, c, E))",
	},
		"The relation F=E H gives F-transpose G=H-transpose E-transpose G. "+
			"Multiplication of a zero-form and a one-form is pointwise coefficient "+
			"multiplication, yielding the coframe relation with all domain and index guards."),
})}

var ConnectionFrameChange = connectionFrameChangeThm{family.Add(registry.ProofEntry{
	Name: "ConnectionFrameChange",
	Key:  "prop_9254d1802784ecc6",
	Deps: []registry.EntryLike{
		ConnectionUnique,
		ConnectionSkew,
		ConnectionTorsionFree,
		CoframeFrameChange,
		FrameChangeSpecialOrthogonal,
		vec_form.GaugeConnectionSkew,
		vec_form.FormGaugeConnectionDef,
		vec_form.MatrixDerivativeLeibniz,
		vec_form.MatrixProductAssociative,
	},
	Reading: "The sign of H-transpose dH follows from the coframe convention " +
		"θ_F=H-transpose θ_E. No Christoffel-symbol change-of-coordinate formula is used.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "riemannian_connection⟨n⟩(g, c, F) = " +
			"vec_form_gauge_connection⟨n⟩(«chart image»(c), " +
			"    n, " +
			"    riemannian_frame_change⟨n⟩(g, c, E, F), " +
			"    riemannian_connection⟨n⟩(g, c, E))",
	},
		"The gauge-transformed connection is skew by orthogonality. Differentiate "+
			"θ_F=H-transpose θ_E and use the original torsion equation and differentiated "+
			"orthogonality to show its torsion for θ_F is zero, then apply ConnectionUnique for F."),
})}

var CurvatureFrameChange = curvatureFrameChangeThm{family.Add(registry.ProofEntry{
	Name: "CurvatureFrameChange",
	Key:  "prop_1f89076bc25a8a35",
	Deps: []registry.EntryLike{
		ConnectionFrameChange,
		ConnectionSkew,
		FrameChangeSpecialOrthogonal,
		vec_form.CurvatureGauge,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, F)) = " +
			"vec_form_matrix_conjugate⟨n⟩(«chart image»(c), " +
			"    2, " +
			"    n, " +
			"    riemannian_frame_change⟨n⟩(g, c, E, F), " +
			"    vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, E)))",
	},
		"Replace the new connection by its gauge formula. CurvatureGauge gives "+
			"exactly the orthogonal congruence of the two curvature matrices."),
})}

var CurvaturePfaffianFrameChange = curvaturePfaffianFrameChangeThm{family.Add(registry.ProofEntry{
	Name: "CurvaturePfaffianFrameChange",
	Key:  "prop_bf000eee012bad08",
	Deps: []registry.EntryLike{
		ConnectionFrameChange,
		ConnectionSkew,
		FrameChangeSpecialOrthogonal,
		vec_form.PfaffianCurvatureGauge,
		vec_form.PfaffianOdd,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E F:((num → real) → num → num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, F)",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(«chart image»(c), " +
			"    n, " +
			"    vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, F))) = " +
			"vec_form_pfaffian⟨n⟩(«chart image»(c), " +
			"    n, " +
			"    vec_form_curvature⟨n⟩(«chart image»(c), n, riemannian_connection⟨n⟩(g, c, E)))",
	},
		"For even n write n=2m and apply the determinant-one curvature Pfaffian gauge law. For "+
			"odd n both Pfaffians are zero by their definition; at n=0 both are the normalized unit."),
})}
