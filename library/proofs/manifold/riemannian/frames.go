// Smooth Gram-Schmidt gives positive orthonormal frames and their dual expansions.

package riemannian

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_form"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PositiveFrameExists = positiveFrameExistsThm{family.Add(registry.ProofEntry{
	Name: "PositiveFrameExists",
	Key:  "prop_7a8ee4ca92b30515",
	Deps: []registry.EntryLike{
		MetricDef,
		PositiveFrameDef,
		vec_smooth.SmoothSqrt,
		vec_smooth.SmoothReciprocal,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothAdd,
		determinant.DeterminantTriangular,
	},
	Reading: "The frame exists on the whole coordinate image; no connectedness or " +
		"contractibility of that image is needed. Positivity is relative to this chart, not a " +
		"choice of global manifold orientation. At dimension zero the empty determinant is one.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real).",
		Hypotheses: []string{"riemannian_metric⟨n⟩(T, 𝒜, g)", "compatible_chart⟨n⟩(T, 𝒜, c)"},
		Conclusion: "∃E:((num → real) → num → num → real). riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
	},
		"Apply Gram-Schmidt to the ordered coordinate vectors with the positive "+
			"coordinate metric. Each residual has strictly positive squared length, so square "+
			"root and reciprocal are smooth; the resulting triangular frame has positive "+
			"diagonal and hence positive determinant, and is set to zero off the chart image."),
})}

var PositiveFrameInverse = positiveFrameInverseThm{family.Add(registry.ProofEntry{
	Name: "PositiveFrameInverse",
	Key:  "prop_71c8d7c064921f44",
	Deps: []registry.EntryLike{
		PositiveFrameDef,
		determinant.MatrixInverse,
		determinant.DeterminantMultiplicative,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀y:(num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)", "y ∈ «chart image»(c)"},
		Conclusion: "matrix_product(real_ring, n, «dual matrix»(y), E(y)) = " +
			"matrix_identity(real_ring, n) ∧ " +
			"matrix_product(real_ring, n, E(y), «dual matrix»(y)) = matrix_identity(real_ring, n)",
	},
		"The defining orthonormality equation says E-transpose G is a left "+
			"inverse. Since E is square with positive determinant, its inverse exists "+
			"and this left inverse equals it, giving the right inverse as well."),
})}

var CoframeForm = coframeFormThm{family.Add(registry.ProofEntry{
	Name: "CoframeForm",
	Key:  "prop_ea0d2aed4b8a143f",
	Deps: []registry.EntryLike{
		coframeDef,
		PositiveFrameDef,
		MetricDef,
		vec_form.FormOnDef,
		vec_form.FormMatrixOnDef,
		vec_smooth.SmoothSum,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real).",
		Hypotheses: []string{"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)"},
		Conclusion: "vec_form_matrix_on⟨n⟩(«chart image»(c), 1, n, 1, riemannian_coframe⟨n⟩(g, c, E))",
	},
		"Every coframe entry is a smooth linear combination of coordinate "+
			"one-forms, with coefficients E-transpose G. The explicit row, column "+
			"and domain guards give the matrix padding and form normalization."),
})}

var CoframeDual = coframeDualThm{family.Add(registry.ProofEntry{
	Name: "CoframeDual",
	Key:  "prop_8b872c460722ed22",
	Deps: []registry.EntryLike{coframeDef, PositiveFrameInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀y:(num → real). " +
			"∀a b:num.",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"y ∈ «chart image»(c)",
			"a < n",
			"b < n",
		},
		Conclusion: "riemannian_coframe⟨n⟩(g, c, E, a, 0, y, «frame column»(y, b)) = COND(a = b, &1, &0)",
	},
		"Evaluation on the b-th frame column is entry (a,b) "+
			"of E-transpose G E, hence the Kronecker delta."),
})}

var CoframeExpansion = coframeExpansionThm{family.Add(registry.ProofEntry{
	Name: "CoframeExpansion",
	Key:  "prop_d4a5e0d2c125d1b7",
	Deps: []registry.EntryLike{coframeDef, PositiveFrameInverse},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀y v:(num → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"y ∈ «chart image»(c)",
			"vec⟨n⟩(v)",
		},
		Conclusion: "matrix_act⟨n⟩(E(y), " +
			"    (λa:num. " +
			"        COND(a < n, " +
			"            riemannian_coframe⟨n⟩(g, c, E, a, 0, y, (λi:num. λj:num. COND(j = 0, v(i), &0))), " +
			"            &0))) = " +
			"v",
	},
		"The coframe coefficients form (E-transpose G)v. Multiplying by E "+
			"gives v by the right-inverse identity; the padded vector hypothesis "+
			"supplies literal equality also in the inactive coordinates."),
})}

var CoframeTwoFormExpansion = coframeTwoFormExpansionThm{family.Add(registry.ProofEntry{
	Name: "CoframeTwoFormExpansion",
	Key:  "prop_9a711ae8bc5cf1dd",
	Deps: []registry.EntryLike{
		CoframeExpansion,
		CoframeDual,
		CoframeForm,
		vec_form.FormOnDef,
		vec_form.WedgeDef,
	},
	Reading: "The factor one half is required because both index orders are summed. In dimensions " +
		"zero and one every two-form is zero, and arbitrary unused frame columns do not contribute.",
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀g:(prod(set(A), A → num → real) → (num → real) → num → num → real). " +
			"∀c:prod(set(A), A → num → real). " +
			"∀E:((num → real) → num → num → real). " +
			"∀ω:((num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"riemannian_positive_frame⟨n⟩(T, 𝒜, g, c, E)",
			"vec_form_on⟨n⟩(«chart image»(c), 2, ω)",
		},
		Conclusion: "ω = " +
			"(λy:(num → real). λP:(num → num → real). " +
			"    (&1 / &2) * " +
			"    (Σ_{a<n} Σ_{b<n} ω(y, «frame pair»(y, a, b)) * " +
			"        vec_form_wedge⟨n⟩(«chart image»(c), " +
			"            1, " +
			"            1, " +
			"            riemannian_coframe⟨n⟩(g, c, E, a, 0), " +
			"            riemannian_coframe⟨n⟩(g, c, E, b, 0), " +
			"            y, " +
			"            P)))",
	},
		"Expand each input vector in the frame and use bilinearity and alternation of ω. "+
			"The ordered pair sum counts each exterior basis contribution twice, so its factor "+
			"one half matches the shuffle wedge convention; both sides vanish outside the image."),
})}
