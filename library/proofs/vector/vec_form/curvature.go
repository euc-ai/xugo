// Curvature of a matrix of one-forms and its differential identities.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var CurvatureForm = curvatureFormThm{family.Add(registry.ProofEntry{
	Name: "CurvatureForm",
	Key:  "prop_1116590408a65a80",
	Deps: []registry.EntryLike{
		FormCurvatureDef,
		MatrixDerivativeForm,
		MatrixProductForm,
		FormModule,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, 1, r, r, A)"},
		Conclusion: "vec_form_matrix_on⟨n⟩(U, 2, r, r, vec_form_curvature⟨n⟩(U, r, A))",
	},
		"Both dA and A∧A have degree two and the same square shape by "+
			"MatrixDerivativeForm and MatrixProductForm. Pointwise addition "+
			"stays in each degree-two form module and preserves zero padding."),
})}

var CurvatureSkew = curvatureSkewThm{family.Add(registry.ProofEntry{
	Name: "CurvatureSkew",
	Key:  "prop_82985edf3ded8e19",
	Deps: []registry.EntryLike{
		CurvatureForm,
		FormSkewMatrixOnDef,
		FormMatrixDerivativeDef,
		MatrixTransposeProduct,
		ExteriorDerivativeLinear,
		WedgeBilinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_skew_matrix_on⟨n⟩(U, 1, r, A)"},
		Conclusion: "vec_form_skew_matrix_on⟨n⟩(U, 2, r, vec_form_curvature⟨n⟩(U, r, A))",
	},
		"Entrywise differentiation commutes with transpose and negation, so dA is skew. "+
			"MatrixTransposeProduct in degrees one and one gives (A∧A)ᵀ = −Aᵀ∧Aᵀ = −A∧A; adding the "+
			"two skew matrices yields the claim, with real coefficients forcing the diagonal to vanish."),
})}

var CurvatureBianchi = curvatureBianchiThm{family.Add(registry.ProofEntry{
	Name: "CurvatureBianchi",
	Key:  "prop_2b58a85e42e19229",
	Reading: "Bianchi holds for every square matrix of one-forms; skew symmetry " +
		"is unnecessary. The matrix factors retain their order: dF + A∧F − F∧A = 0.",
	Deps: []registry.EntryLike{
		CurvatureForm,
		MatrixDerivativeSquareZero,
		MatrixDerivativeLeibniz,
		MatrixProductAssociative,
		WedgeBilinear,
		ExteriorDerivativeLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, 1, r, r, A)"},
		Conclusion: "(λi:num. λj:num. λx:(num → real). λP:(num → num → real). " +
			"    vec_form_matrix_derivative⟨n⟩(U, 2, r, r, «curvature», i, j, x, P) + " +
			"    vec_form_matrix_product⟨n⟩(U, 1, 2, r, r, r, A, «curvature», i, j, x, P) - " +
			"    vec_form_matrix_product⟨n⟩(U, 2, 1, r, r, r, «curvature», A, i, j, x, P)) = " +
			"«zero matrix»",
		Abbrev: Abbrev{{Name: "curvature", Text: "vec_form_curvature⟨n⟩(U, r, A)"}},
	},
		"Expand F = dA+A∧A. The square-zero and graded Leibniz laws give dF "+
			"= dA∧A−A∧dA; expanding A∧F−F∧A cancels these terms, and "+
			"associativity cancels the two cubic terms. No factors are commuted."),
})}

var CurvaturePullback = curvaturePullbackThm{family.Add(registry.ProofEntry{
	Name: "CurvaturePullback",
	Key:  "prop_b1165fc9f0902064",
	Deps: []registry.EntryLike{
		FormCurvatureDef,
		MatrixPullbackForm,
		MatrixPullbackDerivative,
		MatrixPullbackProduct,
		PullbackLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n m r:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_matrix_on⟨m⟩(V, 1, r, r, A)",
		},
		Conclusion: "vec_form_curvature⟨n⟩(U, r, vec_form_matrix_pullback⟨n, m⟩(U, 1, r, r, f, A)) = " +
			"vec_form_matrix_pullback⟨n, m⟩(U, 2, r, r, f, vec_form_curvature⟨m⟩(V, r, A))",
	},
		"Pullback commutes with d, with the matrix wedge product and with entrywise "+
			"addition. Apply MatrixPullbackDerivative and MatrixPullbackProduct to the two "+
			"terms of the curvature definition, retaining the open-domain and image guards."),
})}
