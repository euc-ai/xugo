// Orthogonal gauge transformations act on curvature by congruence.
// Determinant one preserves its Pfaffian, whose exterior derivative vanishes.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var GaugeConnectionSkew = gaugeConnectionSkewThm{family.Add(registry.ProofEntry{
	Name: "GaugeConnectionSkew",
	Key:  "prop_827e873ff19fe060",
	Deps: []registry.EntryLike{
		FormGaugeConnectionDef,
		FormOrthogonalOnDef,
		MatrixProductForm,
		MatrixDerivativeForm,
		MatrixDerivativeLeibniz,
		MatrixTransposeProduct,
		FormModule,
	},
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀H A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_orthogonal_on⟨n⟩(U, r, H)",
			"vec_form_skew_matrix_on⟨n⟩(U, 1, r, A)",
		},
		Conclusion: "vec_form_skew_matrix_on⟨n⟩(U, 1, r, vec_form_gauge_connection⟨n⟩(U, r, H, A))",
	},
		"Conjugation by zero-form matrices preserves skew symmetry. Differentiate "+
			"H-transpose H = I on U to obtain skew symmetry of H-transpose dH; "+
			"normalize outside U and add the two skew one-form matrices."),
})}

var CurvatureGauge = curvatureGaugeThm{family.Add(registry.ProofEntry{
	Name: "CurvatureGauge",
	Key:  "prop_4c0acd6c679ddabc",
	Deps: []registry.EntryLike{
		FormGaugeConnectionDef,
		FormOrthogonalOnDef,
		FormCurvatureDef,
		FormMatrixConjugateDef,
		MatrixDerivativeLeibniz,
		MatrixDerivativeSquareZero,
		MatrixProductAssociative,
		WedgeUnit,
	},
	Reading: "A need not be skew. Degree-one factors must keep their graded signs during " +
		"cancellation; orthogonality is required on U only, where the differential calculation is local.",
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀H A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_orthogonal_on⟨n⟩(U, r, H)", "vec_form_matrix_on⟨n⟩(U, 1, r, r, A)"},
		Conclusion: "vec_form_curvature⟨n⟩(U, r, vec_form_gauge_connection⟨n⟩(U, r, H, A)) = " +
			"vec_form_matrix_conjugate⟨n⟩(U, 2, r, H, vec_form_curvature⟨n⟩(U, r, A))",
	},
		"A square orthogonal real matrix has both H-transpose H = I and H H-transpose "+
			"= I on U. Expand d(H-transpose A H + H-transpose dH) and its square, use the "+
			"differentiated orthogonality identities, and cancel terms with the graded "+
			"product rule; the surviving terms are H-transpose (dA + A∧A) H."),
})}

var PfaffianCurvatureGauge = pfaffianCurvatureGaugeThm{family.Add(registry.ProofEntry{
	Name: "PfaffianCurvatureGauge",
	Key:  "prop_b5c4f863b66b1744",
	Deps: []registry.EntryLike{
		CurvatureGauge,
		CurvatureSkew,
		PfaffianOrientedFrame,
		FormOrthogonalOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀n m:num. " +
			"∀U:set(num → real). " +
			"∀H A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_orthogonal_on⟨n⟩(U, 2 * m, H)",
			"vec_form_skew_matrix_on⟨n⟩(U, 1, 2 * m, A)",
			"∀x:(num → real). " +
				"    x ∈ U ⇒ determinant(real_ring, 2 * m, (λi:num. λj:num. H(i, j, x, «empty frame»))) = &1",
		},
		Conclusion: "vec_form_pfaffian⟨n⟩(U, " +
			"    2 * m, " +
			"    vec_form_curvature⟨n⟩(U, 2 * m, vec_form_gauge_connection⟨n⟩(U, 2 * m, H, A))) = " +
			"vec_form_pfaffian⟨n⟩(U, 2 * m, vec_form_curvature⟨n⟩(U, 2 * m, A))",
	},
		"CurvatureGauge gives the orthogonal congruence of curvature matrices. CurvatureSkew "+
			"supplies the alternating input and PfaffianOrientedFrame removes the determinant-one factor."),
})}

var PfaffianCurvatureClosed = pfaffianCurvatureClosedThm{family.Add(registry.ProofEntry{
	Name: "PfaffianCurvatureClosed",
	Key:  "prop_b76dd37339c3dfcb",
	Deps: []registry.EntryLike{
		CurvatureSkew,
		CurvatureBianchi,
		PfaffianHomogeneous,
		PfaffianOdd,
		PfaffianEmpty,
		FormPfaffianDef,
		ExteriorDerivativeLeibniz,
		ExteriorDerivativeLinear,
		WedgeGradedCommutative,
		PfaffianCongruence,
	},
	Reading: "Closedness is an identity in the full graded algebra, not a derivation law inside " +
		"the even-form ring: dΩ has degree three and A has degree one. No dimension equality or " +
		"nonempty-domain assumption is needed; when r exceeds n the form already vanishes.",
	Build: family.Card(Statement{
		Binders: "∀n r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_skew_matrix_on⟨n⟩(U, 1, r, A)"},
		Conclusion: "vec_exterior_derivative⟨n⟩(U, " +
			"    r, " +
			"    vec_form_pfaffian⟨n⟩(U, r, vec_form_curvature⟨n⟩(U, r, A))) = " +
			"«zero»",
	},
		"Differentiate the finite matching polynomial using the graded Leibniz rule, then "+
			"substitute Bianchi, dΩ = Ω∧A − A∧Ω. The resulting terms cancel by the "+
			"infinitesimal skew-congruence identity of the Pfaffian: the trace of the skew "+
			"connection is zero; commuting a one-form past a two-form introduces no sign. Odd "+
			"order is the zero Pfaffian and order zero is the locally constant normalized unit."),
})}
