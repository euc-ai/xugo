// Matrix-valued form calculus keeps the matrix contraction separate
// from the graded product of its scalar form entries.

package vec_form

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

var MatrixProductForm = matrixProductFormThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductForm",
	Key:  "prop_cf54cd0079fd9572",
	Deps: []registry.EntryLike{FormMatrixOnDef, FormMatrixProductDef, WedgeForm, FormModule},
	Build: family.Card(Statement{
		Binders: "∀n p q r s t:num. " +
			"∀U:set(num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_matrix_on⟨n⟩(U, p, r, s, A)",
			"vec_form_matrix_on⟨n⟩(U, q, s, t, B)",
		},
		Conclusion: "vec_form_matrix_on⟨n⟩(U, " +
			"    p + q, " +
			"    r, " +
			"    t, " +
			"    vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B))",
	},
		"Each active entry is a finite sum of degree-(p+q) wedges, so WedgeForm and "+
			"FormModule give its form carrier. The output guards give rectangular zero "+
			"padding; an empty contracted dimension gives the zero matrix on the open U."),
})}

var MatrixProductAssociative = matrixProductAssociativeThm{family.Add(registry.ProofEntry{
	Name: "MatrixProductAssociative",
	Key:  "prop_db36dfb6cea2b8af",
	Deps: []registry.EntryLike{
		MatrixProductForm,
		FormMatrixProductDef,
		WedgeAssociative,
		WedgeBilinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q k r s t u:num. " +
			"∀U:set(num → real). " +
			"∀A B C:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_matrix_on⟨n⟩(U, p, r, s, A)",
			"vec_form_matrix_on⟨n⟩(U, q, s, t, B)",
			"vec_form_matrix_on⟨n⟩(U, k, t, u, C)",
		},
		Conclusion: "vec_form_matrix_product⟨n⟩(U, " +
			"    p + q, " +
			"    k, " +
			"    r, " +
			"    t, " +
			"    u, " +
			"    vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B), " +
			"    C) = " +
			"vec_form_matrix_product⟨n⟩(U, " +
			"    p, " +
			"    q + k, " +
			"    r, " +
			"    s, " +
			"    u, " +
			"    A, " +
			"    vec_form_matrix_product⟨n⟩(U, q, k, s, t, u, B, C))",
	},
		"Expand the two finite contractions and interchange their summation order. "+
			"WedgeBilinear distributes the sums and WedgeAssociative identifies each "+
			"triple product, with the same row and column guards on both sides."),
})}

var MatrixDerivativeForm = matrixDerivativeFormThm{family.Add(registry.ProofEntry{
	Name: "MatrixDerivativeForm",
	Key:  "prop_b34b477589eb7415",
	Deps: []registry.EntryLike{FormMatrixDerivativeDef, ExteriorDerivativeForm},
	Build: family.Card(Statement{
		Binders: "∀n k r s:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, k, r, s, A)"},
		Conclusion: "vec_form_matrix_on⟨n⟩(U, k + 1, r, s, vec_form_matrix_derivative⟨n⟩(U, k, r, s, A))",
	},
		"Apply ExteriorDerivativeForm at each active entry. The defining index guards give "+
			"the zero form in every inactive entry and preserve the same rectangular shape."),
})}

var MatrixDerivativeSquareZero = matrixDerivativeSquareZeroThm{family.Add(registry.ProofEntry{
	Name: "MatrixDerivativeSquareZero",
	Key:  "prop_5c6af4758f12538c",
	Deps: []registry.EntryLike{
		MatrixDerivativeForm,
		FormMatrixDerivativeDef,
		ExteriorDerivativeSquareZero,
	},
	Build: family.Card(Statement{
		Binders: "∀n k r s:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, k, r, s, A)"},
		Conclusion: "vec_form_matrix_derivative⟨n⟩(U, " +
			"    k + 1, " +
			"    r, " +
			"    s, " +
			"    vec_form_matrix_derivative⟨n⟩(U, k, r, s, A)) = " +
			"«zero matrix»",
	},
		"Each active entry is d² of its scalar form and vanishes by ExteriorDerivativeSquareZero. "+
			"Inactive entries vanish by the outer guards, so this is equality of total matrices of forms."),
})}

var MatrixDerivativeLeibniz = matrixDerivativeLeibnizThm{family.Add(registry.ProofEntry{
	Name: "MatrixDerivativeLeibniz",
	Key:  "prop_f582415c7537d2f6",
	Deps: []registry.EntryLike{
		MatrixProductForm,
		MatrixDerivativeForm,
		ExteriorDerivativeLinear,
		ExteriorDerivativeLeibniz,
	},
	Build: family.Card(Statement{
		Binders: "∀n p q r s t:num. " +
			"∀U:set(num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_matrix_on⟨n⟩(U, p, r, s, A)",
			"vec_form_matrix_on⟨n⟩(U, q, s, t, B)",
		},
		Conclusion: "vec_form_matrix_derivative⟨n⟩(U, " +
			"    p + q, " +
			"    r, " +
			"    t, " +
			"    vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B)) = " +
			"(λi:num. λj:num. λx:(num → real). λP:(num → num → real). " +
			"    vec_form_matrix_product⟨n⟩(U, " +
			"        p + 1, " +
			"        q, " +
			"        r, " +
			"        s, " +
			"        t, " +
			"        vec_form_matrix_derivative⟨n⟩(U, p, r, s, A), " +
			"        B, " +
			"        i, " +
			"        j, " +
			"        x, " +
			"        P) + " +
			"    (-&1)^p * " +
			"    vec_form_matrix_product⟨n⟩(U, " +
			"        p, " +
			"        q + 1, " +
			"        r, " +
			"        s, " +
			"        t, " +
			"        A, " +
			"        vec_form_matrix_derivative⟨n⟩(U, q, s, t, B), " +
			"        i, " +
			"        j, " +
			"        x, " +
			"        P))",
	},
		"ExteriorDerivativeLinear moves d through the finite entry sum, and "+
			"ExteriorDerivativeLeibniz supplies the sign (-1)^p on every term differentiating "+
			"B. The matrix index order is unchanged; no commutation of matrices is used."),
})}

var MatrixPullbackForm = matrixPullbackFormThm{family.Add(registry.ProofEntry{
	Name: "MatrixPullbackForm",
	Key:  "prop_902d81bf705ff562",
	Deps: []registry.EntryLike{FormMatrixPullbackDef, PullbackForm},
	Build: family.Card(Statement{
		Binders: "∀n m k r s:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_matrix_on⟨m⟩(V, k, r, s, A)",
		},
		Conclusion: "vec_form_matrix_on⟨n⟩(U, k, r, s, vec_form_matrix_pullback⟨n, m⟩(U, k, r, s, f, A))",
	},
		"PullbackForm applies to each active entry with the same open source and image guard. The "+
			"matrix pullback definition preserves the rectangular zero padding, including zero-sized shapes."),
})}

var MatrixPullbackProduct = matrixPullbackProductThm{family.Add(registry.ProofEntry{
	Name: "MatrixPullbackProduct",
	Key:  "prop_beccd2479a2c1b9a",
	Deps: []registry.EntryLike{
		MatrixPullbackForm,
		MatrixProductForm,
		PullbackLinear,
		PullbackWedge,
	},
	Build: family.Card(Statement{
		Binders: "∀n m p q r s t:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_matrix_on⟨m⟩(V, p, r, s, A)",
			"vec_form_matrix_on⟨m⟩(V, q, s, t, B)",
		},
		Conclusion: "vec_form_matrix_pullback⟨n, m⟩(U, " +
			"    p + q, " +
			"    r, " +
			"    t, " +
			"    f, " +
			"    vec_form_matrix_product⟨m⟩(V, p, q, r, s, t, A, B)) = " +
			"vec_form_matrix_product⟨n⟩(U, " +
			"    p, " +
			"    q, " +
			"    r, " +
			"    s, " +
			"    t, " +
			"    vec_form_matrix_pullback⟨n, m⟩(U, p, r, s, f, A), " +
			"    vec_form_matrix_pullback⟨n, m⟩(U, q, s, t, f, B))",
	},
		"PullbackLinear moves pullback through each finite contraction and PullbackWedge "+
			"identifies the terms. The same shape guards then give equality at every matrix index."),
})}

var MatrixPullbackDerivative = matrixPullbackDerivativeThm{family.Add(registry.ProofEntry{
	Name: "MatrixPullbackDerivative",
	Key:  "prop_c732dcc17637445d",
	Deps: []registry.EntryLike{
		MatrixPullbackForm,
		MatrixDerivativeForm,
		PullbackExteriorDerivative,
	},
	Build: family.Card(Statement{
		Binders: "∀n m k r s:num. " +
			"∀U V:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"vec_smooth_map_on⟨n, m⟩(U, f)",
			"∀x:(num → real). x ∈ U ⇒ f(x) ∈ V",
			"vec_form_matrix_on⟨m⟩(V, k, r, s, A)",
		},
		Conclusion: "vec_form_matrix_pullback⟨n, m⟩(U, " +
			"    k + 1, " +
			"    r, " +
			"    s, " +
			"    f, " +
			"    vec_form_matrix_derivative⟨m⟩(V, k, r, s, A)) = " +
			"vec_form_matrix_derivative⟨n⟩(U, k, r, s, vec_form_matrix_pullback⟨n, m⟩(U, k, r, s, f, A))",
	},
		"Apply PullbackExteriorDerivative to each active entry. The zero "+
			"guards on the two matrix operations agree outside the rectangle, "+
			"so the scalar identities assemble into a total-function equality."),
})}

var MatrixTraceForm = matrixTraceFormThm{family.Add(registry.ProofEntry{
	Name: "MatrixTraceForm",
	Key:  "prop_3a43db4fe96657b0",
	Deps: []registry.EntryLike{formMatrixTraceDef, FormModule},
	Build: family.Card(Statement{
		Binders: "∀n k r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, k, r, r, A)"},
		Conclusion: "vec_form_on⟨n⟩(U, k, vec_form_matrix_trace(r, A))",
	},
		"The trace is a finite sum of active degree-k entries, hence lies in "+
			"the same form module. At rank zero it is the zero form on the open U."),
})}

var MatrixTraceCyclic = matrixTraceCyclicThm{family.Add(registry.ProofEntry{
	Name: "MatrixTraceCyclic",
	Key:  "prop_85f3036c458edbe7",
	Reading: "Cyclic exchange carries (-1)^(pq), even for rectangular A " +
		"and B. It becomes ordinary cyclicity when one degree is even; matrix " +
		"entries of arbitrary degrees cannot be treated as commuting scalars.",
	Deps: []registry.EntryLike{formMatrixTraceDef, FormMatrixProductDef, WedgeGradedCommutative},
	Build: family.Card(Statement{
		Binders: "∀n p q r s:num. " +
			"∀U:set(num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_matrix_on⟨n⟩(U, p, r, s, A)",
			"vec_form_matrix_on⟨n⟩(U, q, s, r, B)",
		},
		Conclusion: "vec_form_matrix_trace(r, vec_form_matrix_product⟨n⟩(U, p, q, r, s, r, A, B)) = " +
			"(λx:(num → real). λP:(num → num → real). " +
			"    (-&1)^(p * q) * " +
			"    vec_form_matrix_trace(s, vec_form_matrix_product⟨n⟩(U, q, p, s, r, s, B, A), x, P))",
	},
		"Expand both traces as double finite sums, interchange the two matrix "+
			"indices, and use WedgeGradedCommutative on each pair of entries. The sign "+
			"is the common scalar (-1)^(pq), also when either index range is empty."),
})}

var MatrixTraceDerivative = matrixTraceDerivativeThm{family.Add(registry.ProofEntry{
	Name: "MatrixTraceDerivative",
	Key:  "prop_1d65e35f0a4fdc05",
	Deps: []registry.EntryLike{
		MatrixTraceForm,
		MatrixDerivativeForm,
		formMatrixTraceDef,
		ExteriorDerivativeLinear,
	},
	Build: family.Card(Statement{
		Binders: "∀n k r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{"vec_form_matrix_on⟨n⟩(U, k, r, r, A)"},
		Conclusion: "vec_exterior_derivative⟨n⟩(U, k, vec_form_matrix_trace(r, A)) = " +
			"vec_form_matrix_trace(r, vec_form_matrix_derivative⟨n⟩(U, k, r, r, A))",
	},
		"ExteriorDerivativeLinear commutes with the finite sum of diagonal entries. On the diagonal "+
			"below r the matrix derivative is the entry derivative, which gives the trace on the right."),
})}

var MatrixTransposeProduct = matrixTransposeProductThm{family.Add(registry.ProofEntry{
	Name: "MatrixTransposeProduct",
	Key:  "prop_10d820a8edaae954",
	Reading: "Transposition reverses the matrix order and also contributes (-1)^(pq). " +
		"In particular, the square of a skew matrix of one-forms is skew, not symmetric.",
	Deps: []registry.EntryLike{FormMatrixProductDef, WedgeGradedCommutative},
	Build: family.Card(Statement{
		Binders: "∀n p q r s t:num. " +
			"∀U:set(num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real).",
		Hypotheses: []string{
			"vec_form_matrix_on⟨n⟩(U, p, r, s, A)",
			"vec_form_matrix_on⟨n⟩(U, q, s, t, B)",
		},
		Conclusion: "transpose(vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B)) = " +
			"(λi:num. λj:num. λx:(num → real). λP:(num → num → real). " +
			"    (-&1)^(p * q) * " +
			"    vec_form_matrix_product⟨n⟩(U, q, p, t, s, r, transpose(B), transpose(A), i, j, x, P))",
	},
		"The transposed entry is the sum of A(j,l)∧B(l,i). Exchange these "+
			"two factors by WedgeGradedCommutative to read the entry of BᵀAᵀ, "+
			"preserving the swapped output shape and its zero padding."),
})}
