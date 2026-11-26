// Orthogonal zero-form matrices act on form matrices and connection matrices.

package vec_form

import (
	"github.com/euc-ai/xugo/library/registry"
)

var FormMatrixConjugateDef = formMatrixConjugateDefThm{family.Define(registry.DefEntry{
	Name:  "FormMatrixConjugateDef",
	Key:   "prop_af9ceacb945ae6c1",
	Const: "vec_form_matrix_conjugate",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{FormMatrixProductDef},
	Reading: "Conjugation means H-transpose times B times H, with H a matrix of zero-forms. " +
		"It is a congruence without an orthogonality hypothesis; no inverse is inserted.",
	Equations: []string{
		"∀n k r:num. ∀U:set(num → real). ∀H B:(num → num → (num → real) → (num → num → real) → real). " +
			"    vec_form_matrix_conjugate⟨n⟩(U, k, r, H, B) = " +
			"    vec_form_matrix_product⟨n⟩(U, " +
			"        0, " +
			"        k, " +
			"        r, " +
			"        r, " +
			"        r, " +
			"        transpose(H), " +
			"        vec_form_matrix_product⟨n⟩(U, k, 0, r, r, r, B, H))",
	},
})}

var FormOrthogonalOnDef = formOrthogonalOnDefThm{family.Define(registry.DefEntry{
	Name:  "FormOrthogonalOnDef",
	Key:   "prop_3e230842ae6b4bb1",
	Const: "vec_form_orthogonal_on",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dimensions: []string{"n"},
	Deps:       []registry.EntryLike{FormMatrixOnDef},
	Reading: "Orthogonality is imposed at points of U only. Zero-form entries are " +
		"independent of the frame argument, and are zero outside U. Rank zero and the " +
		"empty domain are allowed; determinant one is a separate orientation condition.",
	Equations: []string{
		"∀n r:num. ∀U:set(num → real). ∀H:(num → num → (num → real) → (num → num → real) → real). " +
			"    vec_form_orthogonal_on⟨n⟩(U, r, H) ⇔ " +
			"    vec_form_matrix_on⟨n⟩(U, 0, r, r, H) ∧ " +
			"    (∀x:(num → real). " +
			"        x ∈ U ⇒ " +
			"        matrix_product(real_ring, " +
			"            r, " +
			"            transpose(λi:num. λj:num. H(i, j, x, «empty frame»)), " +
			"            (λi:num. λj:num. H(i, j, x, «empty frame»))) = " +
			"        matrix_identity(real_ring, r))",
	},
})}

var FormGaugeConnectionDef = formGaugeConnectionDefThm{family.Define(registry.DefEntry{
	Name:  "FormGaugeConnectionDef",
	Key:   "prop_e75ee69192b1de4d",
	Const: "vec_form_gauge_connection",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → num → (num → real) → (num → num → real) → real)",
	Dimensions: []string{"n"},
	Deps: []registry.EntryLike{
		FormMatrixConjugateDef,
		FormMatrixDerivativeDef,
		FormMatrixProductDef,
	},
	Reading: "The convention is A transformed to H-transpose A H plus H-transpose " +
		"dH. Its curvature is H-transpose curvature(A) H when H is orthogonal.",
	Equations: []string{
		"∀n r:num. " +
			"∀U:set(num → real). " +
			"∀H A:(num → num → (num → real) → (num → num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_gauge_connection⟨n⟩(U, r, H, A, i, j, x, P) = " +
			"    vec_form_matrix_conjugate⟨n⟩(U, 1, r, H, A, i, j, x, P) + " +
			"    vec_form_matrix_product⟨n⟩(U, " +
			"        0, " +
			"        1, " +
			"        r, " +
			"        r, " +
			"        r, " +
			"        transpose(H), " +
			"        vec_form_matrix_derivative⟨n⟩(U, 0, r, r, H), " +
			"        i, " +
			"        j, " +
			"        x, " +
			"        P)",
	},
})}
