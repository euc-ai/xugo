// Matrices of homogeneous forms carry explicit row and column counts.
// Their product contracts matrix indices and wedges form entries.

package vec_form

import "github.com/euc-ai/xugo/library/registry"

var FormMatrixOnDef = formMatrixOnDefThm{family.Define(registry.DefEntry{
	Name:  "FormMatrixOnDef",
	Key:   "prop_aa764da1a7230afd",
	Const: "vec_form_matrix_on",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{FormOnDef},
	Reading: "The row and column counts describe a matrix of forms, separately from " +
		"ambient dimension n and entry degree k. Inactive entries are the whole zero form, not " +
		"merely zero at one point. Openness is explicit even when a matrix has no active entries.",
	Equations: []string{
		"∀n k r s:num. ∀U:set(num → real). ∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"    vec_form_matrix_on⟨n⟩(U, k, r, s, A) ⇔ " +
			"    U ∈ euclidean_topology(n) ∧ " +
			"    matrix⟨r, s⟩(«zero», A) ∧ " +
			"    (∀i j:num. i < r ∧ j < s ⇒ vec_form_on⟨n⟩(U, k, A(i, j)))",
	},
})}

var FormMatrixProductDef = formMatrixProductDefThm{family.Define(registry.DefEntry{
	Name:  "FormMatrixProductDef",
	Key:   "prop_4eb5207dfb3e9e72",
	Const: "vec_form_matrix_product",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:  "n",
	Deps: []registry.EntryLike{WedgeDef},
	Equations: []string{
		"∀n p q r s t:num. " +
			"∀U:set(num → real). " +
			"∀A B:(num → num → (num → real) → (num → num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_matrix_product⟨n⟩(U, p, q, r, s, t, A, B, i, j, x, P) = " +
			"    COND(i < r ∧ j < t, Σ_{l<s} vec_form_wedge⟨n⟩(U, p, q, A(i, l), B(l, j), x, P), &0)",
	},
})}

var FormMatrixDerivativeDef = formMatrixDerivativeDefThm{family.Define(registry.DefEntry{
	Name:  "FormMatrixDerivativeDef",
	Key:   "prop_21a6b940b8d5bf2e",
	Const: "vec_form_matrix_derivative",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:  "n",
	Deps: []registry.EntryLike{ExteriorDerivativeDef},
	Equations: []string{
		"∀n k r s:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_matrix_derivative⟨n⟩(U, k, r, s, A, i, j, x, P) = " +
			"    COND(i < r ∧ j < s, vec_exterior_derivative⟨n⟩(U, k, A(i, j), x, P), &0)",
	},
})}

var FormMatrixPullbackDef = formMatrixPullbackDefThm{family.Define(registry.DefEntry{
	Name:  "FormMatrixPullbackDef",
	Key:   "prop_d4375bdb864d04d9",
	Const: "vec_form_matrix_pullback",
	Type: "num → " +
		"num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"num → " +
		"((num → real) → num → real) → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:       "n",
	SourceDim: "n",
	TargetDim: "m",
	Deps:      []registry.EntryLike{PullbackDef},
	Equations: []string{
		"∀n m k r s:num. " +
			"∀U:set(num → real). " +
			"∀f:((num → real) → num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_matrix_pullback⟨n, m⟩(U, k, r, s, f, A, i, j, x, P) = " +
			"    COND(i < r ∧ j < s, vec_form_pullback⟨n, m⟩(U, k, f, A(i, j), x, P), &0)",
	},
})}

var formMatrixTraceDef = formMatrixTraceDefThm{family.Define(registry.DefEntry{
	Name:  "formMatrixTraceDef",
	Key:   "prop_58f9847243351012",
	Const: "vec_form_matrix_trace",
	Type: "num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Equations: []string{
		"∀r:num. " +
			"∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_matrix_trace(r, A, x, P) = Σ_{i<r} A(i, i, x, P)",
	},
})}

var FormSkewMatrixOnDef = formSkewMatrixOnDefThm{family.Define(registry.DefEntry{
	Name:  "FormSkewMatrixOnDef",
	Key:   "prop_474ef252a0599997",
	Const: "vec_form_skew_matrix_on",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"bool",
	Dim:  "n",
	Deps: []registry.EntryLike{FormMatrixOnDef},
	Reading: "Skew symmetry is equality of the real-valued form entries with their " +
		"negatives, so it also forces the diagonal to vanish. It does not make matrix " +
		"multiplication commutative; exchanging form factors still carries their degree sign.",
	Equations: []string{
		"∀n k r:num. ∀U:set(num → real). ∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"    vec_form_skew_matrix_on⟨n⟩(U, k, r, A) ⇔ " +
			"    vec_form_matrix_on⟨n⟩(U, k, r, r, A) ∧ " +
			"    (∀i j:num. " +
			"        i < r ∧ j < r ⇒ A(j, i) = (λx:(num → real). λP:(num → num → real). -A(i, j, x, P)))",
	},
})}

var FormCurvatureDef = formCurvatureDefThm{family.Define(registry.DefEntry{
	Name:  "FormCurvatureDef",
	Key:   "prop_e8216450a27bc83e",
	Const: "vec_form_curvature",
	Type: "num → " +
		"set(num → real) → " +
		"num → " +
		"(num → num → (num → real) → (num → num → real) → real) → " +
		"num → " +
		"num → " +
		"(num → real) → " +
		"(num → num → real) → " +
		"real",
	Dim:  "n",
	Deps: []registry.EntryLike{FormMatrixDerivativeDef, FormMatrixProductDef},
	Equations: []string{
		"∀n r:num. " +
			"∀U:set(num → real). " +
			"∀A:(num → num → (num → real) → (num → num → real) → real). " +
			"∀i j:num. " +
			"∀x:(num → real). " +
			"∀P:(num → num → real). " +
			"    vec_form_curvature⟨n⟩(U, r, A, i, j, x, P) = " +
			"    vec_form_matrix_derivative⟨n⟩(U, 1, r, r, A, i, j, x, P) + " +
			"    vec_form_matrix_product⟨n⟩(U, 1, 1, r, r, r, A, A, i, j, x, P)",
	},
})}
