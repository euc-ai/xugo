package determinant

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/free_module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/vector/matrix"
	"github.com/euc-ai/xugo/library/registry"
)

var MatrixOverDef = matrixOverDefThm{family.Define(registry.DefEntry{
	Name:  "MatrixOverDef",
	Key:   "prop_d2e078835955c005",
	Deps:  []registry.EntryLike{},
	Const: "matrix_over",
	Type:  "ring_ops(A) → num → (num → num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). " +
			"    matrix_over(R, n, P) ⇔ " +
			"    matrix⟨n, n⟩(R.zero, P) ∧ (∀i j:num. i < n ∧ j < n ⇒ P(i, j) ∈ R.carrier)",
	},
})}

var MatrixIdentityDef = matrixIdentityDefThm{family.Define(registry.DefEntry{
	Name:  "MatrixIdentityDef",
	Key:   "prop_d171c72951d47a58",
	Deps:  []registry.EntryLike{},
	Const: "matrix_identity",
	Type:  "ring_ops(A) → num → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀n i j:num. matrix_identity(R, n, i, j) = COND(i < n ∧ i = j, R.one, R.zero)",
	},
})}

var PermutationMatrixDef = permutationMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "PermutationMatrixDef",
	Key:   "prop_24b69a0f8462a7d0",
	Deps:  []registry.EntryLike{MatrixIdentityDef},
	Const: "permutation_matrix",
	Type:  "ring_ops(A) → num → permutation(num) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀p:permutation(num). ∀r s:num. " +
			"    permutation_matrix(R, n, p, r, s) = matrix_identity(R, n, r, permutation_map(p, s))",
	},
})}

var ColumnReplaceDef = columnReplaceDefThm{family.Define(registry.DefEntry{
	Name:  "ColumnReplaceDef",
	Key:   "prop_e887065cd1309470",
	Deps:  []registry.EntryLike{},
	Const: "matrix_replace_column",
	Type:  "ring_ops(A) → num → (num → num → A) → num → (num → A) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). ∀j:num. ∀v:(num → A). ∀r c:num. " +
			"    matrix_replace_column(R, n, P, j, v, r, c) = " +
			"    COND(r < n ∧ c < n, COND(c = j, v(r), P(r, c)), R.zero)",
	},
})}

var DeterminantDef = determinantDefThm{family.Define(registry.DefEntry{
	Name: "DeterminantDef",
	Key:  "prop_97d5884b85da70d4",
	Reading: "The sign enters the Leibniz sum as the ring's one for an even permutation and " +
		"minus one for an odd one. At n = 0 the sum runs over the identity alone, the one " +
		"permutation of no points, and its product of entries is empty: the empty determinant is one.",
	Const: "determinant",
	Type:  "ring_ops(A) → num → (num → num → A) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). " +
			"    determinant(R, n, P) = " +
			"    module_sum(R.add, " +
			"        R.zero, " +
			"        symmetric_group({i:num | i < n}), " +
			"        λp:permutation(num). " +
			"            R.mul(COND(permutation_even(n, p), R.one, R.neg(R.one)), " +
			"                module_sum(R.mul, R.one, {i:num | i < n}, λi:num. P(i, permutation_map(p, i)))))",
	},
})}

var ColumnMultilinearDef = columnMultilinearDefThm{family.Define(registry.DefEntry{
	Name:  "ColumnMultilinearDef",
	Key:   "prop_b41dee598100800c",
	Deps:  []registry.EntryLike{MatrixOverDef, ColumnReplaceDef},
	Const: "column_multilinear",
	Type:  "ring_ops(A) → num → ((num → num → A) → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀F:((num → num → A) → A). " +
			"    column_multilinear(R, n, F) ⇔ " +
			"    (∀P:(num → num → A). matrix_over(R, n, P) ⇒ F(P) ∈ R.carrier) ∧ " +
			"    (∀P:(num → num → A). ∀j:num. ∀u v:(num → A). " +
			"        matrix_over(R, n, P) ∧ " +
			"        j < n ∧ " +
			"        u ∈ free_module_record(R, {i:num | i < n}).carrier ∧ " +
			"        v ∈ free_module_record(R, {i:num | i < n}).carrier ⇒ " +
			"        F(matrix_replace_column(R, n, P, j, fun_add(R.add, u, v))) = " +
			"        R.add(F(matrix_replace_column(R, n, P, j, u)), " +
			"            F(matrix_replace_column(R, n, P, j, v)))) ∧ " +
			"    (∀P:(num → num → A). ∀j:num. ∀u:(num → A). ∀a:A. " +
			"        matrix_over(R, n, P) ∧ " +
			"        j < n ∧ " +
			"        u ∈ free_module_record(R, {i:num | i < n}).carrier ∧ " +
			"        a ∈ R.carrier ⇒ " +
			"        F(matrix_replace_column(R, n, P, j, fun_smul(R.mul, a, u))) = " +
			"        R.mul(a, F(matrix_replace_column(R, n, P, j, u))))",
	},
})}

var AlternatingFormDef = alternatingFormDefThm{family.Define(registry.DefEntry{
	Name:  "AlternatingFormDef",
	Key:   "prop_82bd6eb39c7aa0f3",
	Deps:  []registry.EntryLike{ColumnMultilinearDef},
	Const: "alternating_form",
	Type:  "ring_ops(A) → num → ((num → num → A) → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀F:((num → num → A) → A). " +
			"    alternating_form(R, n, F) ⇔ " +
			"    column_multilinear(R, n, F) ∧ " +
			"    (∀P:(num → num → A). ∀i j:num. " +
			"        matrix_over(R, n, P) ∧ i < n ∧ j < n ∧ i ≠ j ∧ transpose(P, i) = transpose(P, j) ⇒ " +
			"        F(P) = R.zero)",
	},
})}

// AdjugateDef — entry (i, j) is the cofactor of entry (j, i), read
// without deleting indices: replace column i by the j-th basis vector.
var AdjugateDef = adjugateDefThm{family.Define(registry.DefEntry{
	Name:  "AdjugateDef",
	Key:   "prop_c8114324bf95f534",
	Const: "matrix_adjugate",
	Type:  "ring_ops(A) → num → (num → num → A) → num → num → A",
	Reading: "The replacement column is i and the basis vector is j: this transposes the cofactor " +
		"array. Both indices are cut off at n; the empty adjugate is the zero-padded empty matrix.",
	Deps: []registry.EntryLike{DeterminantDef, ColumnReplaceDef, MatrixIdentityDef},
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). ∀i j:num. " +
			"    matrix_adjugate(R, n, P, i, j) = " +
			"    COND(i < n ∧ j < n, " +
			"        determinant(R, " +
			"            n, " +
			"            matrix_replace_column(R, n, P, i, λr:num. matrix_identity(R, n, r, j))), " +
			"        R.zero)",
	},
})}

// MatrixInverseDef — the total cofactor formula over a field. Its
// two-sided inverse law is guarded by a nonzero determinant.
var MatrixInverseDef = matrixInverseDefThm{family.Define(registry.DefEntry{
	Name:  "MatrixInverseDef",
	Key:   "prop_9e9e20477295a865",
	Const: "matrix_inverse",
	Type:  "field_ops(A) → num → (num → num → A) → num → num → A",
	Deps:  []registry.EntryLike{AdjugateDef},
	Equations: []string{
		"∀L:field_ops(A). ∀n:num. ∀P:(num → num → A). ∀i j:num. " +
			"    matrix_inverse(L, n, P, i, j) = " +
			"    COND(i < n ∧ j < n, " +
			"        L.mul(L.inv(determinant(field_ring(L), n, P)), " +
			"            matrix_adjugate(field_ring(L), n, P, i, j)), " +
			"        L.zero)",
	},
})}
