package linear_determinant

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var ModuleBasisMatrixDef = moduleBasisMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleBasisMatrixDef",
	Key:   "prop_338622eba4eb5f5c",
	Deps:  []registry.EntryLike{},
	Const: "module_basis_matrix",
	Type:  "ring_ops(A) → module_ops(A, B) → num → (num → B) → (B → B) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e:(num → B). ∀f:(B → B). ∀i j:num. " +
			"    module_basis_matrix(R, M, n, e, f, i, j) = " +
			"    COND(i < n ∧ j < n, " +
			"        module_basis_coordinates(R, M, {e(k) | k:num | k < n}, f(e(j)), e(i)), " +
			"        R.zero)",
	},
})}

var ModuleDeterminantDef = moduleDeterminantDefThm{family.Define(registry.DefEntry{
	Name:  "ModuleDeterminantDef",
	Key:   "prop_1dd0305651253f13",
	Deps:  []registry.EntryLike{ModuleBasisMatrixDef},
	Const: "module_determinant",
	Type:  "ring_ops(A) → module_ops(A, B) → (B → B) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀f:(B → B). " +
			"    module_determinant(R, M, f) = " +
			"    εa:A. ∃n:num. ∃e:(num → B). " +
			"        indexed_module_basis(R, M, n, e) ∧ " +
			"        a = determinant(R, n, module_basis_matrix(R, M, n, e, f))",
	},
})}

var BasisChangeMatrixDef = basisChangeMatrixDefThm{family.Define(registry.DefEntry{
	Name:  "BasisChangeMatrixDef",
	Key:   "prop_286cdf9d69b63a0b",
	Deps:  []registry.EntryLike{},
	Const: "basis_change_matrix",
	Type:  "ring_ops(A) → module_ops(A, B) → num → (num → B) → (num → B) → num → num → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:module_ops(A, B). ∀n:num. ∀e f:(num → B). ∀i j:num. " +
			"    basis_change_matrix(R, M, n, e, f, i, j) = " +
			"    COND(i < n ∧ j < n, " +
			"        module_basis_coordinates(R, M, {e(k) | k:num | k < n}, f(j), e(i)), " +
			"        R.zero)",
	},
})}
