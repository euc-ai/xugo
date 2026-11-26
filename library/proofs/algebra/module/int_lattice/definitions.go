package int_lattice

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/principal_ideal_domain"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegerLatticeDef = integerLatticeDefThm{family.Define(registry.DefEntry{
	Name:  "IntegerLatticeDef",
	Key:   "prop_df4798eebaa7746d",
	Deps:  []registry.EntryLike{},
	Const: "integer_lattice",
	Type:  "ring_ops(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:set(A). " +
			"    integer_lattice(R, M) ⇔ " +
			"    submodule(restrict_ring(R, integer_image(R)), regular_module(R), M) ∧ " +
			"    module_finitely_generated(restrict_ring(R, integer_image(R)), " +
			"        restrict_module(regular_module(R), M))",
	},
})}

var FullIntegerLatticeDef = fullIntegerLatticeDefThm{family.Define(registry.DefEntry{
	Name:  "FullIntegerLatticeDef",
	Key:   "prop_436019f19a16cec",
	Deps:  []registry.EntryLike{IntegerLatticeDef},
	Const: "full_integer_lattice",
	Type:  "field_ops(A) → set(A) → bool",
	Equations: []string{
		"∀L:field_ops(A). ∀M:set(A). " +
			"    full_integer_lattice(L, M) ⇔ " +
			"    integer_lattice(field_ring(L), M) ∧ " +
			"    module_span(restrict_ring(field_ring(L), rational_image(L)), " +
			"        regular_module(field_ring(L)), " +
			"        M) = " +
			"    L.carrier",
	},
})}

var IntegerTriangularBasisDef = integerTriangularBasisDefThm{family.Define(registry.DefEntry{
	Name:  "IntegerTriangularBasisDef",
	Key:   "prop_228a8f9c8b67f4e6",
	Deps:  []registry.EntryLike{},
	Const: "integer_triangular_basis",
	Type:  "num → set(num → int) → num → (num → num → int) → (num → num) → bool",
	Equations: []string{
		"∀n r:num. ∀M:set(num → int). ∀b:(num → num → int). ∀p:(num → num). " +
			"    integer_triangular_basis(n, M, r, b, p) ⇔ " +
			"    indexed_module_basis(int_ring, " +
			"        restrict_module(free_module_record(int_ring, {i:num | i < n}), M), " +
			"        r, " +
			"        b) ∧ " +
			"    (∀i:num. i < r ⇒ p(i) < n ∧ 0 < b(i, p(i)) ∧ (∀j:num. p(i) < j ⇒ b(i, j) = 0)) ∧ " +
			"    (∀i j:num. i < j ∧ j < r ⇒ p(i) < p(j))",
	},
})}

var integerRemainderBoxDef = integerRemainderBoxDefThm{family.Define(registry.DefEntry{
	Name:  "integerRemainderBoxDef",
	Key:   "prop_d94c191b1fa1c789",
	Deps:  []registry.EntryLike{},
	Const: "integer_remainder_box",
	Type:  "num → (num → int) → set(num → int)",
	Equations: []string{
		"∀n:num. ∀d:(num → int). " +
			"    integer_remainder_box(n, d) = " +
			"    {v:(num → int) | " +
			"        v ∈ free_module_record(int_ring, {i:num | i < n}).carrier ∧ " +
			"        (∀i:num. i < n ⇒ 0 ≤ v(i) ∧ v(i) < d(i))}",
	},
})}
