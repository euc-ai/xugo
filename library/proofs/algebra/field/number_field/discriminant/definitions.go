package discriminant

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field_trace"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/ring_of_integers"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/registry"
)

var DiscriminantDef = discriminantDefThm{family.Define(registry.DefEntry{
	Name:  "DiscriminantDef",
	Key:   "prop_775e6d58530d4274",
	Deps:  []registry.EntryLike{},
	Const: "basis_discriminant",
	Type:  "field_ops(A) → num → (num → A) → A",
	Equations: []string{
		"∀F:field_ops(A). ∀n:num. ∀e:(num → A). " +
			"    basis_discriminant(F, n, e) = " +
			"    determinant(restrict_ring(field_ring(F), rational_image(F)), " +
			"        n, " +
			"        λi:num. λj:num. " +
			"            COND(i < n ∧ j < n, field_trace(F, rational_image(F), F.mul(e(i), e(j))), F.zero))",
	},
})}

var IntegerFieldDiscriminantDef = integerFieldDiscriminantDefThm{family.Define(registry.DefEntry{
	Name: "IntegerFieldDiscriminantDef",
	Key:  "prop_4f318da37589762",
	Reading: "The choice is specified by the basis-independence " +
		"theorem; no independence or existence is built into number-field data.",
	Deps:  []registry.EntryLike{DiscriminantDef},
	Const: "integer_field_discriminant",
	Type:  "field_ops(A) → int",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    integer_field_discriminant(F) = " +
			"    εd:int. ∃n:num. ∃e:(num → A). " +
			"        integral_basis(field_ring(F), n, e) ∧ " +
			"        integer_map(field_ring(F), d) = basis_discriminant(F, n, e)",
	},
})}
