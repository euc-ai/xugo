package number_field

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	"github.com/euc-ai/xugo/library/registry"
)

var NumberFieldDef = numberFieldDefThm{family.Define(registry.DefEntry{
	Name:  "NumberFieldDef",
	Key:   "prop_8554050c6f06a950",
	Deps:  []registry.EntryLike{},
	Const: "number_field",
	Type:  "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    number_field(F) ⇔ " +
			"    field_on(F) ∧ " +
			"    characteristic_zero(field_ring(F)) ∧ " +
			"    finite_dimensional(restrict_ring(field_ring(F), rational_image(F)), " +
			"        regular_module(field_ring(F)))",
	},
})}
