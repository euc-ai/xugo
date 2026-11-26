package different

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/trace_dual"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	"github.com/euc-ai/xugo/library/registry"
)

var DifferentDef = differentDefThm{family.Define(registry.DefEntry{
	Name:  "DifferentDef",
	Key:   "prop_a0e60afb6034d8d8",
	Deps:  []registry.EntryLike{},
	Const: "number_different",
	Type:  "field_ops(A) → set(A)",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    number_different(F) = " +
			"    fractional_inverse(field_ring(F), " +
			"        ring_of_integers(field_ring(F)), " +
			"        trace_dual(F, " +
			"            rational_image(F), " +
			"            ring_of_integers(field_ring(F)), " +
			"            integer_image(field_ring(F))))",
	},
})}
