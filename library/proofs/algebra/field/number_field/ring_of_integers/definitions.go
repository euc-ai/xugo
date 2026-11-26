package ring_of_integers

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/number_field/integral_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/linear_independence"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegralBasisDef = integralBasisDefThm{family.Define(registry.DefEntry{
	Name:  "IntegralBasisDef",
	Key:   "prop_d127203d36f490fa",
	Deps:  []registry.EntryLike{},
	Const: "integral_basis",
	Type:  "ring_ops(A) → num → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀e:(num → A). " +
			"    integral_basis(R, n, e) ⇔ " +
			"    indexed_module_basis(restrict_ring(R, integer_image(R)), " +
			"        restrict_module(regular_module(R), ring_of_integers(R)), " +
			"        n, " +
			"        e)",
	},
})}
