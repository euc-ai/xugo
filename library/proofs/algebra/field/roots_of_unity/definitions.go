package roots_of_unity

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	"github.com/euc-ai/xugo/library/registry"
)

// FieldUnitsDef — the multiplicative group of a field: its nonzero
// elements under its product, identity and inverse.
var FieldUnitsDef = fieldUnitsDefThm{family.Define(registry.DefEntry{
	Name:  "FieldUnitsDef",
	Key:   "prop_8b0f674fd8214582",
	Const: "field_units",
	Type:  "field_ops(A) → group_ops(A)",
	Equations: []string{
		"∀F:field_ops(A). field_units(F) = mk_group(F.mul, F.one, F.inv, F.carrier ∖ {F.zero})",
	},
})}
