// definitions.go — the composite of a field with a subfield.

package constant_composite

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	"github.com/euc-ai/xugo/library/registry"
)

var ConstantCompositeDef = constantCompositeDefThm{family.Define(registry.DefEntry{
	Name:  "ConstantCompositeDef",
	Key:   "prop_324a3b45b97803ee",
	Deps:  []registry.EntryLike{},
	Const: "constant_composite",
	Type:  "field_ops(A) → set(A) → set(A) → set(A)",
	Equations: []string{
		"∀F:field_ops(A). ∀K l:set(A). constant_composite(F, K, l) = field_adjoin(F, K, l)",
	},
})}
