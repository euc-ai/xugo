// definitions.go — perfect fields.

package perfect_field

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

var PerfectFieldDef = perfectFieldDefThm{family.Define(registry.DefEntry{
	Name:  "PerfectFieldDef",
	Key:   "prop_2d03bf551d9bf9a5",
	Deps:  []registry.EntryLike{},
	Const: "perfect_field",
	Type:  "field_ops(A) → bool",
	Equations: []string{
		"∀F:field_ops(A). " +
			"    perfect_field(F) ⇔ " +
			"    ∀p:(num → A). " +
			"        polynomial_irreducible(field_ring(F), p) ⇒ polynomial_separable(field_ring(F), p)",
	},
})}
