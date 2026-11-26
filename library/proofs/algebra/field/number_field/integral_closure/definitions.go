package integral_closure

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/characteristic_zero"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	"github.com/euc-ai/xugo/library/registry"
)

var RingOfIntegersDef = ringOfIntegersDefThm{family.Define(registry.DefEntry{
	Name:  "RingOfIntegersDef",
	Key:   "prop_569ae489cdbdea0",
	Deps:  []registry.EntryLike{},
	Const: "ring_of_integers",
	Type:  "ring_ops(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    ring_of_integers(R) = " +
			"    {x:A | x ∈ R.carrier ∧ integral_over(restrict_ring(R, integer_image(R)), x)}",
	},
})}
