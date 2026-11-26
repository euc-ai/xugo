// definitions.go — Π over ℕ is iterated_op at natural multiplication.
// The equation pins the index and value types on both sides.

package nat_product

import (
	"github.com/euc-ai/xugo/library/registry"
)

// NatProductDef — Π over ℕ is the fold at `*`; `Π_{i<n} f(i)` at a num
// body is `nat_product({i:num | i < n}, λi:num. f(i))`.
var NatProductDef = natProductDefThm{family.Define(registry.DefEntry{
	Name:      "NatProductDef",
	Key:       "prop_b423a3ac99345eb6",
	Const:     "nat_product",
	Type:      "set(A) → (A → num) → num",
	Overload:  "product",
	BigOp:     "Π",
	Equations: []string{"nat_product = iterated_op⟨A:A, B:num⟩(*)"},
})}
