// definitions.go — Π over ℤ is iterated_op at integer multiplication.
// The equation pins the index and value types on both sides.

package int_product

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IntProductDef — Π over ℤ is the fold at integer multiplication;
// `Π_{i<n} f(i)` at an int body is `int_product({i:num | i < n}, λi:num. f(i))`.
var IntProductDef = intProductDefThm{family.Define(registry.DefEntry{
	Name:      "IntProductDef",
	Key:       "prop_348f6a30c3a03eb0",
	Const:     "int_product",
	Type:      "set(A) → (A → int) → int",
	Overload:  "product",
	BigOp:     "Π",
	Equations: []string{"int_product = iterated_op⟨A:A, B:int⟩(int_mul)"},
})}
