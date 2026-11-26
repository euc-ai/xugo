// definitions.go — Π over ℝ is iterated_op at real multiplication.
// The equation pins the index and value types on both sides.

package real_product

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealProductDef — Π over ℝ is the fold at real multiplication; `Π_{i<n} f(i)`
// at a real body is `real_product({i:num | i < n}, λi:num. f(i))`.
var RealProductDef = realProductDefThm{family.Define(registry.DefEntry{
	Name:      "RealProductDef",
	Key:       "prop_eda03514cd64826b",
	Const:     "real_product",
	Type:      "set(A) → (A → real) → real",
	Overload:  "product",
	BigOp:     "Π",
	Equations: []string{"real_product = iterated_op⟨A:A, B:real⟩(real_mul)"},
})}
