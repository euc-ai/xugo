// Integer sums are iterated addition over a set.

package int_sum

import "github.com/euc-ai/xugo/library/registry"

// IntSumDef — Σ over ℤ is the fold at integer addition; `Σ_{i<n} f(i)` at
// an int body is `int_sum({i:num | i < n}, λi:num. f(i))`.
var IntSumDef = intSumDefThm{family.Define(registry.DefEntry{
	Name:      "IntSumDef",
	Key:       "prop_4e8d3f51ad849b91",
	Const:     "int_sum",
	Type:      "set(A) → (A → int) → int",
	Overload:  "sum",
	BigOp:     "Σ",
	Equations: []string{"int_sum = iterated_op⟨A:A, B:int⟩(int_add)"},
})}
