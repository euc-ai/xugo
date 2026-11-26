// definitions.go — the chapter's definitional layer: Σ over ℝ.
//
// `real_sum` is the fold at real addition, and the definition says exactly
// that. Everything the chapter proves is the general mechanism read at
// that one operation, plus what ℝ's own algebra adds to it.

package real_sum

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealSumDef — Σ over ℝ is the fold at real addition; `Σ_{i<n} f(i)` at a
// real body is `real_sum({i:num | i < n}, λi:num. f(i))`.
var RealSumDef = realSumDefThm{family.Define(registry.DefEntry{
	Name:     "RealSumDef",
	Key:      "prop_1989a0f85ee8d5f6",
	Const:    "real_sum",
	Type:     "set(A) → (A → real) → real",
	Overload: "sum",
	BigOp:    "Σ",
	// The instance is pinned, as in nat_sum: nothing in
	// `iterated_op(real_add)` ties the fold's index letter to the
	// definiendum's.
	Equations: []string{"real_sum = iterated_op⟨A:A, B:real⟩(real_add)"},
})}
