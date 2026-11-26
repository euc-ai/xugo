// definitions.go — the chapter's definitional layer: Σ over ℕ.
//
// `nat_sum` is not a new mechanism. It is the fold at natural addition,
// and the definition says exactly that — every law in this chapter is
// the general law read at that one operation.

package nat_sum

import (
	"github.com/euc-ai/xugo/library/registry"
)

// NatSumDef — Σ over ℕ is the fold at `+`; `Σ_{i<n} f(i)` at a num body
// is `nat_sum({i:num | i < n}, λi:num. f(i))`.
var NatSumDef = natSumDefThm{family.Define(registry.DefEntry{
	Name:     "NatSumDef",
	Key:      "prop_e07e8bb638398384",
	Const:    "nat_sum",
	Type:     "set(A) → (A → num) → num",
	Overload: "sum",
	BigOp:    "Σ",
	// The instance is pinned: nothing in `iterated_op(+)` ties the fold's
	// index letter to the definiendum's, and an equation's two sides
	// must stand at one type.
	Equations: []string{"nat_sum = iterated_op⟨A:A, B:num⟩(+)"},
})}
