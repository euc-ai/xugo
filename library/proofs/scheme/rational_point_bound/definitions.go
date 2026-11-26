package rational_point_bound

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/registry"
)

var frobeniusTensorDef = frobeniusTensorDefThm{family.Define(registry.DefEntry{
	Name:  "frobeniusTensorDef",
	Key:   "prop_5caf38ebfeb5bcb5",
	Deps:  []registry.EntryLike{},
	Const: "frobenius_tensor",
	Type:  "ring_ops(A) → set(A) → set(A) → num → (prod(A, A) → A) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀E F:set(A). ∀s:num. ∀c:(prod(A, A) → A). " +
			"    frobenius_tensor(R, E, F, s, c) = " +
			"    module_sum(R.add, " +
			"        R.zero, " +
			"        set_cross(E, F), " +
			"        λp:prod(A, A). R.mul(c(p), R.mul(fst(p), monoid_pow(R.mul, R.one, snd(p), s))))",
	},
})}

var frobeniusSwapDef = frobeniusSwapDefThm{family.Define(registry.DefEntry{
	Name:  "frobeniusSwapDef",
	Key:   "prop_97fadb3708f215a0",
	Deps:  []registry.EntryLike{},
	Const: "frobenius_swap",
	Type:  "ring_ops(A) → set(A) → set(A) → num → (prod(A, A) → A) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀E F:set(A). ∀s:num. ∀c:(prod(A, A) → A). " +
			"    frobenius_swap(R, E, F, s, c) = " +
			"    module_sum(R.add, " +
			"        R.zero, " +
			"        set_cross(E, F), " +
			"        λp:prod(A, A). " +
			"            R.mul(monoid_pow(R.mul, R.one, c(p), s), " +
			"                R.mul(monoid_pow(R.mul, R.one, fst(p), s), snd(p))))",
	},
})}
