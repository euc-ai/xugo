package valuation_order

import (
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ValuationOrderDef — an integer order read at pairs of nonzero elements of a
// ring: additive on products, at least the lesser order on a nonzero sum, and
// exactly the lesser order on the sum of two elements of unequal order, which
// is nonzero.
var ValuationOrderDef = valuationOrderDefThm{family.Define(registry.DefEntry{
	Name:  "ValuationOrderDef",
	Key:   "prop_222a97946ad0c282",
	Deps:  []registry.EntryLike{},
	Const: "valuation_order",
	Type:  "ring_ops(A) → (A → int) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀v:(A → int). " +
			"    valuation_order(R, v) ⇔ " +
			"    (∀a b:A. " +
			"        a ∈ R.carrier ∧ b ∈ R.carrier ∧ a ≠ R.zero ∧ b ≠ R.zero ⇒ " +
			"        v(R.mul(a, b)) = v(a) + v(b) ∧ " +
			"        (R.add(a, b) ≠ R.zero ⇒ COND(v(a) ≤ v(b), v(a), v(b)) ≤ v(R.add(a, b))) ∧ " +
			"        (v(a) ≠ v(b) ⇒ R.add(a, b) ≠ R.zero ∧ v(R.add(a, b)) = COND(v(a) ≤ v(b), v(a), v(b))))",
	},
})}
