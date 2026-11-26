package pfaffian

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/symmetric_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_div_mod"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/nat_parity"
	"github.com/euc-ai/xugo/library/registry"
)

// PfaffianDef — the signed perfect-matching sum, with each pair and
// the sequence of first endpoints ordered to count every matching once.
var PfaffianDef = pfaffianDefThm{family.Define(registry.DefEntry{
	Name:  "PfaffianDef",
	Key:   "prop_172688d863689916",
	Const: "pfaffian",
	Type:  "ring_ops(A) → num → (num → num → A) → A",
	Reading: "The dimension argument is the actual matrix size. Odd dimensions return zero. " +
		"In size zero the unique permutation contributes an empty product, one. No factorial or " +
		"power of two is divided out, so the definition applies to all commutative carrier rings.",
	Equations: []string{
		"∀R:ring_ops(A). ∀n:num. ∀P:(num → num → A). " +
			"    pfaffian(R, n, P) = " +
			"    COND(nat_even(n), " +
			"        module_sum(R.add, " +
			"            R.zero, " +
			"            {p:permutation(num) | " +
			"                p ∈ symmetric_group({i:num | i < n}) ∧ " +
			"                (∀i:num. " +
			"                    i < nat_div(n, 2) ⇒ " +
			"                    permutation_map(p, 2 * i) < permutation_map(p, 2 * i + 1)) ∧ " +
			"                (∀i j:num. " +
			"                    i < j ∧ j < nat_div(n, 2) ⇒ " +
			"                    permutation_map(p, 2 * i) < permutation_map(p, 2 * j))}, " +
			"            λp:permutation(num). " +
			"                R.mul(COND(permutation_even(n, p), R.one, R.neg(R.one)), " +
			"                    module_sum(R.mul, " +
			"                        R.one, " +
			"                        {i:num | i < nat_div(n, 2)}, " +
			"                        λi:num. P(permutation_map(p, 2 * i), permutation_map(p, 2 * i + 1))))), " +
			"        R.zero)",
	},
})}
