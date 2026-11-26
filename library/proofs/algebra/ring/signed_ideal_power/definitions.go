// definitions.go — the integer powers of a fractional ideal: the natural
// powers under the product, S at zero, and the powers of the inverse at
// the negative exponents.

package signed_ideal_power

import (
	"github.com/euc-ai/xugo/library/registry"
	// The chapter minting int_of_num and num_of_int, which the signed powers'
	// definition spells, initialized before it.
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
)

// SignedIdealPowerDef — `signed_ideal_power(L, S, I, n)`, written Iⁿ: the
// n-th power of I under the product of fractional ideals of S for n ≥ 0, S at
// 0, and the (−n)-th power of the inverse (S : I) for n < 0.
var SignedIdealPowerDef = signedIdealPowerDefThm{family.Define(registry.DefEntry{
	Name:  "SignedIdealPowerDef",
	Key:   "prop_f3fe09a87c4e4f62",
	Const: "signed_ideal_power",
	Type:  "ring_ops(A) → set(A) → set(A) → int → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S I:set(A). ∀n:int. " +
			"    signed_ideal_power(R, S, I, n) = " +
			"    COND(0 ≤ n, " +
			"        monoid_pow((λX:set(A). λY:set(A). fractional_mul(R, S, X, Y)), S, I, num_of_int(n)), " +
			"        monoid_pow((λX:set(A). λY:set(A). fractional_mul(R, S, X, Y)), " +
			"            S, " +
			"            fractional_inverse(R, S, I), " +
			"            num_of_int(-n)))",
	},
})}
