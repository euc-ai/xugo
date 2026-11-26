// definitions.go — the chapter's definitional layer: the integer
// power.
//
// The integer power is the natural power (real_pow.Pow) read at a
// sign — a nonnegative exponent is the natural power of its
// magnitude, a negative one the inverse of it. Nothing here asks the
// base to be nonzero, so every law that needs that says so itself.

package real_zpow

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealZpowDef — the integer power: the natural power at a nonnegative
// exponent, its inverse at a negative one.
var RealZpowDef = realZpowDefThm{family.Define(registry.DefEntry{
	Name:  "RealZpowDef",
	Key:   "prop_dc9d69d7496cdf76",
	Const: "real_zpow",
	Type:  "real → int → real",
	Equations: []string{
		"∀x:real. ∀n:int. " +
			"    real_zpow(x, n) = " +
			"    COND(0 ≤ n, real_pow(x, num_of_int(n)), real_inv(real_pow(x, num_of_int(-n))))",
	},
})}
