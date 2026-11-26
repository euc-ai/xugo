// definitions.go — the chapter's definitional layer: the real power x^a.
//
// For positive x the power is exp(a·log x). A base that is not positive
// has no logarithm to read, and the definition settles it by the values
// that keep the power laws at 0 true: 0 to a nonzero power is 0, and
// anything to the power 0 is 1. A negative base takes the same values
// as 0: the laws stated at every base (RpowNonneg, RpowZeroExponent)
// read them, and every other law asks for a base that is not negative.
//
// The definition is a COND on the sign of the base, so a proof opens it
// as a rule, `Simp(Fwd(RealRpowDef))`, with the sign of each base it
// meets resident: the rule then reads the branch the sign selects.

package real_rpow

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealRpowDef — `real_rpow(x, a)`: x to the real power a.
var RealRpowDef = realRpowDefThm{family.Define(registry.DefEntry{
	Name:  "RealRpowDef",
	Key:   "prop_c04c4d874f41604f",
	Const: "real_rpow",
	Type:  "real → real → real",
	Equations: []string{
		"∀x a:real. real_rpow(x, a) = COND(&0 < x, exp(a * log(x)), COND(a = &0, &1, &0))",
	},
	// The mints of exp and log (real_exp_log), which the laws' import of
	// that chapter orders before this one, and of `<`, `*` and `&`.
})}
