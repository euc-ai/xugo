// definitions.go — the chapter's definitional layer: the square root.
//
// The root is totalized over all of ℝ by choosing, for x, the y
// whose square is |x| and whose sign is the sign of x — so real_sqrt(-x) is
// -real_sqrt(x), and on the nonnegative reals it is the usual nonnegative
// root. The definition is a choice; that such a y exists is the
// chapter's first theorem, and every other law reads off it.

package real_sqrt

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealSqrtDef — the signed square root: the y with the sign of x whose
// square is |x|.
var RealSqrtDef = realSqrtDefThm{family.Define(registry.DefEntry{
	Name:      "RealSqrtDef",
	Key:       "prop_5590c0366c2653a5",
	Const:     "real_sqrt",
	Type:      "real → real",
	Equations: []string{"∀x:real. real_sqrt(x) = εy:real. sgn(y) = sgn(x) ∧ real_pow(y, 2) = |x|"},
})}
