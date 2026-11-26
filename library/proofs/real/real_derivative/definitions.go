// definitions.go — the chapter's definitional layer: what it means for
// a function to have a derivative at a point.

package real_derivative

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RealDerivativeAtDef — `real_derivative_at(f, c, l)`: the difference
// quotient (f(x) − f(c)) / (x − c) tends to l at c. The quotient is
// never evaluated at c itself — a limit ignores the centre — so its
// value there, a division by zero, plays no part.
var RealDerivativeAtDef = realDerivativeAtDefThm{family.Define(registry.DefEntry{
	Name:  "RealDerivativeAtDef",
	Key:   "prop_2e9c467407861f78",
	Const: "real_derivative_at",
	Type:  "(real → real) → real → real → bool",
	Equations: []string{
		"∀f:(real → real). ∀c l:real. " +
			"    real_derivative_at(f, c, l) ⇔ (λx:real. (f(x) - f(c)) / (x - c)) ⟶ l (at c)",
	},
	// The mints of the limit, division and `-`.
})}
