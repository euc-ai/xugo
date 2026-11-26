// definitions.go — the chapter's definitional layer: what it means for
// a real to be rational.
//
// A rational is a quotient of two integers, the divisor nonzero — the
// textbook sentence, with `integer` the predicate ℤ is carved out of ℝ
// by. Nothing is minted beside it: no numerator, no denominator, no
// reduced form.

package rational

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RationalDef — `rational(x)`: x is a quotient m / n of two integers
// with n nonzero.
var RationalDef = rationalDefThm{family.Define(registry.DefEntry{
	Name:  "RationalDef",
	Key:   "prop_7c42dcb7aeb31240",
	Const: "rational",
	Type:  "real → bool",
	Equations: []string{
		"∀x:real. rational(x) ⇔ ∃m n:real. integer(m) ∧ integer(n) ∧ n ≠ &0 ∧ x = m / n",
	},
	// The mints of the constants the definiens spells: `integer`, the
	// quotient, and the embedding `&`.
})}
