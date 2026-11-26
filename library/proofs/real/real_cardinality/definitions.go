// definitions.go — the chapter's definitional layer: the terms of a set
// of naturals' ternary expansion.
//
// A set of naturals s is read as a real through its ternary expansion
// with digits 0 and 1 — digit 1 at the members of s. The constant names
// the expansion's terms, so that the series of s is `ternary_digits(s)`
// and a statement about its sum reads `real_sums(ternary_digits(s), x)`.

package real_cardinality

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ternaryDigitsDef — `ternary_digits(s, n)`: the n-th term of the
// ternary expansion of s, 3⁻ⁿ when n ∈ s and 0 otherwise.
var ternaryDigitsDef = ternaryDigitsDefThm{family.Define(registry.DefEntry{
	Name:  "ternaryDigitsDef",
	Key:   "prop_b06e9551cb717f80",
	Const: "ternary_digits",
	Type:  "set(num) → num → real",
	Equations: []string{
		"∀s:set(num). ∀n:num. ternary_digits(s, n) = COND(n ∈ s, real_pow(real_inv(&3), n), &0)",
	},
	// The mints of the constants the definiens spells.
})}
