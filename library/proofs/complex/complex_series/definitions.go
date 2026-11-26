// definitions.go — the chapter's one definition: when a complex series
// sums to a complex number.

package complex_series

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexSumsDef — `complex_sums(a, s)`: the series Σ a(n) sums to s
// when its real parts sum to re(s) and its imaginary parts to im(s).
// This is convergence in the plane: a point's distance from s is at
// most the sum and at least each of the distances of its two parts.
var ComplexSumsDef = complexSumsDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexSumsDef",
	Key:   "prop_426b3620eff813d3",
	Const: "complex_sums",
	Type:  "(num → complex) → complex → bool",
	Equations: []string{
		"∀a:(num → complex). ∀s:complex. " +
			"    complex_sums(a, s) ⇔ real_sums(λn:num. re(a(n)), re(s)) ∧ real_sums(λn:num. im(a(n)), im(s))",
	},
	// The mints of the series relation and of the two parts.
})}
