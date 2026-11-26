// definitions.go — the complex power z^w.

package complex_cpow

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexCpowDef — `complex_cpow(z, w)`: z to the complex power w, by the
// principal logarithm, exp(w·log z); at the base 0 it is 0, except that
// 0 to the power 0 is 1.
var ComplexCpowDef = complexCpowDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexCpowDef",
	Key:   "prop_7a95d0ab4efd9656",
	Const: "complex_cpow",
	Type:  "complex → complex → complex",
	Equations: []string{
		"∀z w:complex. " +
			"    complex_cpow(z, w) = " +
			"    COND(z = &0, COND(w = &0, complex_of_real(&1), complex_of_real(&0)), exp(w * log(z)))",
	},
	Reading: "The power is the principal one: at a base on the closed negative half-line " +
		"it reads the logarithm with imaginary part π, and it is not continuous in the base " +
		"across that half-line. At a positive real base x it is exp(w·log x) with the real " +
		"logarithm (CpowPositiveReal), which is where this chapter's laws are stated. At the " +
		"base 0 the values are the convention of real_rpow: 0, and 1 at the exponent 0.",
})}
