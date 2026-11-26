// definitions.go — the chapter's definitional layer: the exponential,
// the cosine and the sine of a complex number.
//
// Each is the sum of its power series, chosen through the relation
// `complex_sums` as ℝ's are through `real_sums`: exp z is Σ zⁿ/n!, cos z
// is Σ (−1)ⁿ·z²ⁿ/(2n)! and sin z is Σ (−1)ⁿ·z²ⁿ⁺¹/(2n+1)!, the signs and
// the factorials being reals carried into ℂ. All three series converge
// for every z (ExpSums, CosSums, SinSums), so each constant IS its sum.

package complex_exp

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexExpDef — `complex_exp(z)`, written `exp(z)`: the sum of the
// series Σ zⁿ/n!.
var ComplexExpDef = complexExpDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexExpDef",
	Key:      "prop_dddd571ff0fa5376",
	Const:    "complex_exp",
	Overload: "exp",
	Type:     "complex → complex",
	Equations: []string{
		"∀z:complex. " +
			"    complex_exp(z) = εs:complex. complex_sums(λn:num. z ^ n / complex_of_real(&factorial(n)), s)",
	},
	// The mints of the series relation, the power, the quotient, the
	// embedding and the factorial.
})}

// ComplexCosDef — `complex_cos(z)`, written `cos(z)`: the sum of the
// series Σ (−1)ⁿ·z²ⁿ/(2n)!.
var ComplexCosDef = complexCosDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexCosDef",
	Key:      "prop_6f77e631c48c42fc",
	Const:    "complex_cos",
	Overload: "cos",
	Type:     "complex → complex",
	Equations: []string{
		"∀z:complex. " +
			"    complex_cos(z) = " +
			"    εs:complex. " +
			"        complex_sums(λn:num. " +
			"                complex_of_real(real_pow(-&1, n)) * " +
			"                z ^ (2 * n) / " +
			"                complex_of_real(&factorial(2 * n)), " +
			"            s)",
	},
	// ComplexExpDef's mints, ℂ's product, ℝ's power and negation, and ℕ's
	// product.
})}

// ComplexSinDef — `complex_sin(z)`, written `sin(z)`: the sum of the
// series Σ (−1)ⁿ·z²ⁿ⁺¹/(2n+1)!.
var ComplexSinDef = complexSinDefThm{family.Define(registry.DefEntry{
	Name:     "ComplexSinDef",
	Key:      "prop_9cf504d1230b9f7c",
	Const:    "complex_sin",
	Overload: "sin",
	Type:     "complex → complex",
	Equations: []string{
		"∀z:complex. " +
			"    complex_sin(z) = " +
			"    εs:complex. " +
			"        complex_sums(λn:num. " +
			"                complex_of_real(real_pow(-&1, n)) * " +
			"                z ^ (2 * n + 1) / " +
			"                complex_of_real(&factorial(2 * n + 1)), " +
			"            s)",
	},
	// ComplexCosDef's mints and ℕ's sum.
})}
