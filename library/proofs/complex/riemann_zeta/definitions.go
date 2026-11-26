// definitions.go — the Riemann zeta function on the half-plane Re s > 0.

package riemann_zeta

import (
	"github.com/euc-ai/xugo/library/registry"
)

// RiemannZetaDef — `riemann_zeta(s)`: ζ(s) as ξ(s)/(s − 1), where
// ξ(s) = 1 + Σ_{n ≥ 1} [(s − 1)·n^(−s) − (n^(1−s) − (n+1)^(1−s))] is a
// series that converges for Re s > 0.
var RiemannZetaDef = riemannZetaDefThm{family.Define(registry.DefEntry{
	Name:  "RiemannZetaDef",
	Key:   "prop_8bd8e8dfb85c5276",
	Const: "riemann_zeta",
	Type:  "complex → complex",
	Equations: []string{
		"∀s:complex. riemann_zeta(s) = (&1 + (εv:complex. complex_sums(«xiTerm»(s), v))) / (s - &1)",
	},
	Reading: "This is ζ for Re s > 0 and s ≠ 1: for Re s > 1 it is the sum of n^(−s) " +
		"(ZetaSums), and on 0 < Re s ≤ 1 its continuation. At s = 1 the quotient is by zero, which " +
		"in ℂ is 0 (complex_inv(&0) = &0), so riemann_zeta(&1) = &0: a convention at the pole, not " +
		"a value or a limit of ζ, and a statement that ζ has no zero must exclude s = 1. For Re s " +
		"≤ 0 this is not ζ: at s = 0 every term of the series is 0, so it sums and the constant is " +
		"−1 where ζ(0) = −1/2; elsewhere there the series has no sum and the value is unspecified.",
})}
