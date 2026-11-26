// definitions.go — the chapter's definitional layer: what it means for
// a function to be a polynomial.
//
// The definition is existential rather than structural: a function IS
// a polynomial when SOME degree bound and SOME coefficient sequence
// reproduce it. Nothing names the degree — a bound is enough, and
// asking for the exact one would make the notion harder to establish
// and no stronger to use.

package real_polynomial

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialFunctionDef — some bound and some coefficients reproduce
// the function.
var PolynomialFunctionDef = polynomialFunctionDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialFunctionDef",
	Key:   "prop_56fb426f3c8faf07",
	Const: "polynomial_function",
	Type:  "(real → real) → bool",
	Equations: []string{
		"∀f:(real → real). " +
			"    polynomial_function(f) ⇔ " +
			"    ∃m:num. ∃c:(num → real). ∀x:real. f(x) = sum(0 .. m, λi:num. c(i) * real_pow(x, i))",
	},
})}
