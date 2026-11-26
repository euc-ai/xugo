// definitions.go — the definitional layer: the coefficients of the zeta
// numerator, and a simple pole at one.

package real_formal_series

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_pow"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_field"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/registry"
)

// ZetaNumeratorCoefficientDef — `zeta_numerator_coefficient(q, a, n)`: the
// n-th coefficient of the zeta numerator (1 − T)(1 − qT)·Σ a(n)Tⁿ, which is
// a(n) − (q + 1)·a(n − 1) + q·a(n − 2). The sequence a is read at integer
// indices, so that n − 1 and n − 2 are indices of a at n = 0 and n = 1.
var ZetaNumeratorCoefficientDef = zetaNumeratorCoefficientDefThm{family.Define(registry.DefEntry{
	Name:  "ZetaNumeratorCoefficientDef",
	Key:   "prop_c07e74a8fb155867",
	Deps:  []registry.EntryLike{},
	Const: "zeta_numerator_coefficient",
	Type:  "num → (int → real) → num → real",
	Equations: []string{
		"∀q n:num. ∀a:(int → real). " +
			"    zeta_numerator_coefficient(q, a, n) = " +
			"    a(n) - real_of_num(q + 1) * a(n - &1) + real_of_num(q) * a(n - &2)",
	},
})}

// SeriesSimplePoleDef — `series_simple_pole_one(a)`: the real series a has a
// simple pole at one, a = P / ((1 − T)·Q) for real polynomials P and Q with
// Q(0) ≠ 0, so that Q is invertible as a series, and P(1), Q(1) ≠ 0, so
// that the pole at T = 1 is that of 1 − T alone. The quotient is stated
// cleared of its denominator: (1 − T)·Q·a = P.
var SeriesSimplePoleDef = seriesSimplePoleDefThm{family.Define(registry.DefEntry{
	Name:  "SeriesSimplePoleDef",
	Key:   "prop_ac9eb6ae5f3c2bcc",
	Deps:  []registry.EntryLike{},
	Const: "series_simple_pole_one",
	Type:  "(num → real) → bool",
	Equations: []string{
		"∀a:(num → real). " +
			"    series_simple_pole_one(a) ⇔ " +
			"    ∃P Q:(num → real). " +
			"        polynomial_over(𝕌, P) ∧ " +
			"        polynomial_over(𝕌, Q) ∧ " +
			"        Q(0) ≠ real_of_num(0) ∧ " +
			"        polynomial_eval(P, real_of_num(1)) ≠ real_of_num(0) ∧ " +
			"        polynomial_eval(Q, real_of_num(1)) ≠ real_of_num(0) ∧ " +
			"        polynomial_mul(polynomial_mul(basis_vector(0) - basis_vector(1), Q), a) = P",
	},
})}
