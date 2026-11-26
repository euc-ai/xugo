// definitions.go — the Weil conjectures as one predicate on a point-count function, so that
// the chapter states the package once and its theorems say where it holds.

package weil_curve

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/complex/finite_spectrum"
	_ "github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// WeilConjecturesDef — weil_conjectures(q, g, N, P): P is the Weil numerator for the
// point counts N of a curve of genus g over a field of q elements. P has integer
// coefficients, constant term one, degree 2g and top coefficient q^g; (1 − T)(1 − qT)
// times the formal exponential of Σ N(m) T^m / m is P; the coefficients of P are
// reciprocal; P is the product of 2g factors 1 − a_i T whose a_i have modulus √q and
// whose power sums are q^m + 1 − N(m); and N(m) lies within 2g·√(q^m) of q^m + 1.
var WeilConjecturesDef = weilConjecturesDefThm{family.Define(registry.DefEntry{
	Name:  "WeilConjecturesDef",
	Key:   "prop_fb43427e2ad85e14",
	Deps:  []registry.EntryLike{},
	Const: "weil_conjectures",
	Type:  "num → num → (num → num) → (num → real) → bool",
	Reading: "N is read at positive m only: its value at zero is no part of " +
		"the predicate, so two count functions agreeing on the positive integers " +
		"satisfy it together (WeilConjecturesOfAgreeingCounts). No hypothesis is " +
		"placed on q; for a curve q is the size of its finite field of constants.",
	Abbrev: Abbrev{
		{Name: "1−T", Text: "vec_sub(real_sub, " +
			"    basis_vector(real_of_num(0), real_of_num(1), 0), " +
			"    basis_vector(real_of_num(0), real_of_num(1), 1))"},
		{Name: "1−qT", Text: "vec_sub(real_sub, " +
			"    basis_vector(real_of_num(0), real_of_num(1), 0), " +
			"    vec_scalar_mul(real_mul, real_of_num(q), basis_vector(real_of_num(0), real_of_num(1), 1)))"},
		{Name: "expOfCounts", Text: "formal_exp_zero(real_ring, " +
			"    λm:num. COND(m = 0, real_of_num(0), real_of_num(N(m)) / real_of_num(m)))"},
	},
	Equations: []string{
		"∀q g:num. ∀N:(num → num). ∀P:(num → real). " +
			"    weil_conjectures(q, g, N, P) ⇔ " +
			"    polynomial_over(real_of_num(0), image(real_of_int, 𝕌), P) ∧ " +
			"    P(0) = real_of_num(1) ∧ " +
			"    polynomial_degree(real_of_num(0), P) = 2 * g ∧ " +
			"    P(2 * g) = real_of_num(q) ^ g ∧ " +
			"    polynomial_mul(real_add, " +
			"        real_of_num(0), " +
			"        real_mul, " +
			"        polynomial_mul(real_add, real_of_num(0), real_mul, «1−T», «1−qT»), " +
			"        «expOfCounts») = " +
			"    P ∧ " +
			"    (∀j:num. j ≤ 2 * g ⇒ real_of_num(q) ^ g * P(j) = real_of_num(q) ^ j * P(2 * g - j)) ∧ " +
			"    (∃a:(num → complex). " +
			"        (λn:num. complex_of_real(P(n))) = reciprocal_product(2 * g, a) ∧ " +
			"        (∀i:num. i < 2 * g ⇒ complex_abs(a(i)) = real_sqrt(real_of_num(q))) ∧ " +
			"        (∀m:num. " +
			"            0 < m ⇒ " +
			"            complex_of_real(real_of_num(N(m))) = " +
			"            complex_sub(complex_of_real(real_of_num(q ^ m + 1)), " +
			"                finite_power_sum(2 * g, a, m)))) ∧ " +
			"    (∀m:num. " +
			"        0 < m ⇒ " +
			"        real_abs(real_of_num(N(m)) - real_of_num(q ^ m + 1)) ≤ " +
			"        real_of_num(2 * g) * real_sqrt(real_of_num(q ^ m)))",
	},
})}
