// definitions.go — the definitional layer: a polynomial is a sequence of
// coefficients with finitely many nonzero, added, negated, subtracted and
// scaled as the vector chapter's sequences are, and multiplied by
// convolution.

package polynomial

import (
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialOverDef — `polynomial_over(c, p)`: p is a polynomial with
// coefficients in c, a sequence that is zero from some index on — an
// n-vector for some n — with every coefficient in c. The polynomials
// over a subring are polynomials over the larger ring as they stand: the
// coefficients are the same sequence, and only the predicate differs.
var PolynomialOverDef = polynomialOverDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialOverDef",
	Key:      "prop_f4ac2bc5cf11a763",
	Const:    "polynomial_over",
	Type:     "A → set(A) → (num → A) → bool",
	Implicit: []string{"zero"},
	Equations: []string{
		"∀zero:A. ∀c:set(A). ∀p:(num → A). " +
			"    polynomial_over(zero, c, p) ⇔ (∃n:num. vec⟨n⟩(zero, p)) ∧ (∀i:num. p(i) ∈ c)",
	},
})}

// PolynomialMulDef — `polynomial_mul(p, q)`, the product of polynomials: the n-th
// coefficient is the sum of p(i) * q(n - i) over i ≤ n, folded from zero
// by the ring's addition. The sum is the module chapter's finite sum, so
// the product is defined for a ring on a set and needs no whole-type
// fold.
var PolynomialMulDef = polynomialMulDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialMulDef",
	Key:      "prop_6bd3c70b52059aa7",
	Const:    "polynomial_mul",
	Type:     "(A → A → A) → A → (A → A → A) → (num → A) → (num → A) → num → A",
	Implicit: []string{"add", "zero", "mul"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀p q:(num → A). ∀n:num. " +
			"    polynomial_mul(add, zero, mul, p, q, n) = " +
			"    module_sum(add, zero, {i:num | i ≤ n}, λi:num. mul(p(i), q(n - i)))",
	},
})}

// PolynomialDegreeDef — `polynomial_degree(p)`: the least d with p zero
// past d — the index of the last nonzero coefficient, and zero for the
// zero polynomial. For a sequence of infinite support it is a number
// nothing is said about.
var PolynomialDegreeDef = polynomialDegreeDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialDegreeDef",
	Key:      "prop_1226a77c25090145",
	Const:    "polynomial_degree",
	Type:     "A → (num → A) → num",
	Implicit: []string{"zero"},
	Equations: []string{
		"∀zero:A. ∀p:(num → A). " +
			"    polynomial_degree(zero, p) = " +
			"    εd:num. vec⟨suc(d)⟩(zero, p) ∧ (∀m:num. vec⟨suc(m)⟩(zero, p) ⇒ d ≤ m)",
	},
})}

// PolynomialMonicDef — `polynomial_monic(p)`: the coefficient at the
// degree is one.
var PolynomialMonicDef = polynomialMonicDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialMonicDef",
	Key:      "prop_667e662efbaa23e8",
	Const:    "polynomial_monic",
	Type:     "A → A → (num → A) → bool",
	Implicit: []string{"zero", "one"},
	Equations: []string{
		"∀zero one:A. ∀p:(num → A). polynomial_monic(zero, one, p) ⇔ p(polynomial_degree(zero, p)) = one",
	},
	Deps: []registry.EntryLike{PolynomialDegreeDef},
})}

// PolynomialDerivativeDef — `polynomial_derivative(p)`: the formal
// derivative, its n-th coefficient (n + 1) · p(n + 1), the numeral n + 1
// being one added to itself n + 1 times.
var PolynomialDerivativeDef = polynomialDerivativeDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialDerivativeDef",
	Key:      "prop_c5b133ebbaf30b5d",
	Const:    "polynomial_derivative",
	Type:     "(A → A → A) → A → (A → A → A) → A → (num → A) → num → A",
	Implicit: []string{"add", "zero", "mul", "one"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀p:(num → A). ∀n:num. " +
			"    polynomial_derivative(add, zero, mul, one, p, n) = " +
			"    mul(monoid_pow(add, zero, one, suc(n)), p(suc(n)))",
	},
})}

// PolynomialPowDef — `polynomial_pow(p, n)`: the n-th power of p under
// the product of polynomials, the monoid power with the one polynomial
// as its identity. It is spelled by name, as the product is.
var PolynomialPowDef = polynomialPowDefThm{family.Define(registry.DefEntry{
	Name:     "PolynomialPowDef",
	Key:      "prop_e7318559130413a7",
	Const:    "polynomial_pow",
	Type:     "(A → A → A) → A → (A → A → A) → A → (num → A) → num → num → A",
	Implicit: []string{"add", "zero", "mul", "one"},
	Equations: []string{
		"∀add:(A → A → A). ∀zero:A. ∀mul:(A → A → A). ∀one:A. ∀p:(num → A). ∀n:num. " +
			"    polynomial_pow(add, zero, mul, one, p, n) = " +
			"    monoid_pow(polynomial_mul(add, zero, mul), basis_vector(zero, one, 0), p, n)",
	},
	Deps: []registry.EntryLike{PolynomialMulDef},
})}

// PolynomialRingDef — `polynomial_ring(R)`: the polynomials over the ring
// R as a ring record: the vector chapter's sum, zero, negation and
// difference, the product of polynomials, and the one polynomial
// basis_vector(0), on the polynomials with coefficients in R's carrier.
var PolynomialRingDef = polynomialRingDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialRingDef",
	Key:   "prop_704ea51b9a92de30",
	Const: "polynomial_ring",
	Type:  "ring_ops(A) → ring_ops(num → A)",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"    polynomial_ring(R) = " +
			"    mk_ring(vec_add(R.add), " +
			"        vec_zero(R.zero), " +
			"        vec_neg(R.neg), " +
			"        polynomial_mul(R.add, R.zero, R.mul), " +
			"        basis_vector(R.zero, R.one, 0), " +
			"        vec_sub(R.sub), " +
			"        {p:(num → A) | polynomial_over(R.zero, R.carrier, p)})",
	},
	Deps: []registry.EntryLike{PolynomialMulDef, PolynomialOverDef},
})}
