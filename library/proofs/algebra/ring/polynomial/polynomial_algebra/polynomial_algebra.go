// polynomial_algebra.go — the polynomial algebra on a set of variables,
// built from functions: a monomial is an exponent for each variable,
// zero at all but finitely many and nonzero only at variables of the
// set; a polynomial is a member of the free module on the monomials,
// added pointwise and multiplied by the convolution of coefficients,
// and the polynomials of S with these operations are a ring record.

package polynomial_algebra

import (
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Monomials
// ---------------------------------------------------------------------------

// MonomialsDef — `monomials(S)`: the exponent functions on the
// variables that are zero at all but finitely many and nonzero only at
// members of S.
var MonomialsDef = monomialsDefThm{family.Define(registry.DefEntry{
	Name:  "MonomialsDef",
	Key:   "prop_9370c89a06293cf7",
	Const: "monomials",
	Type:  "set(D) → set(D → num)",
	Equations: []string{
		"∀S:set(D). monomials(S) = {m:(D → num) | finite_support(0, m) ∧ (∀x:D. ¬(m(x) = 0) ⇒ x ∈ S)}",
	},
	Reading: "The empty set has one monomial, the exponent " +
		"zero at every variable, the monomial of the constants.",
})}

// MonomialVarDef — `monomial_var(x)`: the monomial of the variable x,
// exponent one at x and zero elsewhere.
var MonomialVarDef = monomialVarDefThm{family.Define(registry.DefEntry{
	Name:      "MonomialVarDef",
	Key:       "prop_b8d462e4b5f36b7",
	Const:     "monomial_var",
	Type:      "D → D → num",
	Equations: []string{"∀x:D. monomial_var(x) = delta_at(0, 1, x)"},
})}

// ---------------------------------------------------------------------------
// Polynomials and their operations
// ---------------------------------------------------------------------------

// PolynomialAlgebraDef — `polynomial_algebra(R, S)`: the polynomials in
// the variables of S over R, the free module on the monomials of S —
// finitely many nonzero coefficients, every coefficient in R's carrier.
var PolynomialAlgebraDef = polynomialAlgebraDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraDef",
	Key:   "prop_a9418391cb5d19b0",
	Const: "polynomial_algebra",
	Type:  "ring_ops(A) → set(D) → set((D → num) → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(D). " +
			"    polynomial_algebra(R, S) = finite_supp(R.zero, R.carrier, monomials(S))",
	},
	Deps: []registry.EntryLike{MonomialsDef},
})}

// PolynomialAlgebraMulDef — `polynomial_algebra_mul(R, f, g)`: the
// product of polynomials, its coefficient at a monomial m the sum over
// the monomials m₁ below m, exponent by exponent, of f(m₁) * g(m - m₁).
var PolynomialAlgebraMulDef = polynomialAlgebraMulDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraMulDef",
	Key:   "prop_116a6abad28820e2",
	Const: "polynomial_algebra_mul",
	Type:  "ring_ops(A) → ((D → num) → A) → ((D → num) → A) → (D → num) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀f g:((D → num) → A). ∀m:(D → num). " +
			"    polynomial_algebra_mul(R, f, g, m) = " +
			"    COND(finite_support(0, m), " +
			"        module_sum(R.add, " +
			"            R.zero, " +
			"            {m₁:(D → num) | ∀x:D. m₁(x) ≤ m(x)}, " +
			"            λm₁:(D → num). R.mul(f(m₁), g(λx:D. m(x) - m₁(x)))), " +
			"        R.zero)",
	},
	Reading: "The monomials below a finitely supported m are finitely many, and there the " +
		"difference m - m₁ is exact. At an exponent function of infinite support the index set is " +
		"infinite and its sum is unspecified, so the coefficient there is set to R.zero: the product " +
		"of two polynomials is zero off the finitely supported monomials, as a polynomial must be.",
})}

// PolynomialAlgebraOneDef — `polynomial_algebra_one(R)`: the one
// polynomial, coefficient R.one at the monomial of the constants and
// zero elsewhere.
var PolynomialAlgebraOneDef = polynomialAlgebraOneDefThm{family.Define(registry.DefEntry{
	Name:      "PolynomialAlgebraOneDef",
	Key:       "prop_10dfb31995aff732",
	Const:     "polynomial_algebra_one",
	Type:      "ring_ops(A) → (D → num) → A",
	Equations: []string{"∀R:ring_ops(A). polynomial_algebra_one(R) = delta_at(R.zero, R.one, λx:D. 0)"},
})}

// PolynomialAlgebraConstDef — `polynomial_algebra_const(R, a)`: the
// constant polynomial a, coefficient a at the monomial of the constants
// and zero elsewhere.
var PolynomialAlgebraConstDef = polynomialAlgebraConstDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraConstDef",
	Key:   "prop_c9c81ac75fe4e2ee",
	Const: "polynomial_algebra_const",
	Type:  "ring_ops(A) → A → (D → num) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀a:A. polynomial_algebra_const(R, a) = delta_at(R.zero, a, λx:D. 0)",
	},
})}

// PolynomialAlgebraVarDef — `polynomial_algebra_var(R, x)`: the variable
// x as a polynomial, coefficient R.one at the monomial of x and zero
// elsewhere.
var PolynomialAlgebraVarDef = polynomialAlgebraVarDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraVarDef",
	Key:   "prop_7d23267a9676dfb1",
	Const: "polynomial_algebra_var",
	Type:  "ring_ops(A) → D → (D → num) → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀x:D. polynomial_algebra_var(R, x) = delta_at(R.zero, R.one, monomial_var(x))",
	},
	Reading: "Over the zero ring, where R.one = R.zero, every variable is the " +
		"zero polynomial, so distinct variables are told apart only when R.one ≠ R.zero.",
	Deps: []registry.EntryLike{MonomialVarDef},
})}

// PolynomialAlgebraRingDef — `polynomial_algebra_ring(R, S)`: the
// polynomials in the variables of S over R as a ring record — the
// pointwise sum, zero, negation and difference of coefficients, the
// product of polynomials, the one polynomial, and the polynomials of S
// as the carrier. The operations do not read S: the rings of two sets
// of variables differ only in their carriers.
var PolynomialAlgebraRingDef = polynomialAlgebraRingDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialAlgebraRingDef",
	Key:   "prop_4906a661797debff",
	Const: "polynomial_algebra_ring",
	Type:  "ring_ops(A) → set(D) → ring_ops((D → num) → A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(D). " +
			"    polynomial_algebra_ring(R, S) = " +
			"    mk_ring(fun_add(R.add), " +
			"        fun_zero(R.zero), " +
			"        fun_neg(R.neg), " +
			"        polynomial_algebra_mul(R), " +
			"        polynomial_algebra_one(R), " +
			"        (λf:((D → num) → A). λg:((D → num) → A). λm:(D → num). R.sub(f(m), g(m))), " +
			"        polynomial_algebra(R, S))",
	},
	Deps: []registry.EntryLike{PolynomialAlgebraDef, PolynomialAlgebraMulDef, PolynomialAlgebraOneDef},
})}
