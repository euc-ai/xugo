// mason_stothers.go — the Wronskian of two polynomials and the
// Mason–Stothers theorem over a field, in the divisor form Snyder's
// argument proves, with Fermat's equation for polynomials and
// Davenport's bound as its corollaries.

package separable_polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_domain"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The Wronskian
// ---------------------------------------------------------------------------

// WronskianOver — the Wronskian of polynomials over c is over c.
var WronskianOver = wronskianOverThm{family.Add(registry.ProofEntry{
	Name: "WronskianOver",
	Key:  "prop_a5171b9a6ca00b99",
	Deps: []registry.EntryLike{
		PolynomialWronskianDef,
		polynomial.PolynomialMulOver,
		polynomial.DerivativeOver,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_over(R.carrier, polynomial_wronskian(p, q))",
	}),
		"a difference of two products of polynomials over R.carrier (PolynomialWronskianDef, "+
			"PolynomialMulOver), the derivatives being over R.carrier (DerivativeOver at K = "+
			"R.carrier), in the ring of polynomials over R.carrier (PolynomialRingOn)"),
})}

// WronskianSum — adding one argument to the other leaves the Wronskian
// unchanged.
var WronskianSum = wronskianSumThm{family.Add(registry.ProofEntry{
	Name: "WronskianSum",
	Key:  "prop_ef4cb50f5603573c",
	Deps: []registry.EntryLike{
		PolynomialWronskianDef,
		polynomial.DerivativeAdd,
		polynomial.DerivativeOver,
		polynomial.PolynomialMulDistrib,
		polynomial.PolynomialMulComm,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "polynomial_wronskian(p, p + q) = polynomial_wronskian(p, q) ∧ " +
			"polynomial_wronskian(p + q, q) = polynomial_wronskian(p, q)",
	}),
		"expand by the sum rule (DerivativeAdd) and distributivity (PolynomialMulDistrib): "+
			"W(p, p + q) gains polynomial_mul(p, p') - polynomial_mul(p', p), and W(p + q, q) "+
			"gains polynomial_mul(q, q') - polynomial_mul(q', q), both R.zero by commutativity "+
			"(PolynomialMulComm) in the ring of polynomials over R.carrier (PolynomialRingOn)"),
})}

// WronskianDivisor — a common divisor of p and its derivative divides
// the Wronskian of p with any q, in either order.
var WronskianDivisor = wronskianDivisorThm{family.Add(registry.ProofEntry{
	Name: "WronskianDivisor",
	Key:  "prop_22ca181ba935fbb6",
	Deps: []registry.EntryLike{
		PolynomialWronskianDef,
		polynomial_division.PolynomialDividesDef,
		polynomial.DerivativeOver,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀d p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, d)",
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_divides(R, d, p)",
			"polynomial_divides(R, d, polynomial_derivative(p))",
		},
		Conclusion: "polynomial_divides(R, d, polynomial_wronskian(p, q)) ∧ " +
			"polynomial_divides(R, d, polynomial_wronskian(q, p))",
	}),
		"with p = polynomial_mul(d, r) and polynomial_derivative(p) = polynomial_mul(d, "+
			"s), W(p, q) = polynomial_mul(d, polynomial_mul(r, q') - polynomial_mul(s, q)) "+
			"and W(q, p) = polynomial_mul(d, polynomial_mul(q, s) - polynomial_mul(q', r)), "+
			"in the ring of polynomials over R.carrier (PolynomialRingOn)"),
})}

// WronskianVec — the Wronskian vanishes from deg p + deg q on.
var WronskianVec = wronskianVecThm{family.Add(registry.ProofEntry{
	Name: "WronskianVec",
	Key:  "prop_d1b44d5930de361",
	Deps: []registry.EntryLike{
		PolynomialWronskianDef,
		polynomial.DegreeVec,
		polynomial.DerivativeVec,
		polynomial.DerivativeOver,
		polynomial.PolynomialMulVec,
		vec_space.VecAddOn,
		vec_space.VecNegOn,
		vec_space.SubAddNegOn,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
		},
		Conclusion: "vec⟨polynomial_degree(p) + polynomial_degree(q)⟩(polynomial_wronskian(p, q))",
	}),
		"p vanishes past its degree and its derivative from it (DegreeVec, DerivativeVec), and "+
			"likewise q; so polynomial_mul(p, q') and polynomial_mul(p', q) vanish from deg p + deg "+
			"q (PolynomialMulVec, a factor that vanishes from 0 being vec_zero), and so does their "+
			"difference, all coefficients lying in R.carrier (VecAddOn, VecNegOn, SubAddNegOn)"),
})}

// WronskianNonzero — over a field, coprime polynomials not both of zero
// derivative have a nonzero Wronskian.
var WronskianNonzero = wronskianNonzeroThm{family.Add(registry.ProofEntry{
	Name: "WronskianNonzero",
	Reading: "The field is load-bearing: over ℤ/4, 1 + 2t is a unit, so " +
		"coprime to itself, with derivative 2, yet its Wronskian with itself " +
		"is zero. So is coprimality: the Wronskian of t with t is zero.",
	Key: "prop_fd6b36cbb92d6660",
	Deps: []registry.EntryLike{
		PolynomialWronskianDef,
		polynomial_division.CoprimeDividesProduct,
		polynomial_division.CoprimeSymm,
		polynomial_division.DividesDegree,
		polynomial.DerivativeVec,
		polynomial.DegreeBelow,
		polynomial.DerivativeOver,
		polynomial.PolynomialMulComm,
		polynomial.PolynomialRingOn,
	},
	Build: family.Card(field.FieldOn.Statement(Statement{
		Binders: "∀p q:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"polynomial_coprime(field_ring(F), p, q)",
			"¬(polynomial_derivative(p) = vec_zero ∧ polynomial_derivative(q) = vec_zero)",
		},
		Conclusion: "¬(polynomial_wronskian(p, q) = vec_zero)",
	}),
		"if W(p, q) is F.zero, polynomial_mul(p, q') = polynomial_mul(p', q) in the additive group "+
			"of the polynomials over F.carrier (PolynomialRingOn), so p divides polynomial_mul(q, p') "+
			"and, being coprime to q, divides p' (CoprimeDividesProduct); a nonzero p' would then have "+
			"degree at least deg p (DividesDegree) and below it (DerivativeVec, DegreeBelow), so p' is "+
			"F.zero; by the same argument with q, coprime to p (CoprimeSymm), q' is F.zero"),
})}

// ---------------------------------------------------------------------------
// The Mason–Stothers theorem
// ---------------------------------------------------------------------------

// WronskianDivisorProduct — for coprime p and q, divisors d of p and p',
// e of q and q', and f of p + q and its derivative have their product
// dividing the Wronskian.
var WronskianDivisorProduct = wronskianDivisorProductThm{family.Add(registry.ProofEntry{
	Name: "WronskianDivisorProduct",
	Key:  "prop_1e461f9ba653951e",
	Deps: []registry.EntryLike{
		WronskianDivisor,
		WronskianSum,
		WronskianOver,
		polynomial_division.CoprimeDivisor,
		polynomial_division.CoprimeSum,
		polynomial_division.CoprimeSymm,
		polynomial_division.CoprimeMul,
		polynomial_division.CoprimeProductDivides,
		polynomial.PolynomialMulOver,
		vec_space.AddCommOn,
	},
	Build: family.Card(comm_ring.CommRingOn.Statement(Statement{
		Binders: "∀p q d e f:(num → A).",
		Hypotheses: []string{
			"polynomial_over(R.carrier, p)",
			"polynomial_over(R.carrier, q)",
			"polynomial_over(R.carrier, d)",
			"polynomial_over(R.carrier, e)",
			"polynomial_over(R.carrier, f)",
			"polynomial_coprime(R, p, q)",
			"polynomial_divides(R, d, p)",
			"polynomial_divides(R, d, polynomial_derivative(p))",
			"polynomial_divides(R, e, q)",
			"polynomial_divides(R, e, polynomial_derivative(q))",
			"polynomial_divides(R, f, p + q)",
			"polynomial_divides(R, f, polynomial_derivative(p + q))",
		},
		Conclusion: "polynomial_divides(R, " +
			"    polynomial_mul(polynomial_mul(d, e), f), " +
			"    polynomial_wronskian(p, q))",
	}),
		"each divides W(p, q): d and e by WronskianDivisor(e in its second conjunct, at q and p), "+
			"f by WronskianDivisor at p + q and q with WronskianSum; they are pairwise coprime, as "+
			"divisors of the coprime pairs p, q and p, p + q and q, p + q (CoprimeDivisor, CoprimeSum, "+
			"CoprimeSymm, AddCommOn); so polynomial_mul(d, e) divides W (CoprimeProductDivides), is "+
			"coprime to f (CoprimeMul), and its product with f divides W (CoprimeProductDivides)"),
})}

// MasonStothers — the Mason–Stothers theorem in its divisor form: over a
// field, for coprime p and q not both of zero derivative, divisors d of p
// and p', e of q and q', and f of p + q and its derivative have degrees
// summing below the degree sum of any two of p, q and p + q.
var MasonStothers = masonStothersThm{family.Add(registry.ProofEntry{
	Name: "MasonStothers",
	Reading: "Coprimality is load-bearing: over ℚ, p = q = t³ with d = e = f = t² " +
		"meet the divisibility hypotheses, and 6 < 6 fails. So is the hypothesis on " +
		"the derivatives, which is weaker than nonconstancy: in characteristic ℓ ≠ 2, " +
		"p = t^ℓ and q = (t + 1)^ℓ with d = p, e = q and f = (2t + 1)^ℓ give 3ℓ < 2ℓ.",
	Key: "prop_547b21021813be2b",
	Deps: []registry.EntryLike{
		WronskianNonzero,
		WronskianDivisorProduct,
		WronskianSum,
		WronskianVec,
		WronskianOver,
		polynomial_division.DividesDegree,
		polynomial.DegreeMul,
		polynomial.DegreeBelow,
		polynomial.PolynomialMulOver,
		integral_domain.FieldIntegralDomain,
	},
	Build: family.Card(field.FieldOn.Statement(Statement{
		Binders: "∀p q d e f:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, p)",
			"polynomial_over(F.carrier, q)",
			"polynomial_over(F.carrier, d)",
			"polynomial_over(F.carrier, e)",
			"polynomial_over(F.carrier, f)",
			"polynomial_coprime(field_ring(F), p, q)",
			"¬(polynomial_derivative(p) = vec_zero ∧ polynomial_derivative(q) = vec_zero)",
			"polynomial_divides(field_ring(F), d, p)",
			"polynomial_divides(field_ring(F), d, polynomial_derivative(p))",
			"polynomial_divides(field_ring(F), e, q)",
			"polynomial_divides(field_ring(F), e, polynomial_derivative(q))",
			"polynomial_divides(field_ring(F), f, p + q)",
			"polynomial_divides(field_ring(F), f, polynomial_derivative(p + q))",
		},
		Conclusion: "polynomial_degree(d) + polynomial_degree(e) + polynomial_degree(f) < " +
			"polynomial_degree(p) + polynomial_degree(q) ∧ " +
			"polynomial_degree(d) + polynomial_degree(e) + polynomial_degree(f) < " +
			"polynomial_degree(p) + polynomial_degree(p + q) ∧ " +
			"polynomial_degree(d) + polynomial_degree(e) + polynomial_degree(f) < " +
			"polynomial_degree(q) + polynomial_degree(p + q)",
	}),
		"Snyder's argument. W = W(p, q) is nonzero (WronskianNonzero) and "+
			"polynomial_mul(polynomial_mul(d, e), f) divides it (WronskianDivisorProduct), "+
			"so d, e and f are nonzero, and deg d + deg e + deg f, the degree of the product "+
			"(DegreeMul in the domain the field is), is at most deg W (DividesDegree); W is "+
			"also W(p, p + q) and W(p + q, q) (WronskianSum), and vanishes from the degree "+
			"sum of each pair (WronskianVec), so deg W is below each sum (DegreeBelow)"),
})}

// ---------------------------------------------------------------------------
// Fermat's equation and Davenport's bound
// ---------------------------------------------------------------------------

// FermatPolynomial — Fermat's equation over the polynomials of a field:
// for an exponent n ≥ 3 that is not zero in the field, a solution with x
// and y coprime has x, y and z all of zero derivative.
var FermatPolynomial = fermatPolynomialThm{family.Add(registry.ProofEntry{
	Name: "FermatPolynomial",
	Reading: "The hypotheses on n are load-bearing: in characteristic 3, t³ " +
		"+ 1³ = (t + 1)³ with t' = 1, and at n = 2, (t² − 1)² + (2t)² = (t² + " +
		"1)². Coprimality is what excludes x = y = t with z = a • t for a^n = 2.",
	Key: "prop_288bf0591115ebb8",
	Deps: []registry.EntryLike{
		MasonStothers,
		polynomial.PowDerivativeZero,
		polynomial.DerivativeAdd,
		polynomial.DerivativeOver,
		polynomial_division.CoprimePow,
		polynomial.DerivativePow,
		polynomial.PolynomialMulScalar,
		polynomial.DegreePow,
		polynomial.PolynomialPowOver,
		integral_domain.FieldIntegralDomain,
	},
	Build: family.Card(field.FieldOn.Statement(Statement{
		Binders: "∀n:num. ∀x y z:(num → A).",
		Hypotheses: []string{
			"3 ≤ n",
			"¬(monoid_pow(F.add, F.zero, F.one, n) = F.zero)",
			"polynomial_over(F.carrier, x)",
			"polynomial_over(F.carrier, y)",
			"polynomial_over(F.carrier, z)",
			"polynomial_coprime(field_ring(F), x, y)",
			"polynomial_pow(x, n) + polynomial_pow(y, n) = polynomial_pow(z, n)",
		},
		Conclusion: "polynomial_derivative(x) = vec_zero ∧ " +
			"polynomial_derivative(y) = vec_zero ∧ " +
			"polynomial_derivative(z) = vec_zero",
	}),
		"write n = suc(m). If the n-th powers of x and y both have F.zero derivative, so do "+
			"x and y (PowDerivativeZero), and so does z, the derivative of polynomial_pow(z, n) "+
			"being their sum (DerivativeAdd). Otherwise MasonStothers applies to p = "+
			"polynomial_pow(x, n) and q = polynomial_pow(y, n), coprime by CoprimePow, with d, e "+
			"and f the m-th powers of x, y and z, each dividing its n-th power and that power's "+
			"derivative (DerivativePow, PolynomialMulScalar); with X, Y, Z the degrees of x, y, "+
			"z and S = X + Y + Z, its three inequalities read m S < n X + n Y, m S < n X + n Z "+
			"and m S < n Y + n Z (DegreePow), whose sum 3 m S + 3 ≤ 2 (m + 1) S fails for m ≥ 2"),
})}

// DavenportCoprime — Davenport's bound for coprime f and g over a field
// in which 3 is not zero: when f has a nonzero derivative, f³ − g² has
// degree at least half the degree of f, plus one.
var DavenportCoprime = davenportCoprimeThm{family.Add(registry.ProofEntry{
	Name: "DavenportCoprime",
	Reading: "3 ≠ F.zero is load-bearing: over 𝔽₃, f = t² + t and g = (t − 1)³ are coprime " +
		"with f' = 2t + 1 ≠ 0, and f³ − g² = 2 is constant. So is f' ≠ 0, which is stronger " +
		"than f nonconstant: in characteristic 2, f = t² and g = t³ + 1 give f³ − g² = 1.",
	Key: "prop_7039f25b386672bb",
	Deps: []registry.EntryLike{
		MasonStothers,
		polynomial_division.CoprimePow,
		polynomial_division.CoprimeSymm,
		polynomial_division.CoprimeSum,
		polynomial.PowDerivativeZero,
		polynomial.DerivativePow,
		polynomial.PolynomialMulScalar,
		polynomial.DegreePow,
		polynomial.DegreeBasisVector,
		polynomial.PolynomialPowOver,
		polynomial.BasisVectorOver,
		polynomial.PolynomialRingOn,
		integral_domain.FieldIntegralDomain,
	},
	Build: family.Card(field.FieldOn.Statement(Statement{
		Binders: "∀f g:(num → A).",
		Hypotheses: []string{
			"polynomial_over(F.carrier, f)",
			"polynomial_over(F.carrier, g)",
			"polynomial_coprime(field_ring(F), f, g)",
			"¬(polynomial_derivative(f) = vec_zero)",
			"¬(monoid_pow(F.add, F.zero, F.one, 3) = F.zero)",
		},
		Conclusion: "polynomial_degree(f) + 2 ≤ " +
			"2 * polynomial_degree(polynomial_pow(f, 3) - polynomial_pow(g, 2))",
	}),
		"MasonStothers at p = polynomial_pow(g, 2) and q = h = polynomial_pow(f, 3) - polynomial_pow(g, "+
			"2), so that p + q = polynomial_pow(f, 3) in the ring of polynomials over F.carrier "+
			"(PolynomialRingOn), with divisors g, basis_vector(0) and polynomial_pow(f, 2) (DerivativePow, "+
			"PolynomialMulScalar): p and q are coprime (CoprimeSymm, CoprimePow, CoprimeSum), and not both "+
			"of F.zero derivative, else polynomial_pow(f, 3) would be and then f (PowDerivativeZero); with "+
			"F, G, H the degrees of f, g, h (DegreePow, DegreeBasisVector), its first and third "+
			"inequalities read G + 2 F < 2 G + H and G + 2 F < H + 3 F, whose sum is F + 2 ≤ 2 H"),
})}
