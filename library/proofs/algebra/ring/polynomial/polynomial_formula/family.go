package polynomial_formula

import (
	_ "embed"

	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/registry"
)

//go:embed polynomial_formula.cnf.pb
var familyCNF []byte

// family is the family handle. Its table names the terms the statements
// about a polynomial p in one variable v share: the lowering of a monomial
// (its exponent of v zeroed), the fibre of p's monomials of exponent k at
// v, and the exponents of v that occur in p; the parameter ring on a set U
// of variables, the integer polynomial ring restricted to the polynomials
// on U, «parameterRing»(U); the univariate polynomials over the parameter
// polynomials, those on U, «overParameters»; the specialization at ρ of a
// polynomial g over the parameter polynomials, its coefficients evaluated
// in a ring R, «specialized»(R, ρ, g), which at the coefficient family of p
// in v is p's coefficients in v specialized at ρ, and its value at a point
// x of a field F, «value»(F, ρ, g, x), the specialization read at F's ring;
// and the atoms that read a predicate P off the value of their polynomial
// in a ring R, «predicateAtoms»(R, P), read at the type R is a ring on, so
// that the statements carrying one ring into another name the atoms of both
// rings by it.
var family = registry.NewFamily(
	"algebra/ring/polynomial/polynomial_formula", familyCNF).WithAbbrev(Abbrev{
	{Name: "lower", Text: "λm:(num → num). λi:num. COND(i = v, 0, m(i))"},
	{Name: "fibre", Text: "λk:num. {m:(num → num) | m ∈ fun_support(int_of_num(0), p) ∧ m(v) = k}"},
	{Name: "exponents", Text: "image(λm:(num → num). m(v), fun_support(int_of_num(0), p))"},
	{Name: "parameterRing", Text: "λU:set(num). " +
		"    restrict_ring(integer_polynomial_ring, polynomial_algebra(int_ring, U))"},
	{Name: "overParameters", Text: "λf:(num → ((num → num) → int)). " +
		"    polynomial_over(integer_polynomial_ring.zero, polynomial_algebra(int_ring, U), f)"},
	{Name: "specialized", Text: "λR:ring_ops(A). " +
		"λρ:(num → A). " +
		"λg:(num → ((num → num) → int)). " +
		"λi:num. " +
		"    integer_polynomial_eval(R, ρ, g(i))"},
	{Name: "value", Text: "λF:field_ops(A). λρ:(num → A). λg:(num → ((num → num) → int)). λx:A. " +
		"    polynomial_eval(F.add, F.zero, F.mul, F.one, «specialized»(field_ring(F), ρ, g), x)"},
	{Name: "predicateAtoms", Text: "λR:ring_ops(A). " +
		"λP:(A → bool). " +
		"λp:((num → num) → int). " +
		"λτ:(num → A). " +
		"    P(integer_polynomial_eval(R, τ, p))"},
})

// ChapterAbbrev is the chapter's table as the chapters that read under
// it name it (registry.Family.WithOuterAbbrev).
var ChapterAbbrev = family.ChapterAbbrev()
