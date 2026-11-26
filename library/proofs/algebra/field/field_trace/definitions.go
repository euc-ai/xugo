// definitions.go — the chapter's definitions statements.

package field_trace

import (
	"github.com/euc-ai/xugo/library/registry"
)

// The polynomial ring and its two principal quotients, read in definition equations.
// Constant classes give the scalar action; the minimal-polynomial quotient
// carries the cofactor class divided by the derivative value.
const (
	ftDefPolynomialRing = "mk_ring(vec_add, vec_zero, vec_neg, polynomial_mul, " +
		"basis_vector(0), vec_sub, {h:(num → A) | polynomial_over(L.carrier, h)})"
	ftDefPrincipalIdeal = "ideal_span(mk_ring(vec_add, vec_zero, vec_neg, polynomial_mul, " +
		"basis_vector(0), vec_sub, {h:(num → A) | polynomial_over(L.carrier, h)}), {p})"
	ftDefQuotient = "ideal_quotient_ring(" +
		ftDefPolynomialRing +
		", " +
		ftDefPrincipalIdeal +
		")"
	ftDefConstantClass = "ideal_quotient_projection(" +
		ftDefPolynomialRing +
		", " +
		ftDefPrincipalIdeal +
		", vec_scalar_mul(a, basis_vector(0)))"
	ftDefMinimalPolynomial = "minimal_polynomial(L, K, y)"
	ftDefMinimalIdeal      = "ideal_span(mk_ring(vec_add, vec_zero, vec_neg, polynomial_mul, basis_vector(0), vec_sub, {h:(num → A) | polynomial_over(L.carrier, h)}), {" +
		ftDefMinimalPolynomial +
		"})"
	ftDefMinimalQuotient = "ideal_quotient_ring(" +
		ftDefPolynomialRing +
		", " +
		ftDefMinimalIdeal +
		")"
	ftDefCofactorClass = "ideal_quotient_projection(" +
		ftDefPolynomialRing +
		", " +
		ftDefMinimalIdeal +
		", trace_cofactor(L, K, y))"
	ftDefInverseDerivativeClass = "ideal_quotient_projection(" +
		ftDefPolynomialRing +
		", " +
		ftDefMinimalIdeal +
		", vec_scalar_mul(L.mul, L.inv(polynomial_eval(L.add, L.zero, L.mul, L.one, polynomial_derivative(L.add, L.zero, L.mul, L.one, " +
		ftDefMinimalPolynomial +
		"), y)), basis_vector(0)))"
)

// FieldTraceDef — The field trace is the trace of multiplication over the base field.
var FieldTraceDef = fieldTraceDefThm{family.Define(registry.DefEntry{
	Name:  "FieldTraceDef",
	Key:   "prop_509c107ddb178273",
	Const: "field_trace",
	Type:  "field_ops(A) → set(A) → A → A",

	Reading: "The trace uses a finite set basis of L over K. A finite extension and z in L " +
		"determine the value; nothing is claimed for an infinite extension or z outside the field.",
	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). ∀z:A. " +
			"    field_trace(L, K, z) = " +
			"    module_trace(restrict_ring(field_ring(L), K), regular_module(field_ring(L)), L.mul(z))",
	},
})}

// traceQuotientModuleDef — The polynomial quotient by a principal ideal, as a module under constant classes.
var traceQuotientModuleDef = traceQuotientModuleDefThm{family.Define(registry.DefEntry{
	Name:  "traceQuotientModuleDef",
	Key:   "prop_897f40b8614612d2",
	Const: "trace_quotient_module",
	Type:  "field_ops(A) → (num → A) → module_ops(A, set(num → A))",

	Equations: []string{"∀L:field_ops(A). ∀p:(num → A). trace_quotient_module(L, p) = mk_module(" +
		ftDefQuotient +
		".add, " +
		ftDefQuotient +
		".zero, " +
		ftDefQuotient +
		".neg, λa:A. λv:set(num → A). " +
		ftDefQuotient +
		".mul(" +
		ftDefConstantClass +
		", v), " +
		ftDefQuotient +
		".carrier)"},
})}

// traceCofactorDef — The polynomial cofactor of T−y in the minimal polynomial.
var traceCofactorDef = traceCofactorDefThm{family.Define(registry.DefEntry{
	Name:  "traceCofactorDef",
	Key:   "prop_ec6ebacc6b18fa45",
	Const: "trace_cofactor",
	Type:  "field_ops(A) → set(A) → A → num → A",

	Equations: []string{
		"∀L:field_ops(A). ∀K:set(A). ∀y:A. " +
			"    trace_cofactor(L, K, y) = " +
			"    εq:(num → A). " +
			"        polynomial_over(L.zero, L.carrier, q) ∧ " +
			"        polynomial_mul(L.add, " +
			"            L.zero, " +
			"            L.mul, " +
			"            vec_sub(L.sub, " +
			"                basis_vector(L.zero, L.one, 1), " +
			"                vec_scalar_mul(L.mul, y, basis_vector(L.zero, L.one, 0))), " +
			"            q) = " +
			"        minimal_polynomial(L, K, y)",
	},
})}

// traceIdempotentDef — The cofactor class scaled by the inverse derivative value.
var traceIdempotentDef = traceIdempotentDefThm{family.Define(registry.DefEntry{
	Name:  "traceIdempotentDef",
	Key:   "prop_6f4465bc45cc3f16",
	Const: "trace_idempotent",
	Type:  "field_ops(A) → set(A) → A → set(num → A)",

	Deps: []registry.EntryLike{traceCofactorDef},
	Equations: []string{"∀L:field_ops(A). ∀K:set(A). ∀y:A. trace_idempotent(L, K, y) = " +
		ftDefMinimalQuotient +
		".mul(" +
		ftDefCofactorClass +
		", " +
		ftDefInverseDerivativeClass +
		")"},
})}
