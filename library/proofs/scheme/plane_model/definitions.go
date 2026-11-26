package plane_model

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegralPlaneModelDef = integralPlaneModelDefThm{family.Define(registry.DefEntry{
	Name: "IntegralPlaneModelDef",
	Key:  "prop_d6a1d369eb4679e4",
	Reading: "The equation is represented at a generic root in its regular function field. Its " +
		"coefficients remain actual k[t] elements; separability and the weight bound are explicit.",
	Deps:  []registry.EntryLike{},
	Const: "integral_plane_model",
	Type:  "field_ops(A) → set(A) → A → A → (num → A) → num → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀t:A. ∀z:A. ∀F:(num → A). ∀b:num. " +
			"    integral_plane_model(R, k, t, z, F, b) ⇔ " +
			"    regular_function_field(R, k, R.carrier) ∧ " +
			"    t ∈ R.carrier ∧ " +
			"    ¬algebraic_over(R, k, t) ∧ " +
			"    z ∈ R.carrier ∧ " +
			"    field_adjoin(R, field_adjoin(R, k, {t}), {z}) = R.carrier ∧ " +
			"    F = minimal_polynomial(R, field_adjoin(R, k, {t}), z) ∧ " +
			"    polynomial_separable(restrict_ring(field_ring(R), field_adjoin(R, k, {t})), F) ∧ " +
			"    0 < polynomial_degree(R.zero, F) ∧ " +
			"    0 < b ∧ " +
			"    (∀i:num. " +
			"        i < polynomial_degree(R.zero, F) ⇒ " +
			"        ∃a:(num → A). " +
			"            polynomial_over(R.zero, k, a) ∧ " +
			"            polynomial_degree(R.zero, a) ≤ b * (polynomial_degree(R.zero, F) - i) ∧ " +
			"            polynomial_eval(R.add, R.zero, R.mul, R.one, a, t) = F(i))",
	},
})}

var PlaneChartZeroDef = planeChartZeroDefThm{family.Define(registry.DefEntry{
	Name:  "PlaneChartZeroDef",
	Key:   "prop_611315f8d502250c",
	Deps:  []registry.EntryLike{},
	Const: "plane_chart_zero",
	Type:  "ring_ops(A) → set(A) → A → A → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀t z:A. " +
			"    plane_chart_zero(R, k, t, z) = polynomial_image(R, polynomial_image(R, k, t), z)",
	},
})}

var PlaneChartOneDef = planeChartOneDefThm{family.Define(registry.DefEntry{
	Name:  "PlaneChartOneDef",
	Key:   "prop_c5e53258bccb97de",
	Deps:  []registry.EntryLike{PlaneChartZeroDef},
	Const: "plane_chart_one",
	Type:  "field_ops(A) → set(A) → A → A → num → set(A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀t:A. ∀z:A. ∀b:num. " +
			"    plane_chart_one(R, k, t, z, b) = " +
			"    plane_chart_zero(field_ring(R), k, R.inv(t), R.mul(monoid_pow(R.mul, R.one, R.inv(t), b), z))",
	},
})}

var AbsolutePlaneEquationDef = absolutePlaneEquationDefThm{family.Define(registry.DefEntry{
	Name:  "AbsolutePlaneEquationDef",
	Key:   "prop_d74a6d9189964397",
	Deps:  []registry.EntryLike{},
	Const: "absolute_plane_equation",
	Type:  "field_ops(A) → set(A) → (num → num → A) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀F:(num → num → A). " +
			"    absolute_plane_equation(R, k, F) ⇔ " +
			"    polynomial_over(polynomial_ring(restrict_ring(field_ring(R), k)).zero, " +
			"        polynomial_ring(restrict_ring(field_ring(R), k)).carrier, " +
			"        F) ∧ " +
			"    polynomial_monic(polynomial_ring(restrict_ring(field_ring(R), k)).zero, " +
			"        polynomial_ring(restrict_ring(field_ring(R), k)).one, " +
			"        F) ∧ " +
			"    0 < polynomial_degree(polynomial_ring(restrict_ring(field_ring(R), k)).zero, F) ∧ " +
			"    polynomial_irreducible(polynomial_ring( " +
			"            restrict_ring(field_ring(R), {x:A | x ∈ R.carrier ∧ algebraic_over(R, k, x)})), " +
			"        F) ∧ " +
			"    polynomial_derivative(polynomial_ring(restrict_ring(field_ring(R), k)).add, " +
			"        polynomial_ring(restrict_ring(field_ring(R), k)).zero, " +
			"        polynomial_ring(restrict_ring(field_ring(R), k)).mul, " +
			"        polynomial_ring(restrict_ring(field_ring(R), k)).one, " +
			"        F) ≠ " +
			"    (λi:num. polynomial_ring(restrict_ring(field_ring(R), k)).zero)",
	},
})}

var PlaneEquationCountDef = planeEquationCountDefThm{family.Define(registry.DefEntry{
	Name:  "PlaneEquationCountDef",
	Key:   "prop_5c064f199ad8d440",
	Deps:  []registry.EntryLike{},
	Const: "plane_equation_count",
	Type:  "ring_ops(A) → set(A) → (num → num → A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀l:set(A). ∀F:(num → num → A). " +
			"    plane_equation_count(R, l, F) = " +
			"    card({p:prod(A, A) | " +
			"            fst(p) ∈ l ∧ " +
			"            snd(p) ∈ l ∧ " +
			"            polynomial_eval(R.add, " +
			"                R.zero, " +
			"                R.mul, " +
			"                R.one, " +
			"                (λi:num. polynomial_eval(R.add, R.zero, R.mul, R.one, F(i), fst(p))), " +
			"                snd(p)) = " +
			"            R.zero})",
	},
})}

var PlaneGoodCertificateDef = planeGoodCertificateDefThm{family.Define(registry.DefEntry{
	Name:  "PlaneGoodCertificateDef",
	Key:   "prop_610190f70d3bcdc0",
	Deps:  []registry.EntryLike{},
	Const: "plane_good_certificate",
	Type:  "ring_ops(A) → set(A) → A → (num → A) → (num → A) → (num → A) → (num → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀t:A. ∀F a U V:(num → A). " +
			"    plane_good_certificate(R, k, t, F, a, U, V) ⇔ " +
			"    polynomial_over(R.zero, k, a) ∧ " +
			"    a ≠ vec_zero(R.zero) ∧ " +
			"    polynomial_over(R.zero, polynomial_image(R, k, t), U) ∧ " +
			"    polynomial_over(R.zero, polynomial_image(R, k, t), V) ∧ " +
			"    vec_add(R.add, " +
			"        polynomial_mul(R.add, R.zero, R.mul, U, F), " +
			"        polynomial_mul(R.add, " +
			"            R.zero, " +
			"            R.mul, " +
			"            V, " +
			"            polynomial_derivative(R.add, R.zero, R.mul, R.one, F))) = " +
			"    vec_scalar_mul(R.mul, " +
			"        polynomial_eval(R.add, R.zero, R.mul, R.one, a, t), " +
			"        basis_vector(R.zero, R.one, 0))",
	},
})}
