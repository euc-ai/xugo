// definitions.go — the local ring at a point of a curve over the line, and the
// order, evaluation and pole spaces read off it.

package regular_point

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// PointLocalRingDef — `point_local_ring(R, A₀, A₁, P)`: the localization of
// P's chart point_chart(A₀, A₁, P) at P's ideal point_ideal(A₀, P), the
// fractions a/b of the chart with b off the ideal.
var PointLocalRingDef = pointLocalRingDefThm{family.Define(registry.DefEntry{
	Name:  "PointLocalRingDef",
	Key:   "prop_4c8f647769304887",
	Deps:  []registry.EntryLike{},
	Const: "point_local_ring",
	Type:  "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). " +
			"    point_local_ring(R, A₀, A₁, P) = " +
			"    subring_localization(R, point_chart(A₀, A₁, P), point_ideal(A₀, P))",
	},
})}

// RegularPointOrderDef — `regular_point_order(R, A₀, A₁, P, f)`: an exponent
// n with f times the local ring at P equal to the n-th signed power of the
// ideal P's ideal generates there; a choice, unique where one exists
// (OrderAtRegularPoint).
var RegularPointOrderDef = regularPointOrderDefThm{family.Define(registry.DefEntry{
	Name:  "RegularPointOrderDef",
	Key:   "prop_733655508e1a2cd5",
	Deps:  []registry.EntryLike{PointLocalRingDef},
	Const: "regular_point_order",
	Type:  "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → A → int",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). ∀f:A. " +
			"    regular_point_order(R, A₀, A₁, P, f) = " +
			"    εn:int. " +
			"        image(R.mul(f), point_local_ring(R, A₀, A₁, P)) = " +
			"        signed_ideal_power(R, " +
			"            point_local_ring(R, A₀, A₁, P), " +
			"            ideal_span(restrict_ring(R, point_local_ring(R, A₀, A₁, P)), point_ideal(A₀, P)), " +
			"            n)",
	},
})}

// RegularPointEvaluationDef — `regular_point_evaluation(R, k, A₀, A₁, P, f)`:
// a constant c of k with f − c in the maximal ideal of the local ring at P; a
// choice, unique at a rational point (EvaluationAtRationalPoint).
var RegularPointEvaluationDef = regularPointEvaluationDefThm{family.Define(registry.DefEntry{
	Name:  "RegularPointEvaluationDef",
	Key:   "prop_7b7b6765abe4aab3",
	Deps:  []registry.EntryLike{PointLocalRingDef},
	Const: "regular_point_evaluation",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → A → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁:set(A). ∀P:prod(set(A), set(A)). ∀f:A. " +
			"    regular_point_evaluation(R, k, A₀, A₁, P, f) = " +
			"    εc:A. " +
			"        c ∈ k ∧ " +
			"        R.sub(f, c) ∈ " +
			"        ideal_span(restrict_ring(R, point_local_ring(R, A₀, A₁, P)), point_ideal(A₀, P))",
	},
})}

// SinglePointPoleSpaceDef — `single_point_pole_space(R, A₀, A₁, P, n)`, L(nP):
// H⁰ of the n-th power of P⁻¹, the functions with a pole of order at most n
// at P and regular everywhere else.
var SinglePointPoleSpaceDef = singlePointPoleSpaceDefThm{family.Define(registry.DefEntry{
	Name:  "SinglePointPoleSpaceDef",
	Key:   "prop_d1336c3a02c3b3a6",
	Deps:  []registry.EntryLike{},
	Const: "single_point_pole_space",
	Type:  "ring_ops(A) → set(A) → set(A) → prod(set(A), set(A)) → num → module_ops(A, A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁:set(A). ∀P:prod(set(A), set(A)). ∀n:num. " +
			"    single_point_pole_space(R, A₀, A₁, P, n) = " +
			"    lattice_pair_h0(regular_module(R), " +
			"        monoid_pow(λX:prod(set(A), set(A)). λY:prod(set(A), set(A)). " +
			"                lattice_pair_mul(R, A₀, A₁, X, Y), " +
			"            (A₀, A₁), " +
			"            lattice_pair_inverse(R, A₀, A₁, P), " +
			"            n))",
	},
})}
