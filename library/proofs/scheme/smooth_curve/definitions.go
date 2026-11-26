package smooth_curve

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/function_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/algebra_points"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/fractional_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/integral_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_formal_series"
	_ "github.com/euc-ai/xugo/library/proofs/scheme/algebraic_curve"
	_ "github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

var SmoothFiniteFieldCurveDef = smoothFiniteFieldCurveDefThm{family.Define(registry.DefEntry{
	Name: "SmoothFiniteFieldCurveDef",
	Key:  "prop_ad98b50e4559ca98",
	Reading: "Over a perfect finite field, a normal integral curve is smooth: the " +
		"two charts integrally closed in R are the smoothness. No clause states that " +
		"the constants are exact: over a finite field they are, by NormalChartsRegular. " +
		"Normality is not inferred from a bare biaffine presentation.",
	Deps:  []registry.EntryLike{},
	Const: "smooth_finite_curve",
	Type:  "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀t:A. " +
			"    smooth_finite_curve(R, k, t, A₀, A₁, A₀₁) ⇔ " +
			"    curve_over_line(R, k, t, A₀, A₁, A₀₁) ∧ " +
			"    finite(k) ∧ " +
			"    integrally_closed_in(restrict_ring(field_ring(R), A₀), R.carrier) ∧ " +
			"    integrally_closed_in(restrict_ring(field_ring(R), A₁), R.carrier)",
	},
})}

var CurveClosedPointDef = curveClosedPointDefThm{family.Define(registry.DefEntry{
	Name:  "CurveClosedPointDef",
	Key:   "prop_76cc4250a8c7ea35",
	Deps:  []registry.EntryLike{},
	Const: "curve_closed_point",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀P:prod(set(A), set(A)). " +
			"    curve_closed_point(R, A₀, A₁, A₀₁, P) ⇔ " +
			"    (fst(P) = A₀ ∨ maximal_ideal(restrict_ring(R, A₀), fst(P))) ∧ " +
			"    (snd(P) = A₁ ∨ maximal_ideal(restrict_ring(R, A₁), snd(P))) ∧ " +
			"    ¬(fst(P) = A₀ ∧ snd(P) = A₁) ∧ " +
			"    ideal_span(restrict_ring(R, A₀₁), fst(P)) = ideal_span(restrict_ring(R, A₀₁), snd(P)) ∧ " +
			"    (fst(P) ≠ A₀ ∧ snd(P) ≠ A₁ ⇒ R.one ∉ ideal_span(restrict_ring(R, A₀₁), fst(P)))",
	},
})}

var ClosedPointDegreeDef = closedPointDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedPointDegreeDef",
	Key:   "prop_4605f5f29d6108ad",
	Deps:  []registry.EntryLike{},
	Const: "curve_closed_degree",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → prod(set(A), set(A)) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁:set(A). ∀P:prod(set(A), set(A)). " +
			"    curve_closed_degree(R, k, A₀, A₁, P) = " +
			"    module_dim(restrict_ring(R, k), " +
			"        quotient_module(restrict_module(regular_module(R), point_chart(A₀, A₁, P)), " +
			"            point_ideal(A₀, P)))",
	},
})}
