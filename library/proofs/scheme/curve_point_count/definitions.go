package curve_point_count

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

var CurveRationalPointCountDef = curveRationalPointCountDefThm{family.Define(registry.DefEntry{
	Name: "CurveRationalPointCountDef",
	Key:  "prop_22ab96e634897ba8",
	Reading: "This counts actual normalized evaluation maps on the two charts, with " +
		"overlap counted once. No weighted closed-point formula occurs in the definition.",
	Deps:  []registry.EntryLike{},
	Const: "curve_rational_point_count",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → set(A) → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k l A₀ A₁ A₀₁:set(A). " +
			"    curve_rational_point_count(R, k, l, A₀, A₁, A₀₁) = " +
			"    card(algebra_points(restrict_ring(R, A₀), restrict_ring(R, l), k, (λx:A. x))) + " +
			"    card(algebra_points(restrict_ring(R, A₁), restrict_ring(R, l), k, (λx:A. x))) - " +
			"    card(algebra_points(restrict_ring(R, A₀₁), restrict_ring(R, l), k, (λx:A. x)))",
	},
})}

var CurveExtensionCountDef = curveExtensionCountDefThm{family.Define(registry.DefEntry{
	Name: "CurveExtensionCountDef",
	Key:  "prop_42dbfa40b6b0f27d",
	Reading: "R.carrier is the algebraically closed extension host in point-count " +
		"theorems, not the function field of the curve. The charts and k are subobjects of " +
		"that host; finite_constants is taken in the host so actual extensions are available.",
	Deps:  []registry.EntryLike{CurveRationalPointCountDef},
	Const: "curve_extension_count",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → set(A) → num → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁ A₀₁:set(A). ∀m:num. " +
			"    curve_extension_count(R, k, A₀, A₁, A₀₁, m) = " +
			"    COND(m = 0, " +
			"        0, " +
			"        curve_rational_point_count(R, k, finite_constants(R, card(k), m), A₀, A₁, A₀₁))",
	},
})}

var CurveEvaluationPointsDef = curveEvaluationPointsDefThm{family.Define(registry.DefEntry{
	Name:  "CurveEvaluationPointsDef",
	Key:   "prop_3507f07b3144d0ee",
	Deps:  []registry.EntryLike{},
	Const: "curve_evaluation_points",
	Type:  "field_ops(A) → set(A) → set(A) → A → set(A) → set(A) → (set(prod(bool, A → A)))",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀l:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀t:A. " +
			"    curve_evaluation_points(R, k, l, t, A₀, A₁) = " +
			"    {p:prod(bool, A → A) | " +
			"        (¬fst(p) ∧ " +
			"            snd(p) ∈ " +
			"            algebra_points(restrict_ring(field_ring(R), A₀), " +
			"                restrict_ring(field_ring(R), l), " +
			"                k, " +
			"                (λa:A. a))) ∨ " +
			"        (fst(p) ∧ " +
			"            snd(p) ∈ " +
			"            algebra_points(restrict_ring(field_ring(R), A₁), " +
			"                restrict_ring(field_ring(R), l), " +
			"                k, " +
			"                (λa:A. a)) ∧ " +
			"            snd(p, R.inv(t)) = R.zero)}",
	},
})}
