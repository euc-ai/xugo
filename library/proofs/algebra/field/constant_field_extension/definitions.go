package constant_field_extension

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

var ConstantChartDef = constantChartDefThm{family.Define(registry.DefEntry{
	Name:  "ConstantChartDef",
	Key:   "prop_a7933ac68654829d",
	Deps:  []registry.EntryLike{},
	Const: "constant_chart",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀l B:set(A). " +
			"    constant_chart(R, l, B) = module_span(restrict_ring(R, l), regular_module(R), B)",
	},
})}
