package closed_divisor

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
	_ "github.com/euc-ai/xugo/library/proofs/scheme/smooth_curve"
	_ "github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

var ClosedDivisorDef = closedDivisorDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedDivisorDef",
	Key:   "prop_4193a7ed070a40b0",
	Deps:  []registry.EntryLike{},
	Const: "closed_divisor",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀D:(prod(set(A), set(A)) → int). " +
			"    closed_divisor(R, A₀, A₁, A₀₁, D) ⇔ " +
			"    finite(fun_support(int_of_num(0), D)) ∧ " +
			"    (∀P:prod(set(A), set(A)). D(P) ≠ 0 ⇒ curve_closed_point(R, A₀, A₁, A₀₁, P))",
	},
})}

var ClosedDivisorDegreeDef = closedDivisorDegreeDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedDivisorDegreeDef",
	Key:   "prop_ec6eb6a3c66702cc",
	Deps:  []registry.EntryLike{},
	Const: "closed_divisor_degree",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → (prod(set(A), set(A)) → int) → int",
	Equations: []string{
		"∀R:ring_ops(A). ∀k A₀ A₁:set(A). ∀D:(prod(set(A), set(A)) → int). " +
			"    closed_divisor_degree(R, k, A₀, A₁, D) = " +
			"    module_sum((λa:int. λb:int. a + b), " +
			"        0, " +
			"        fun_support(int_of_num(0), D), " +
			"        λP:prod(set(A), set(A)). D(P) * curve_closed_degree(R, k, A₀, A₁, P))",
	},
})}

var ClosedDivisorPairDef = closedDivisorPairDefThm{family.Define(registry.DefEntry{
	Name: "ClosedDivisorPairDef",
	Key:  "prop_38b1c1dd24979978",
	Reading: "The existing finite product on lattice pairs is reused. Its definition is " +
		"not restricted to rational points; the separate curve_divisor predicate is not used.",
	Deps:  []registry.EntryLike{},
	Const: "closed_divisor_pair",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"(prod(set(A), set(A)) → int) → " +
		"prod(set(A), set(A))",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀D:(prod(set(A), set(A)) → int). " +
			"    closed_divisor_pair(R, A₀, A₁, A₀₁, D) = curve_divisor_pair(R, A₀, A₁, A₀₁, D)",
	},
})}
