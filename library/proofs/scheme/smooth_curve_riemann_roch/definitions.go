package smooth_curve_riemann_roch

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
	_ "github.com/euc-ai/xugo/library/proofs/scheme/closed_divisor"
	_ "github.com/euc-ai/xugo/library/proofs/sets/weighted_divisors"
	"github.com/euc-ai/xugo/library/registry"
)

var CanonicalDivisorDef = canonicalDivisorDefThm{family.Define(registry.DefEntry{
	Name:  "CanonicalDivisorDef",
	Key:   "prop_d112177c7679c9a3",
	Deps:  []registry.EntryLike{},
	Const: "curve_canonical_divisor",
	Type:  "field_ops(A) → set(A) → A → set(A) → set(A) → set(A) → prod(set(A), set(A)) → int",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀A₀:set(A). ∀A₁:set(A). ∀A₀₁:set(A). ∀t:A. " +
			"    curve_canonical_divisor(R, k, t, A₀, A₁, A₀₁) = " +
			"    εD:(prod(set(A), set(A)) → int). " +
			"        closed_divisor(field_ring(R), A₀, A₁, A₀₁, D) ∧ " +
			"        dualizing_model(R, k, t, A₀, A₁, A₀₁, closed_divisor_pair(field_ring(R), A₀, A₁, A₀₁, D))",
	},
})}
