package divisor_lattice_correspondence

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

var ClosedPrincipalDivisorDef = closedPrincipalDivisorDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedPrincipalDivisorDef",
	Key:   "prop_3a25ca5672b8650d",
	Deps:  []registry.EntryLike{},
	Const: "closed_principal_divisor",
	Type:  "ring_ops(A) → set(A) → set(A) → set(A) → A → prod(set(A), set(A)) → int",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀f:A. " +
			"    closed_principal_divisor(R, A₀, A₁, A₀₁, f) = " +
			"    εD:(prod(set(A), set(A)) → int). " +
			"        closed_divisor(R, A₀, A₁, A₀₁, D) ∧ " +
			"        closed_divisor_pair(R, A₀, A₁, A₀₁, D) = " +
			"        (fractional_inverse(R, A₀, image(R.mul(f), A₀)), " +
			"            fractional_inverse(R, A₁, image(R.mul(f), A₁)))",
	},
})}

var ClosedDivisorEquivalentDef = closedDivisorEquivalentDefThm{family.Define(registry.DefEntry{
	Name:  "ClosedDivisorEquivalentDef",
	Key:   "prop_868ce58824acd13f",
	Deps:  []registry.EntryLike{},
	Const: "closed_divisor_equivalent",
	Type: "ring_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"set(A) → " +
		"(prod(set(A), set(A)) → int) → " +
		"(prod(set(A), set(A)) → int) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀A₀ A₁ A₀₁:set(A). ∀D E:(prod(set(A), set(A)) → int). " +
			"    closed_divisor_equivalent(R, A₀, A₁, A₀₁, D, E) ⇔ " +
			"    curve_pair_class(R, closed_divisor_pair(R, A₀, A₁, A₀₁, D)) = " +
			"    curve_pair_class(R, closed_divisor_pair(R, A₀, A₁, A₀₁, E))",
	},
})}
