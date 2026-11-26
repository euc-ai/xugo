package integral_element

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegralOverDef = integralOverDefThm{family.Define(registry.DefEntry{
	Name:  "IntegralOverDef",
	Key:   "prop_d109d5833c6f1af6",
	Deps:  []registry.EntryLike{},
	Const: "integral_over",
	Type:  "ring_ops(A) → A → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀x:A. " +
			"    integral_over(R, x) ⇔ " +
			"    ∃p:(num → A). " +
			"        polynomial_over(R.zero, R.carrier, p) ∧ " +
			"        polynomial_monic(R.zero, R.one, p) ∧ " +
			"        0 < polynomial_degree(R.zero, p) ∧ " +
			"        polynomial_eval(R.add, R.zero, R.mul, R.one, p, x) = R.zero",
	},
})}

var IntegrallyClosedDef = integrallyClosedDefThm{family.Define(registry.DefEntry{
	Name:  "IntegrallyClosedDef",
	Key:   "prop_8a7dadc7680afa3a",
	Deps:  []registry.EntryLike{IntegralOverDef},
	Const: "integrally_closed_in",
	Type:  "ring_ops(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀L:set(A). " +
			"    integrally_closed_in(R, L) ⇔ (∀x:A. x ∈ L ∧ integral_over(R, x) ⇒ x ∈ R.carrier)",
	},
})}

var BoundedFractionalDef = boundedFractionalDefThm{family.Define(registry.DefEntry{
	Name:  "BoundedFractionalDef",
	Key:   "prop_c17d398606fea2c2",
	Deps:  []registry.EntryLike{},
	Const: "bounded_fractional",
	Type:  "ring_ops(A) → set(A) → set(A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀S I:set(A). " +
			"    bounded_fractional(R, S, I) ⇔ " +
			"    submodule(restrict_ring(R, S), regular_module(R), I) ∧ " +
			"    I ≠ {R.zero} ∧ " +
			"    (∃d:A. d ∈ S ∧ d ≠ R.zero ∧ image(R.mul(d), I) ⊆ S)",
	},
})}

// IntegralClosureDef — `integral_closure(R, K)`: the members of K integral
// over the ring R.
var IntegralClosureDef = integralClosureDefThm{family.Define(registry.DefEntry{
	Name:  "IntegralClosureDef",
	Key:   "prop_4fac70c536845090",
	Deps:  []registry.EntryLike{IntegralOverDef},
	Const: "integral_closure",
	Type:  "ring_ops(A) → set(A) → set(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀K:set(A). integral_closure(R, K) = {x:A | x ∈ K ∧ integral_over(R, x)}",
	},
	Reading: "For R a subring of a field and K a subfield holding it, the " +
		"integral closure of R in K; integrally_closed_in(R, K) says it is R's carrier.",
})}
