package hilbert_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

var SeminormDef = seminormDefThm{family.DefineStructure(registry.DefEntry{
	Name:  "SeminormDef",
	Key:   "prop_b8eec26059652128",
	Const: "complex_seminorm",
	Type:  "module_ops(complex, A) → (A → real) → bool",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). " +
			"    complex_seminorm(M, v) ⇔ " +
			"    module_on(complex_ring, M) ∧ " +
			"    v(M.zero) = &0 ∧ " +
			"    (∀x:A. x ∈ M.carrier ⇒ &0 ≤ v(x)) ∧ " +
			"    (∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ v(M.add(x, y)) ≤ v(x) + v(y)) ∧ " +
			"    (∀c:complex. ∀x:A. x ∈ M.carrier ⇒ v(M.smul(c, x)) = |c| * v(x))",
	},
})}

var SeminormKernelDef = seminormKernelDefThm{family.Define(registry.DefEntry{
	Name:  "SeminormKernelDef",
	Key:   "prop_2b9f2745e4f1da51",
	Const: "seminorm_kernel",
	Type:  "module_ops(complex, A) → (A → real) → set(A)",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀v:(A → real). " +
			"    seminorm_kernel(M, v) = {x:A | x ∈ M.carrier ∧ v(x) = &0}",
	},
})}

var QuotientNormDef = quotientNormDefThm{family.Define(registry.DefEntry{
	Name:      "QuotientNormDef",
	Key:       "prop_9155ea3e1c61a065",
	Const:     "quotient_norm",
	Type:      "(A → real) → set(A) → real",
	Equations: []string{"∀v:(A → real). ∀Q:set(A). quotient_norm(v, Q) = induced_map(v, Q)"},
})}

var SemiInnerDef = semiInnerDefThm{family.DefineStructure(registry.DefEntry{
	Name:  "SemiInnerDef",
	Key:   "prop_ba73dc4e8bb9cbf0",
	Const: "complex_semi_inner",
	Type:  "module_ops(complex, A) → (A → A → complex) → bool",
	Reading: "The first variable is complex linear and the second is conjugate " +
		"linear. The diagonal is nonnegative; separation is imposed only after quotienting.",
	Equations: []string{
		"∀M:module_ops(complex, A). ∀p:(A → A → complex). " +
			"    complex_semi_inner(M, p) ⇔ " +
			"    module_on(complex_ring, M) ∧ " +
			"    (∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ p(x, y) = complex_conj(p(y, x))) ∧ " +
			"    (∀x y z:A. " +
			"        x ∈ M.carrier ∧ y ∈ M.carrier ∧ z ∈ M.carrier ⇒ " +
			"        p(M.add(x, y), z) = p(x, z) + p(y, z)) ∧ " +
			"    (∀c:complex. ∀x y:A. x ∈ M.carrier ∧ y ∈ M.carrier ⇒ p(M.smul(c, x), y) = c * p(x, y)) ∧ " +
			"    (∀x:A. x ∈ M.carrier ⇒ &0 ≤ re(p(x, x)))",
	},
})}

var QuotientInnerDef = quotientInnerDefThm{family.Define(registry.DefEntry{
	Name:  "QuotientInnerDef",
	Key:   "prop_78165fb18a2db4a2",
	Const: "quotient_inner",
	Type:  "(A → A → complex) → set(A) → set(A) → complex",
	Equations: []string{
		"∀p:(A → A → complex). ∀Q R:set(A). " +
			"    quotient_inner(p, Q, R) = induced_map(λx:A. induced_map(p(x), R), Q)",
	},
})}
