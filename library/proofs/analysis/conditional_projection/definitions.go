package conditional_projection

import (
	"github.com/euc-ai/xugo/library/registry"
)

var CondExpDef = condExpDefThm{family.Define(registry.DefEntry{
	Name:  "CondExpDef",
	Key:   "prop_2279954ded434bb9",
	Const: "cond_exp",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"(A → real) → " +
		"(A → real)",
	Reading: "This is a choice from the relation, with no existence " +
		"theorem used by the definition. Its conditional-expectation meaning is " +
		"asserted by CondExpSpecification under finite measure and integrability.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G:set(set(A)). ∀X:(A → real). " +
			"    cond_exp(Ω, S, μ, G, X) = εY:(A → real). is_cond_exp(Ω, S, μ, G, X, Y)",
	},
})}

var complexCondExpDef = complexCondExpDefThm{family.Define(registry.DefEntry{
	Name:  "complexCondExpDef",
	Key:   "prop_fef1c0918e94b0d5",
	Const: "complex_cond_exp",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"(A → complex) → " +
		"(A → complex)",
	Deps: []registry.EntryLike{CondExpDef},
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀f:(A → complex). " +
			"∀x:A. " +
			"    complex_cond_exp(Ω, S, μ, G, f, x) = " +
			"    complex_of_real(cond_exp(Ω, S, μ, G, λy:A. re(f(y)), x)) + " +
			"    complex_i * complex_of_real(cond_exp(Ω, S, μ, G, λy:A. im(f(y)), x))",
	},
})}

var conditionalClassDef = conditionalClassDefThm{family.Define(registry.DefEntry{
	Name:  "conditionalClassDef",
	Key:   "prop_7cf353d225d532ef",
	Const: "conditional_class",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"set(A → complex) → " +
		"set(A → complex)",
	Deps: []registry.EntryLike{complexCondExpDef},
	Equations: []string{
		"∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀G:set(set(A)). " +
			"∀Q:set(A → complex). " +
			"    conditional_class(Ω, S, μ, G, Q) = " +
			"    induced_map(λf:(A → complex). ae_class(Ω, S, μ, complex_cond_exp(Ω, S, μ, G, f)), Q)",
	},
})}
