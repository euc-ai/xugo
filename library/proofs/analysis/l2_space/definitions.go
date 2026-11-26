package l2_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

var L2FunctionInnerDef = l2FunctionInnerDefThm{family.Define(registry.DefEntry{
	Name:  "L2FunctionInnerDef",
	Key:   "prop_5eb0f07dfe547698",
	Const: "l2_function_inner",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → complex) → " +
		"(A → complex) → " +
		"complex",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → complex). " +
			"    l2_function_inner(Ω, S, μ, f, g) = " +
			"    complex_measure_integral(Ω, S, μ, λx:A. f(x) * complex_conj(g(x)))",
	},
})}

var L2InnerDef = l2InnerDefThm{family.Define(registry.DefEntry{
	Name:  "L2InnerDef",
	Key:   "prop_8fb9b92ec87c62b0",
	Const: "l2_inner",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(A → complex) → " +
		"set(A → complex) → " +
		"complex",
	Deps: []registry.EntryLike{L2FunctionInnerDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Q R:set(A → complex). " +
			"    l2_inner(Ω, S, μ, Q, R) = quotient_inner(l2_function_inner(Ω, S, μ), Q, R)",
	},
})}
