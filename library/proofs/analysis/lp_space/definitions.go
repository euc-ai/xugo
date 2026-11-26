package lp_space

import (
	"github.com/euc-ai/xugo/library/registry"
)

var LpSeminormDef = lpSeminormDefThm{family.Define(registry.DefEntry{
	Name:  "LpSeminormDef",
	Key:   "prop_4cf5012a5e4a3c5e",
	Const: "lp_seminorm",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → real → (A → complex) → real",
	Reading: "The finite exponent is a value, not a type index. This total function is " +
		"used as a seminorm only on measurable functions with finite pth-power integral and p≥1.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. ∀f:(A → complex). " +
			"    lp_seminorm(Ω, S, μ, p, f) = " +
			"    real_rpow(extended_to_real( " +
			"            nonneg_integral(Ω, S, μ, λx:A. extended_of_real(real_rpow(|f(x)|, p)))), " +
			"        real_inv(p))",
	},
})}

var LpFunctionsDef = lpFunctionsDefThm{family.Define(registry.DefEntry{
	Name:  "LpFunctionsDef",
	Key:   "prop_68b8788e3cec5a0c",
	Const: "lp_functions",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → real → set(A → complex)",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. " +
			"    lp_functions(Ω, S, μ, p) = " +
			"    {f:(A → complex) | " +
			"        f ∈ measurable_functions(Ω, S) ∧ " +
			"        nonneg_integral(Ω, S, μ, λx:A. extended_of_real(real_rpow(|f(x)|, p))) ≠ " +
			"        extended_infinity}",
	},
})}

var LpFunctionModuleDef = lpFunctionModuleDefThm{family.Define(registry.DefEntry{
	Name:  "LpFunctionModuleDef",
	Key:   "prop_7a91cdfd41a93b8",
	Const: "lp_function_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"real → " +
		"module_ops(complex, A → complex)",
	Deps: []registry.EntryLike{LpFunctionsDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. " +
			"    lp_function_module(Ω, S, μ, p) = " +
			"    restrict_module(measurable_function_module(Ω, S), lp_functions(Ω, S, μ, p))",
	},
})}

var LpModuleDef = lpModuleDefThm{family.Define(registry.DefEntry{
	Name:  "LpModuleDef",
	Key:   "prop_b4cb762b6c62d8cc",
	Const: "lp_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"real → " +
		"module_ops(complex, set(A → complex))",
	Deps: []registry.EntryLike{LpFunctionModuleDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. " +
			"    lp_module(Ω, S, μ, p) = " +
			"    quotient_module(lp_function_module(Ω, S, μ, p), null_functions(Ω, S, μ))",
	},
})}

var LpNormDef = lpNormDefThm{family.Define(registry.DefEntry{
	Name:  "LpNormDef",
	Key:   "prop_e3d1cb042aa585e0",
	Const: "lp_norm",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"real → " +
		"set(A → complex) → " +
		"real",
	Deps: []registry.EntryLike{LpSeminormDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. ∀Q:set(A → complex). " +
			"    lp_norm(Ω, S, μ, p, Q) = induced_map(lp_seminorm(Ω, S, μ, p), Q)",
	},
})}

var LpMeasurableSubspaceDef = lpMeasurableSubspaceDefThm{family.Define(registry.DefEntry{
	Name:  "LpMeasurableSubspaceDef",
	Key:   "prop_db3ed57c891a4fb4",
	Const: "lp_measurable_subspace",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(set(A)) → " +
		"real → " +
		"set(set(A → complex))",
	Deps: []registry.EntryLike{LpModuleDef},
	Reading: "This is the image of the smaller-sigma quotient under the " +
		"ambient inclusion. Its elements have a G-measurable representative; " +
		"a chosen S-measurable representative need not itself be G-measurable.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. ∀G:set(set(A)). " +
			"    lp_measurable_subspace(Ω, S, μ, G, p) = " +
			"    image(ae_inclusion(Ω, S, μ), lp_module(Ω, G, μ, p).carrier)",
	},
})}

var LpIntegralDef = lpIntegralDefThm{family.Define(registry.DefEntry{
	Name:  "LpIntegralDef",
	Key:   "prop_d9cb45376d3672a5",
	Const: "lp_integral",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A → complex) → complex",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Q:set(A → complex). " +
			"    lp_integral(Ω, S, μ, Q) = induced_map(complex_measure_integral(Ω, S, μ), Q)",
	},
})}

var EssentialSupDef = essentialSupDefThm{family.Define(registry.DefEntry{
	Name:  "EssentialSupDef",
	Key:   "prop_1879e92d4a7545af",
	Const: "essential_sup",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → complex) → " +
		"extended_nonneg_real",
	Reading: "The empty set of finite essential bounds has infimum infinity; " +
		"the seminorm reads the finite value only on the essentially bounded carrier.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex). " +
			"    essential_sup(Ω, S, μ, f) = " +
			"    extended_inf({r:extended_nonneg_real | " +
			"            ∃C:real. &0 ≤ C ∧ r = extended_of_real(C) ∧ measure_ae(Ω, S, μ, λx:A. |f(x)| ≤ C)})",
	},
})}

var LInfinityFunctionsDef = lInfinityFunctionsDefThm{family.Define(registry.DefEntry{
	Name:  "LInfinityFunctionsDef",
	Key:   "prop_e3f65a7a4147b400",
	Const: "linfinity_functions",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A → complex)",
	Deps:  []registry.EntryLike{EssentialSupDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    linfinity_functions(Ω, S, μ) = " +
			"    {f:(A → complex) | " +
			"        f ∈ measurable_functions(Ω, S) ∧ essential_sup(Ω, S, μ, f) ≠ extended_infinity}",
	},
})}

var LInfinityFunctionModuleDef = lInfinityFunctionModuleDefThm{family.Define(registry.DefEntry{
	Name:  "LInfinityFunctionModuleDef",
	Key:   "prop_87229049d471e5d7",
	Const: "linfinity_function_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"module_ops(complex, A → complex)",
	Deps: []registry.EntryLike{LInfinityFunctionsDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    linfinity_function_module(Ω, S, μ) = " +
			"    restrict_module(measurable_function_module(Ω, S), linfinity_functions(Ω, S, μ))",
	},
})}

var LInfinityModuleDef = lInfinityModuleDefThm{family.Define(registry.DefEntry{
	Name:  "LInfinityModuleDef",
	Key:   "prop_1a09cd8b3d55701c",
	Const: "linfinity_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"module_ops(complex, set(A → complex))",
	Deps: []registry.EntryLike{LInfinityFunctionModuleDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    linfinity_module(Ω, S, μ) = " +
			"    quotient_module(linfinity_function_module(Ω, S, μ), null_functions(Ω, S, μ))",
	},
})}

var LInfinityNormDef = lInfinityNormDefThm{family.Define(registry.DefEntry{
	Name:  "LInfinityNormDef",
	Key:   "prop_d2633d6ebb05fa0e",
	Const: "linfinity_norm",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A → complex) → real",
	Deps:  []registry.EntryLike{EssentialSupDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Q:set(A → complex). " +
			"    linfinity_norm(Ω, S, μ, Q) = " +
			"    induced_map(λf:(A → complex). extended_to_real(essential_sup(Ω, S, μ, f)), Q)",
	},
})}

var LpRealModuleDef = lpRealModuleDefThm{family.Define(registry.DefEntry{
	Name:  "LpRealModuleDef",
	Key:   "prop_99920a0fb5c1f4ff",
	Const: "lp_real_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"real → " +
		"module_ops(real, set(A → complex))",
	Deps: []registry.EntryLike{LpModuleDef},
	Reading: "Real-valued classes form a real submodule " +
		"after scalar restriction, not a complex submodule.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real. " +
			"    lp_real_module(Ω, S, μ, p) = " +
			"    restrict_module(scalar_restriction(complex_of_real, lp_module(Ω, S, μ, p)), " +
			"        {Q:set(A → complex) | " +
			"            Q ∈ lp_module(Ω, S, μ, p).carrier ∧ " +
			"            ∃f:(A → real). real_measurable(Ω, S, f) ∧ Q = real_ae_class(Ω, S, μ, f)})",
	},
})}
