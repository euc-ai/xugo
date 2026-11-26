package almost_everywhere_function

import (
	"github.com/euc-ai/xugo/library/registry"
)

var MeasurableFunctionsDef = measurableFunctionsDefThm{family.Define(registry.DefEntry{
	Name:  "MeasurableFunctionsDef",
	Key:   "prop_4bec6ec4e4f93778",
	Const: "measurable_functions",
	Type:  "set(A) → set(set(A)) → set(A → complex)",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). " +
			"    measurable_functions(Ω, S) = " +
			"    {f:(A → complex) | complex_measurable(Ω, S, f) ∧ (∀x:A. x ∉ Ω ⇒ f(x) = complex_of_real(&0))}",
	},
})}

var MeasurableFunctionModuleDef = measurableFunctionModuleDefThm{family.Define(registry.DefEntry{
	Name:  "MeasurableFunctionModuleDef",
	Key:   "prop_15551a8377c19f80",
	Const: "measurable_function_module",
	Type:  "set(A) → set(set(A)) → module_ops(complex, A → complex)",
	Deps:  []registry.EntryLike{MeasurableFunctionsDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). " +
			"    measurable_function_module(Ω, S) = " +
			"    restrict_module(function_module(regular_module(complex_ring), Ω), measurable_functions(Ω, S))",
	},
})}

var NullFunctionsDef = nullFunctionsDefThm{family.Define(registry.DefEntry{
	Name:  "NullFunctionsDef",
	Key:   "prop_8d3a126a11ce05a2",
	Const: "null_functions",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → set(A → complex)",
	Deps:  []registry.EntryLike{MeasurableFunctionsDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    null_functions(Ω, S, μ) = " +
			"    {f:(A → complex) | " +
			"        f ∈ measurable_functions(Ω, S) ∧ measure_ae(Ω, S, μ, λx:A. f(x) = complex_of_real(&0))}",
	},
})}

var AEModuleDef = aEModuleDefThm{family.Define(registry.DefEntry{
	Name:  "AEModuleDef",
	Key:   "prop_c7a622ca97cea636",
	Const: "ae_module",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"module_ops(complex, set(A → complex))",
	Deps: []registry.EntryLike{MeasurableFunctionModuleDef, NullFunctionsDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). " +
			"    ae_module(Ω, S, μ) = " +
			"    quotient_module(measurable_function_module(Ω, S), null_functions(Ω, S, μ))",
	},
})}

var AEClassDef = aEClassDefThm{family.Define(registry.DefEntry{
	Name:  "AEClassDef",
	Key:   "prop_638d26adfa5cdb39",
	Const: "ae_class",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"(A → complex) → " +
		"set(A → complex)",
	Deps: []registry.EntryLike{
		MeasurableFunctionModuleDef,
		NullFunctionsDef,
	},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → complex). " +
			"    ae_class(Ω, S, μ, f) = " +
			"    left_coset(measurable_function_module(Ω, S).add, " +
			"        normalize_on(Ω, complex_of_real(&0), f), " +
			"        null_functions(Ω, S, μ))",
	},
})}

var RealAEClassDef = realAEClassDefThm{family.Define(registry.DefEntry{
	Name:  "RealAEClassDef",
	Key:   "prop_5e32b0570ef29d77",
	Const: "real_ae_class",
	Type:  "set(A) → set(set(A)) → (set(A) → extended_nonneg_real) → (A → real) → set(A → complex)",
	Deps:  []registry.EntryLike{AEClassDef},
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f:(A → real). " +
			"    real_ae_class(Ω, S, μ, f) = ae_class(Ω, S, μ, λx:A. complex_of_real(f(x)))",
	},
})}

var AEInclusionDef = aEInclusionDefThm{family.Define(registry.DefEntry{
	Name:  "AEInclusionDef",
	Key:   "prop_909b62cd86835b56",
	Const: "ae_inclusion",
	Type: "set(A) → " +
		"set(set(A)) → " +
		"(set(A) → extended_nonneg_real) → " +
		"set(A → complex) → " +
		"set(A → complex)",
	Deps: []registry.EntryLike{MeasurableFunctionModuleDef, NullFunctionsDef},
	Reading: "For a sub-sigma algebra G this sends its function coset " +
		"to the ambient S-coset. The G and S cosets are not identified as sets.",
	Equations: []string{
		"∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Q:set(A → complex). " +
			"    ae_inclusion(Ω, S, μ, Q) = " +
			"    set_mul(measurable_function_module(Ω, S).add, Q, null_functions(Ω, S, μ))",
	},
})}
