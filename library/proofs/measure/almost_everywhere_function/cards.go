package almost_everywhere_function

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/function_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/registry"
)

var MeasurableFunctionModule = measurableFunctionModuleThm{family.Add(registry.ProofEntry{
	Name: "MeasurableFunctionModule",
	Deps: []registry.EntryLike{
		complex_measure_integral.ComplexMeasurableAdd,
		complex_measure_integral.ComplexMeasurableScale,
		function_module.FunModuleOn,
		submodule.SubmoduleModuleOn,
	},
	Key: "prop_77a293314edf05fa",
	Build: family.Card(Statement{Binders: "∀Ω:set(A). ∀S:set(set(A)).",
		Hypotheses: []string{"sigma_algebra_on(Ω, S)"},
		Conclusion: "submodule(complex_ring, " +
			"    function_module(regular_module(complex_ring), Ω), " +
			"    measurable_functions(Ω, S)) ∧ " +
			"module_on(complex_ring, measurable_function_module(Ω, S))"},
		"Measurability is closed under addition and complex scaling; "+
			"pointwise operations preserve vanishing outside the carrier."),
})}

var NullFunctionSubmodule = nullFunctionSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "NullFunctionSubmodule",
	Deps: []registry.EntryLike{
		MeasurableFunctionModule,
		measure_space.AEOperation,
		submodule.QuotientModuleOn,
	},
	Key: "prop_d49c835206d57419",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "submodule(complex_ring, " +
			"    measurable_function_module(Ω, S), " +
			"    null_functions(Ω, S, μ)) ∧ " +
			"module_on(complex_ring, ae_module(Ω, S, μ))",
	},
		"The union of two null exceptional sets is null and each linear operation "+
			"preserves zero away from it. Apply the existing quotient-module theorem."),
})}

var ClassEqIffAE = classEqIffAEThm{family.Add(registry.ProofEntry{
	Name: "ClassEqIffAE",
	Reading: "The measurability hypotheses are load-bearing: " +
		"otherwise ae_class(f) is a coset outside the carrier of ae_module.",
	Deps: []registry.EntryLike{NullFunctionSubmodule, submodule.SubmoduleCosetEq},
	Key:  "prop_d83cbb4771f7e291",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀f g:(A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"complex_measurable(Ω, S, f)",
			"complex_measurable(Ω, S, g)",
		},
		Conclusion: "ae_class(Ω, S, μ, f) ∈ ae_module(Ω, S, μ).carrier ∧ " +
			"(ae_class(Ω, S, μ, f) = ae_class(Ω, S, μ, g) ⇔ measure_ae_eq(Ω, S, μ, f, g))",
	},
		"Normalize off the carrier and apply SubmoduleCosetEq to the null "+
			"submodule. The difference is null exactly when the two functions agree a.e."),
})}

var AEClassRepresentative = aEClassRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "AEClassRepresentative",
	Deps: []registry.EntryLike{NullFunctionSubmodule},
	Key:  "prop_38a3fb6d9f3ab6c9",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀Q:set(A → complex).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "Q ∈ ae_module(Ω, S, μ).carrier"},
		Conclusion: "∃f:(A → complex). f ∈ measurable_functions(Ω, S) ∧ Q = ae_class(Ω, S, μ, f)",
	},
		"The quotient carrier consists of cosets with representatives in the measurable function module."),
})}

var SubSigmaClassEmbedding = subSigmaClassEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "SubSigmaClassEmbedding",
	Reading: "Injectivity reads only G-measurability of the disagreement " +
		"set and monotonicity of μ on S; no completeness is needed.",
	Deps: []registry.EntryLike{
		NullFunctionSubmodule,
		ClassEqIffAE,
		module_homomorphism.QuotientInclusionHom,
	},
	Key: "prop_81f453a9b93eaa4",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀G:set(set(A)).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "sigma_algebra_on(Ω, G)", "G ⊆ S"},
		Conclusion: "module_homomorphism(complex_ring, " +
			"    ae_module(Ω, G, μ), " +
			"    ae_module(Ω, S, μ), " +
			"    ae_inclusion(Ω, S, μ)) ∧ " +
			"injective_on(ae_module(Ω, G, μ).carrier, ae_inclusion(Ω, S, μ))",
	},
		"Apply QuotientInclusionHom. For injectivity, the disagreement set "+
			"of two G-measurable representatives is G-measurable; if covered by "+
			"an S-null set its measure is zero, so it is already a G-null set."),
})}
