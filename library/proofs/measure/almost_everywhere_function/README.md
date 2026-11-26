# almost_everywhere_function — measurable functions modulo almost everywhere equality

Complex measurable functions that vanish off the carrier form a function module. Quotienting by its almost everywhere zero submodule gives one ambient space of function classes. Smaller sigma algebras enter through the quotient inclusion map, so having a measurable representative is a property of the class.

## Members

| Entry | Statement |
| --- | --- |
| `MeasurableFunctionsDef` | measurable_functions |
| `MeasurableFunctionModuleDef` | measurable_function_module |
| `NullFunctionsDef` | null_functions |
| `AEModuleDef` | ae_module |
| `AEClassDef` | ae_class |
| `RealAEClassDef` | real_ae_class |
| `AEInclusionDef` | ae_inclusion |
| `MeasurableFunctionModule` | submodule(complex_ring, function_module(regular_module(complex_ring), Ω), measurable_functions(Ω, S)) ∧ module_on(complex_ring, measurable_function_module(Ω, S)) — card |
| `NullFunctionSubmodule` | submodule(complex_ring, measurable_function_module(Ω, S), null_functions(Ω, S, μ)) ∧ module_on(complex_ring, ae_module(Ω, S, μ)) — card |
| `ClassEqIffAE` | ae_class(Ω, S, μ, f) ∈ ae_module(Ω, S, μ).carrier ∧ (ae_class(Ω, S, μ, f) = ae_class(Ω, S, μ, g) ⇔ measure_ae_eq(Ω, S, μ, f, g)) — card |
| `AEClassRepresentative` | ∃f:(A → complex). f ∈ measurable_functions(Ω, S) ∧ Q = ae_class(Ω, S, μ, f) — card |
| `SubSigmaClassEmbedding` | module_homomorphism(complex_ring, ae_module(Ω, G, μ), ae_module(Ω, S, μ), ae_inclusion(Ω, S, μ)) ∧ inj_on(ae_inclusion(Ω, S, μ), ae_module(Ω, G, μ).carrier) — card |
