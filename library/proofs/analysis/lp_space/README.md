# lp_space — Lebesgue spaces in a common almost everywhere quotient

For every finite real exponent p≥1, the p-integrable functions form a submodule of the measurable function module. Their quotient uses the same null submodule as L0, so all Lp carriers and L-infinity are subsets of one ambient class space. Function-layer inequalities and completeness feed the universal seminorm quotient construction.

## Members

| Entry | Statement |
| --- | --- |
| `LpSeminormDef` | lp_seminorm |
| `LpFunctionsDef` | lp_functions |
| `LpFunctionModuleDef` | lp_function_module |
| `LpModuleDef` | lp_module |
| `LpNormDef` | lp_norm |
| `LpMeasurableSubspaceDef` | lp_measurable_subspace |
| `LpIntegralDef` | lp_integral |
| `EssentialSupDef` | essential_sup |
| `LInfinityFunctionsDef` | linfinity_functions |
| `LInfinityFunctionModuleDef` | linfinity_function_module |
| `LInfinityModuleDef` | linfinity_module |
| `LInfinityNormDef` | linfinity_norm |
| `LpRealModuleDef` | lp_real_module |
| `RealMeasurableRpow` | real_measurable(Ω, S, λx:A. real_rpow(u(x), p)) |
| `LpSeminormNonneg` | &0 ≤ lp_seminorm(Ω, S, μ, p, f) |
| `LpPowerIntegral` | real_integrable(Ω, S, μ, λx:A. real_rpow(\|f(x)\|, p)) ∧ measure_integral(Ω, S, μ, λx:A. real_rpow(\|f(x)\|, p)) = real_rpow(lp_seminorm(Ω, S, μ, p, f), p) |
| `LpSeminormZeroIffAE` | lp_seminorm(Ω, S, μ, p, f) = &0 ⇔ measure_ae(Ω, S, μ, λx:A. f(x) = &0) |
| `LpHolder` | complex_integrable(Ω, S, μ, λx:A. f(x) * g(x)) ∧ measure_integral(Ω, S, μ, λx:A. \|f(x) * g(x)\|) ≤ lp_seminorm(Ω, S, μ, p, f) * lp_seminorm(Ω, S, μ, q, g) |
| `LpSeminorm` | submodule(complex_ring, measurable_function_module(Ω, S), lp_functions(Ω, S, μ, p)) ∧ complex_seminorm(lp_function_module(Ω, S, μ, p), lp_seminorm(Ω, S, μ, p)) ∧ seminorm_kernel(lp_function_module(Ω, S, μ, p), lp_seminorm(Ω, S, μ, p)) = null_functions(Ω, S, μ) — card |
| `FastCauchyLimit` | ∃g:(A → complex). ∃σ:(num → num). g ∈ lp_functions(Ω, S, μ, p) ∧ complex_measurable(Ω, G, g) ∧ (∀n:num. σ(n) < σ(n + 1)) ∧ measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. \|f(σ(n), x) - g(x)\|, &0)) ∧ real_converges_to(λn:num. lp_seminorm(Ω, S, μ, p, λx:A. f(n, x) - g(x)), &0) — card |
| `LpBanach` | complex_banach_space(lp_module(Ω, S, μ, p), lp_norm(Ω, S, μ, p)) ∧ lp_module(Ω, S, μ, p).carrier ⊆ ae_module(Ω, S, μ).carrier — card |
| `LpNormClass` | ae_class(Ω, S, μ, f) ∈ lp_module(Ω, S, μ, p).carrier ∧ lp_norm(Ω, S, μ, p, ae_class(Ω, S, μ, f)) = lp_seminorm(Ω, S, μ, p, f) — card |
| `LpMeasurableClosed` | submodule(complex_ring, lp_module(Ω, S, μ, p), lp_measurable_subspace(Ω, S, μ, G, p)) ∧ closed_in(norm_topology(lp_module(Ω, S, μ, p), lp_norm(Ω, S, μ, p)), lp_measurable_subspace(Ω, S, μ, G, p)) — card |
| `LpMeasurableRepresentative` | Q ∈ lp_measurable_subspace(Ω, S, μ, G, p) ⇔ ∃f:(A → complex). f ∈ lp_functions(Ω, S, μ, p) ∧ complex_measurable(Ω, G, f) ∧ Q = ae_class(Ω, S, μ, f) — card |
| `IntegralOnClasses` | module_homomorphism(complex_ring, lp_module(Ω, S, μ, &1), regular_module(complex_ring), lp_integral(Ω, S, μ)) ∧ (∀f:(A → complex). f ∈ lp_functions(Ω, S, μ, &1) ⇒ lp_integral(Ω, S, μ, ae_class(Ω, S, μ, f)) = complex_measure_integral(Ω, S, μ, f)) ∧ (∀Q:set(A → complex). Q ∈ lp_module(Ω, S, μ, &1).carrier ⇒ \|lp_integral(Ω, S, μ, Q)\| ≤ lp_norm(Ω, S, μ, &1, Q)) — card |
| `SimpleDenseInLp` | ∃s:(A → complex). s ∈ lp_functions(Ω, S, μ, p) ∧ finite(image(s, Ω)) ∧ lp_seminorm(Ω, S, μ, p, λx:A. f(x) - s(x)) < ε — card |
| `LpNested` | lp_module(Ω, S, μ, q).carrier ⊆ lp_module(Ω, S, μ, p).carrier ∧ (∀Q:set(A → complex). Q ∈ lp_module(Ω, S, μ, q).carrier ⇒ lp_norm(Ω, S, μ, p, Q) ≤ real_rpow(extended_to_real(μ(Ω)), real_inv(p) - real_inv(q)) * lp_norm(Ω, S, μ, q, Q)) — card |
| `LInfinitySeminorm` | complex_seminorm(linfinity_function_module(Ω, S, μ), λf:(A → complex). extended_to_real(essential_sup(Ω, S, μ, f))) ∧ seminorm_kernel(linfinity_function_module(Ω, S, μ), λf:(A → complex). extended_to_real(essential_sup(Ω, S, μ, f))) = null_functions(Ω, S, μ) ∧ (∀f:(num → A → complex). metric_cauchy(linfinity_function_module(Ω, S, μ).carrier, norm_distance(linfinity_function_module(Ω, S, μ), λg:(A → complex). extended_to_real(essential_sup(Ω, S, μ, g))), f) ⇒ ∃g:(A → complex). g ∈ linfinity_functions(Ω, S, μ) ∧ real_converges_to(λn:num. extended_to_real(essential_sup(Ω, S, μ, λx:A. f(n, x) - g(x))), &0)) — card |
| `LInfinityBanach` | complex_banach_space(linfinity_module(Ω, S, μ), linfinity_norm(Ω, S, μ)) ∧ linfinity_module(Ω, S, μ).carrier ⊆ ae_module(Ω, S, μ).carrier — card |
| `LInfinityToLp` | linfinity_module(Ω, S, μ).carrier ⊆ lp_module(Ω, S, μ, p).carrier ∧ (∀Q:set(A → complex). Q ∈ linfinity_module(Ω, S, μ).carrier ⇒ lp_norm(Ω, S, μ, p, Q) ≤ real_rpow(extended_to_real(μ(Ω)), real_inv(p)) * linfinity_norm(Ω, S, μ, Q)) — card |
| `LpRealSubmodule` | module_on(real_ring, lp_real_module(Ω, S, μ, p)) — card |
