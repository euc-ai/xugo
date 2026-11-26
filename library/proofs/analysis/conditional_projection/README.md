# conditional_projection — conditional expectation from Hilbert projection

On a finite measure space, orthogonal projection onto the closed subspace of classes with a measurable representative constructs conditional expectation for square-integrable functions, and the residual X − Y is orthogonal to every square-integrable G-measurable function. Bounded truncation, L1 contraction and function-layer completeness extend existence to every integrable function; the relation also descends to a linear operator on classes.

## Members

| Entry | Statement |
| --- | --- |
| `CondExpDef` | cond_exp |
| `complexCondExpDef` | complex_cond_exp |
| `conditionalClassDef` | conditional_class |
| `CondExpExistsL2` | ∃Y:(A → real). is_cond_exp(Ω, S, μ, G, X, Y) ∧ real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x)) — card |
| `CondExpIffProjection` | is_cond_exp(Ω, S, μ, G, X, Y) ⇔ real_ae_class(Ω, S, μ, Y) = hilbert_projection(lp_module(Ω, S, μ, &2), l2_inner(Ω, S, μ), lp_measurable_subspace(Ω, S, μ, G, &2), real_ae_class(Ω, S, μ, X)) — card |
| `CondExpL2Bound` | real_integrable(Ω, S, μ, λx:A. Y(x) * Y(x)) ∧ measure_integral(Ω, S, μ, λx:A. Y(x) * Y(x)) ≤ measure_integral(Ω, S, μ, λx:A. X(x) * X(x)) — card |
| `CondExpResidualOrthogonal` | real_integrable(Ω, S, μ, λx:A. (X(x) - Y(x)) * Z(x)) ∧ measure_integral(Ω, S, μ, λx:A. (X(x) - Y(x)) * Z(x)) = &0 — card |
| `CondExpExists` | ∃Y:(A → real). is_cond_exp(Ω, S, μ, G, X, Y) — card |
| `CondExpSpecification` | is_cond_exp(Ω, S, μ, G, X, cond_exp(Ω, S, μ, G, X)) — card |
| `ConditionalClassOperator` | bounded_operator(lp_module(Ω, S, μ, &1), lp_norm(Ω, S, μ, &1), lp_module(Ω, S, μ, &1), lp_norm(Ω, S, μ, &1), conditional_class(Ω, S, μ, G)) ∧ image(conditional_class(Ω, S, μ, G), lp_module(Ω, S, μ, &1).carrier) ⊆ lp_measurable_subspace(Ω, S, μ, G, &1) — card |
| `ConditionalClassRealContraction` | conditional_class(Ω, S, μ, G, Q) ∈ lp_real_module(Ω, S, μ, &1).carrier ∧ lp_norm(Ω, S, μ, &1, conditional_class(Ω, S, μ, G, Q)) ≤ lp_norm(Ω, S, μ, &1, Q) — card |
| `ConditionalClassProjection` | conditional_class(Ω, S, μ, G, Q) = hilbert_projection(lp_module(Ω, S, μ, &2), l2_inner(Ω, S, μ), lp_measurable_subspace(Ω, S, μ, G, &2), Q) — card |
