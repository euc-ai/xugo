# l2_space — the Hilbert space of square-integrable function classes

The integral of f times the conjugate of g is a positive semidefinite inner product on square-integrable functions. Its null space is the common almost everywhere zero submodule, and its quotient is the p=2 member of the Lp family, with the existing complex Hilbert convention of linearity in the first variable.

## Members

| Entry | Statement |
| --- | --- |
| `L2FunctionInnerDef` | l2_function_inner |
| `L2InnerDef` | l2_inner |
| `L2SemiInner` | complex_semi_inner(lp_function_module(Ω, S, μ, &2), l2_function_inner(Ω, S, μ)) ∧ (∀f:(A → complex). f ∈ lp_functions(Ω, S, μ, &2) ⇒ hilbert_norm(l2_function_inner(Ω, S, μ), f) = lp_seminorm(Ω, S, μ, &2, f)) — card |
| `L2Hilbert` | complex_hilbert_space(lp_module(Ω, S, μ, &2), l2_inner(Ω, S, μ)) ∧ (∀Q:set(A → complex). Q ∈ lp_module(Ω, S, μ, &2).carrier ⇒ hilbert_norm(l2_inner(Ω, S, μ), Q) = lp_norm(Ω, S, μ, &2, Q)) — card |
| `L2InnerClasses` | l2_inner(Ω, S, μ, ae_class(Ω, S, μ, f), ae_class(Ω, S, μ, g)) = l2_function_inner(Ω, S, μ, f, g) — card |
