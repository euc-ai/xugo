# complex_measure_integral — complex integration over arbitrary measure spaces

A complex function is measurable when its real and imaginary parts are measurable. Integration reads these two real integrals, with absolute integrability giving linearity and estimates independent of representatives.

## Members

| Entry | Statement |
| --- | --- |
| `ComplexMeasurableDef` | complex_measurable |
| `ComplexIntegrableDef` | complex_integrable |
| `ComplexIntegralDef` | complex_measure_integral |
| `ComplexMeasurableAdd` | complex_measurable(Ω, S, λx:A. f(x) + g(x)) |
| `ComplexMeasurableMul` | complex_measurable(Ω, S, λx:A. f(x) * g(x)) |
| `ComplexMeasurableScale` | complex_measurable(Ω, S, λx:A. c * f(x)) |
| `ComplexMeasurableConj` | complex_measurable(Ω, S, λx:A. conj(f(x))) |
| `ComplexMeasurableAbs` | real_measurable(Ω, S, λx:A. \|f(x)\|) |
| `ComplexIntegralLinear` | complex_integrable(Ω, S, μ, λx:A. c * f(x) + g(x)) ∧ complex_measure_integral(Ω, S, μ, λx:A. c * f(x) + g(x)) = c * complex_measure_integral(Ω, S, μ, f) + complex_measure_integral(Ω, S, μ, g) — card |
| `ComplexIntegralConjugate` | complex_integrable(Ω, S, μ, λx:A. complex_conj(f(x))) ∧ complex_measure_integral(Ω, S, μ, λx:A. complex_conj(f(x))) = complex_conj(complex_measure_integral(Ω, S, μ, f)) — card |
| `ComplexIntegralBound` | \|complex_measure_integral(Ω, S, μ, f)\| ≤ measure_integral(Ω, S, μ, λx:A. \|f(x)\|) — card |
| `ComplexIntegralAE` | (complex_integrable(Ω, S, μ, f) ⇔ complex_integrable(Ω, S, μ, g)) ∧ complex_measure_integral(Ω, S, μ, f) = complex_measure_integral(Ω, S, μ, g) — card |
| `SquareProductIntegrable` | complex_integrable(Ω, S, μ, λx:A. f(x) * complex_conj(g(x))) — card |
| `ComplexRealEmbedding` | complex_integrable(Ω, S, μ, λx:A. complex_of_real(f(x))) ∧ complex_measure_integral(Ω, S, μ, λx:A. complex_of_real(f(x))) = complex_of_real(measure_integral(Ω, S, μ, f)) — card |
| `ComplexDominatedConvergenceAE` | complex_integrable(Ω, S, μ, g) ∧ (∀n:num. complex_integrable(Ω, S, μ, f(n))) ∧ real_converges_to(λn:num. \|complex_measure_integral(Ω, S, μ, f(n)) - complex_measure_integral(Ω, S, μ, g)\|, &0) — card |
