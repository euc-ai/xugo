# density_measure — the measure a density gives against a measure, and integration against it

A function ρ with values in ⟦0, ∞⟧ on a measure space (Ω, S, μ) gives each set E the mass ∫ ρ·1_E dμ, the integral of ρ cut to 0 off E (`DensityMeasureDef`). The formula is a number for every set and every ρ. For a measurable ρ it is a measure on S, and integrating against it is integrating the product with the density: for measurable functions into ⟦0, ∞⟧, with no integrability condition, and for real functions against a nonnegative real density, where integrability on one side is integrability on the other. Nothing is asked of μ beyond being a measure, and the density may be infinite.

## Members

| Entry | Statement |
| --- | --- |
| `DensityMeasureDef` | `density_measure(Ω, S, μ, ρ, E) = nonneg_integral(Ω, S, μ, λx. COND(x ∈ E, ρ(x), &0))` |
| `DensityMeasure` | for a measure μ and a measurable ρ, `measure_on(Ω, S, density_measure(Ω, S, μ, ρ))` |
| `DensityMeasureNonnegIntegral` | for measurable ρ and f, `nonneg_integral(Ω, S, density_measure(Ω, S, μ, ρ), f) = nonneg_integral(Ω, S, μ, λx. ρ(x) * f(x))` |
| `DensityMeasureIntegral` | for a measurable real g, nonnegative on Ω, and a measurable real f: f is integrable against the density measure of g exactly when g·f is integrable against μ, and the two integrals agree |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
