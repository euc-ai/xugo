# lebesgue_riemann — the Lebesgue integral of a continuous function as a Riemann integral, and the Gaussian integral on the line

A function continuous on a closed interval and zero off it is Lebesgue integrable, and its Lebesgue integral is its Riemann integral over the interval: its upper level sets are relatively open in the interval, a constant dominates it there, and mean-value tags make a Riemann sum of each fine partition equal to the Lebesgue integral exactly. This is the bridge by which the calculus of real_integral, the fundamental theorem, substitution and integration by parts, computes Lebesgue integrals: on a bounded interval directly, and on the line as the limit of the cutoffs to ⟦−R, R⟧. The Gaussian integral is computed that way in gaussian.go, by the one-variable derivative trick. With I(t) the integral of exp(−x²) over ⟦0, t⟧ and J(t) the integral over ⟦0, 1⟧ of exp(−t²(1 + x²))/(1 + x²), the function I² + J has derivative 0, its value at 0 is arctan(1) = π/4, and J tends to 0.

## Members

| Entry | Statement |
| --- | --- |
| `LebesgueIntegralInterval` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ∧ (∀x. x ∉ ⟦a, b⟧ ⇒ f(x) = &0) ⇒ lebesgue_integrable(f) ∧ lebesgue_integral(f) = real_integral(f, a, b)` |
| `LebesgueNonnegIntegralOnInterval` | for `l ≤ u` and f continuous and nonnegative on ⟦l, u⟧, the cut of f to ⟦l, u⟧ embedded in ⟦0, ∞⟧ is measurable and its nonnegative integral is `extended_of_real(real_integral(f, l, u))` |
| `LebesgueNonnegIntegralByWindows` | For a nonnegative function continuous on each of a sequence of increasing closed intervals covering the line, the nonnegative integral is the supremum of the embedded Riemann integrals over those intervals. |
| `LebesgueNonnegIntegralBySymmetricWindows` | for f nonnegative and continuous on the line and `&0 < w`, the nonnegative integral of f embedded in ⟦0, ∞⟧ is `extended_sup(image(λn. extended_of_real(real_integral(f, m - w * &n, m + w * &n)), 𝕌))` |
| `LebesgueIntegralByWindows` | for f nonnegative and continuous on the line and closed intervals ⟦l(n), u(n)⟧ increasing to the line, `(λn. real_integral(f, l(n), u(n))) ⟶ L` ⇒ f is `real_integrable` for Lebesgue measure with `measure_integral` L |
| `LebesgueIntegralByCenteredWindows` | the same over the windows ⟦−n, n⟧: `(λn. real_integral(f, -&n, &n)) ⟶ L` ⇒ f is `real_integrable` for Lebesgue measure with `measure_integral` L |
| `LebesgueNonnegIntegralAffineChange` | for `&0 < q` and f nonnegative and continuous on the line, the nonnegative integral of `λy. extended_of_real(q * f(p + q * y))` is that of `λx. extended_of_real(f(x))` |
| `GaussianIntegral` | `lebesgue_integrable(λt. exp(-t ^ 2)) ∧ lebesgue_integral(λt. exp(-t ^ 2)) = real_sqrt(π)` |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
