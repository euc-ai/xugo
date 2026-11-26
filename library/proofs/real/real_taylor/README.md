# real_taylor — Cauchy's mean value theorem, L'Hôpital's rule and Taylor's theorem

Cauchy's mean value theorem compares the increments of two functions through their derivatives at one point. L'Hôpital's rule for a 0/0 quotient and Taylor's theorem with the Lagrange remainder both follow from it, or from Rolle's theorem applied to a function built for the purpose.

## The movements

**Cauchy's mean value theorem.** For f and g continuous on ⟦a, b⟧ with
derivatives inside, Rolle's theorem applied to
(f(b) − f(a))·g(x) − (g(b) − g(a))·f(x), which takes one value at both
ends, finds z with (f(b) − f(a))·g′(z) = (g(b) − g(a))·f′(z).

**L'Hôpital's rule.** Where f(c) = g(c) = 0, both continuous at c, and
f′/g′ tends to L at c with g′ never 0 nearby, f/g tends to L. On the
closed interval between c and a nearby x, g(x) ≠ g(c) by Rolle's
theorem, and Cauchy's theorem gives z strictly between with
f(x)/g(x) = f′(z)/g′(z); z is closer to c than x is, so the radius that
serves f′/g′ serves f/g.

**Taylor's theorem.** It is proved once on an interval whose two ends
are the centre c and the point x, in either order (`TaylorLagrange`).
Rolle's theorem is applied to
h(y) = Q(c)·R(y) − R(c)·Q(y), where T(y) is the Taylor sum about y,
R(y) = D(0)(x) − T(y) and $Q(y) = \frac{(x-y)^{n+1}}{(n+1)!}$. As a function of
its centre the Taylor sum telescopes under differentiation
(`TaylorSumDerivative`, an induction carried by `TaylorSumRecursion`), so h′ vanishing at z says D(n+1)(z) is the
coefficient of the Lagrange remainder. `TaylorLagrangeAbove` and
`TaylorLagrangeBelow` are the two readings of that one theorem.

In the table `⟦a, b⟧` abbreviates `{x | a ≤ x ∧ x ≤ b}` and
«taylorSum» is `Σ_{k∈0 .. n} D(k)(c) · real_pow(x − c, k) / &factorial(k)`.

## Members

| entry | statement |
|---|---|
| `CauchyMeanValue` | `a < b ∧ real_continuous_on(⟦a, b⟧, f) ∧ real_continuous_on(⟦a, b⟧, g) ∧ (∀x. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x))) ⇒ ∃z. a < z ∧ z < b ∧ (f(b) − f(a)) · g'(z) = (g(b) − g(a)) · f'(z)` |
| `LHopital` | `&0 < d ∧ f(c) = &0 ∧ g(c) = &0 ∧ real_continuous_at(f, c) ∧ real_continuous_at(g, c) ∧ (∀x. &0 < real_abs(x − c) ∧ real_abs(x − c) < d ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x)) ∧ g'(x) ≠ &0) ∧ (λx. f'(x) / g'(x)) ⟶ L (at c) ⇒ (λx. f(x) / g(x)) ⟶ L (at c)` |
| `PowerFactorialDerivative` | `real_derivative_at(λt. real_pow(x − t, m + 1) / &factorial(m + 1), y, −(real_pow(x − y, m) / &factorial(m)))` |
| `TaylorSumRecursion` | `(λt. Σ_{k∈0 .. 0} D(k)(t) · real_pow(x − t, k) / &factorial(k)) = D(0) ∧ (λt. Σ_{k∈0 .. n + 1} D(k)(t) · real_pow(x − t, k) / &factorial(k)) = (λt. Σ_{k∈0 .. n} D(k)(t) · real_pow(x − t, k) / &factorial(k) + D(n + 1)(t) · (real_pow(x − t, n + 1) / &factorial(n + 1)))` |
| `TaylorSumDerivative` | `(∀k. k ≤ n ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ⇒ real_derivative_at(λt. Σ_{k∈0 .. n} D(k)(t) · real_pow(x − t, k) / &factorial(k), y, D(n + 1)(y) · real_pow(x − y, n) / &factorial(n))` |
| `TaylorLagrange` | `a < b ∧ (c = a ∧ x = b ∨ c = b ∧ x = a) ∧ (∀k. k ≤ n ⇒ real_continuous_on(⟦a, b⟧, D(k))) ∧ (∀k y. k ≤ n ∧ a < y ∧ y < b ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ⇒ ∃z. a < z ∧ z < b ∧ D(0)(x) = «taylorSum» + D(n + 1)(z) · real_pow(x − c, n + 1) / &factorial(n + 1)` |
| `TaylorLagrangeAbove` | `c < x ∧ (∀k. k ≤ n ⇒ real_continuous_on(⟦c, x⟧, D(k))) ∧ (∀k y. k ≤ n ∧ c < y ∧ y < x ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ⇒ ∃z. c < z ∧ z < x ∧ D(0)(x) = «taylorSum» + D(n + 1)(z) · real_pow(x − c, n + 1) / &factorial(n + 1)` |
| `TaylorLagrangeBelow` | `x < c ∧ (∀k. k ≤ n ⇒ real_continuous_on(⟦x, c⟧, D(k))) ∧ (∀k y. k ≤ n ∧ x < y ∧ y < c ⇒ real_derivative_at(D(k), y, D(k + 1)(y))) ⇒ ∃z. x < z ∧ z < c ∧ D(0)(x) = «taylorSum» + D(n + 1)(z) · real_pow(x − c, n + 1) / &factorial(n + 1)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
