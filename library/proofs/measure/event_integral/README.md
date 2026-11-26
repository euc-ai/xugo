# event_integral — the integral of a real function over an event

The integral of a real function f over an event E is the integral, over the whole carrier, of f cut to 0 off E. Every law here is a law of the integral read at such a cut. The cut of an integrable function to an event is integrable (IntegrableOnEvent), which is what the laws that need integrability stand on. The event integral reads its integrand on Ω ∩ E only, pointwise (EventIntegralEqOn) and up to a null set (EventIntegralAE), and over the whole carrier it is the integral (EventIntegralCarrier). It is linear in the integrand, additive over disjoint events and monotone, pointwise and almost everywhere (EventIntegralMonoAE); a cut inside the integrand intersects the event (EventIntegralRestrict), a constant integrates to its value times the measure of the event, convergence in L¹ on the carrier carries to the integrals over every measurable event (EventIntegralL1Limit), and so does dominated almost-everywhere convergence of measurable integrands (EventIntegralDominatedConvergence); in particular the integral of an integrable function over the events where the absolute value of a measurable one exceeds an unbounded level tends to 0 (EventIntegralTailLimit). A law that is an identity of integrands asks no structure of Ω, S or μ; the others ask what the law of the integral they read asks, and E ∈ S where a cut must be measurable.

## Members

| Entry | Statement |
| --- | --- |
| `EventIntegralDef` | event_integral |
| `IntegrableOnEvent` | `E ∈ S ∧ real_integrable(Ω, S, μ, f) ⇒ real_integrable(Ω, S, μ, λx. COND(x ∈ E, f(x), &0))` under `sigma_algebra_on(Ω, S)` |
| `EventIntegralCarrier` | `event_integral(Ω, S, μ, Ω, f) = measure_integral(Ω, S, μ, f)`, no structure hypothesis |
| `EventIntegralEqOn` | `(∀x. x ∈ Ω ∧ x ∈ E ⇒ f(x) = g(x)) ⇒ event_integral(Ω, S, μ, E, f) = event_integral(Ω, S, μ, E, g)`, no structure hypothesis |
| `EventIntegralAE` | `measure_ae_eq(Ω, S, μ, f, g) ⇒ event_integral(Ω, S, μ, E, f) = event_integral(Ω, S, μ, E, g)` under `measure_on(Ω, S, μ)` |
| `EventIntegralAdd` | `event_integral(Ω, S, μ, E, λx. f(x) + g(x)) = event_integral(Ω, S, μ, E, f) + event_integral(Ω, S, μ, E, g)` for `E ∈ S` and integrable f, g, under `measure_on(Ω, S, μ)` |
| `EventIntegralSub` | `event_integral(Ω, S, μ, E, λx. f(x) - g(x)) = event_integral(Ω, S, μ, E, f) - event_integral(Ω, S, μ, E, g)` for `E ∈ S` and integrable f, g, under `measure_on(Ω, S, μ)` |
| `EventIntegralScale` | `event_integral(Ω, S, μ, E, λx. c * f(x)) = c * event_integral(Ω, S, μ, E, f)` under `measure_on(Ω, S, μ)` |
| `EventIntegralNeg` | `event_integral(Ω, S, μ, E, λx. -f(x)) = -event_integral(Ω, S, μ, E, f)`, no structure hypothesis — card |
| `EventIntegralUnion` | `E ∩ D = ∅ ⇒ event_integral(Ω, S, μ, E ∪ D, f) = event_integral(Ω, S, μ, E, f) + event_integral(Ω, S, μ, D, f)` for `E ∈ S`, `D ∈ S` and integrable f, under `measure_on(Ω, S, μ)` |
| `EventIntegralMono` | `(∀x. x ∈ Ω ∩ E ⇒ f(x) ≤ g(x)) ⇒ event_integral(Ω, S, μ, E, f) ≤ event_integral(Ω, S, μ, E, g)` for integrable f, g, with no structure or event measurability hypothesis |
| `EventIntegralMonoAE` | `measure_ae(Ω, S, μ, λx. f(x) ≤ g(x)) ⇒ event_integral(Ω, S, μ, E, f) ≤ event_integral(Ω, S, μ, E, g)` for integrable f, g and any set E, under `measure_on(Ω, S, μ)` |
| `EventIntegralRestrict` | `event_integral(Ω, S, μ, E, λx. COND(x ∈ D, f(x), &0)) = event_integral(Ω, S, μ, E ∩ D, f)`, no structure hypothesis |
| `EventIntegralConst` | `E ∈ S ⇒ event_integral(Ω, S, μ, E, λx. c) = c * extended_to_real(μ(E))` under `measure_on(Ω, S, μ)` |
| `EventIntegralL1Limit` | `measure_integral(Ω, S, μ, λx. \|f(n, x) - g(x)\|) ⟶ &0 ⇒ event_integral(Ω, S, μ, E, f(n)) ⟶ event_integral(Ω, S, μ, E, g)` for `E ∈ S` and integrable f(n), g, under `measure_on(Ω, S, μ)` |
| `EventIntegralDominatedConvergence` | `event_integral(Ω, S, μ, E, f(n)) ⟶ event_integral(Ω, S, μ, E, g)` for a measurable sequence converging almost everywhere to measurable g, bounded almost everywhere by an integrable h, and `E ∈ S`, under `measure_on(Ω, S, μ)` |
| `EventIntegralTailLimit` | `(λn. event_integral(Ω, S, μ, {x \| c(n) < \|f(x)\|}, g)) ⟶ &0` for measurable f, integrable g and a level c that eventually exceeds every bound, under `measure_on(Ω, S, μ)` |
