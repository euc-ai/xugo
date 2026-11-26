# optional_stopping — optional sampling and optional stopping

Bounded optional sampling compares two stopping times by the conditional-expectation relation at the earlier stopped sigma algebra. Sampled against the zero time it keeps the expectation of a martingale stopped and observed at a finite time, and so of one stopped at a time almost everywhere bounded. Almost everywhere dominated convergence gives unbounded stopping under an integrable bound, including finite expected time and bounded increments.

The bounded times and the limits are two files, because the proofs change in kind between them. The bounded file proves integrability of the truncated processes, cancels each increment over the earlier stopped event and telescopes to the terminal values; the truncated and almost-everywhere-bounded results follow from it, the process stopped at the bound showing the stopped value almost everywhere. In the limit file the dominated theorem reads the integrals of the truncations off the truncated one and passes to the limit, and the integrable-time theorem reaches the dominated one through the envelope |M(0)| + |C|·τ, τ the finite part of T.

## Members

| Entry | Statement |
| --- | --- |
| `OptionalSamplingBounded` | is_cond_exp(Ω, S, μ, stopped_sigma(Ω, S, F, U), stopped_value(M, T), stopped_value(M, U)) for stopping times U ≤ T ≤ N on Ω |
| `OptionalStoppingTruncated` | real_integrable(Ω, S, μ, stopped_process(M, T, n)) ∧ expectation(Ω, S, μ, stopped_process(M, T, n)) = expectation(Ω, S, μ, M(0)) |
| `OptionalStoppingBoundedAE` | real_integrable(Ω, S, μ, stopped_value(M, T)) ∧ expectation(Ω, S, μ, stopped_value(M, T)) = expectation(Ω, S, μ, M(0)) for T ≤ N almost everywhere |
| `OptionalStoppingDominated` | the same conclusion for T finite almost everywhere and every \|stopped_process(M, T, n)\| ≤ Y almost everywhere, Y integrable |
| `OptionalStoppingIntegrableTime` | the same conclusion for T of finite expected time and every \|M(n + 1) − M(n)\| ≤ C almost everywhere |
