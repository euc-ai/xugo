# stopping_time — discrete stopping times with an infinite value

A stopping time takes values in option(num), with none representing infinity. Truncation always yields a natural time; evaluation at infinity is assigned zero. The stopped sigma algebra contains ambient events whose restrictions to each finite stopping event are observable by that time.

Constants, minima, maxima and finite truncations require only that each F(n) is a sigma algebra on Ω. The increasing-filtration condition enters when comparing information at different times.

## Members

| Entry | Statement |
| --- | --- |
| `TimeLeDef` | stopping_time_le |
| `TimeMinNatDef` | stopping_time_min_nat |
| `TimeToExtendedDef` | stopping_time_extended |
| `StoppingTimeDef` | stopping_time_on |
| `StoppedSigmaDef` | stopped_sigma |
| `StoppedProcessDef` | stopped_process |
| `StoppedValueDef` | stopped_value |
| `FirstEntranceDef` | first_entrance |
| `TimeLeClauses` | `stopping_time_le(some(m), some(n)) ⇔ m ≤ n`; every time lies below none, and none below no finite time |
| `TimeLeTrans` | `stopping_time_le(r, s) ∧ stopping_time_le(s, t) ⇒ stopping_time_le(r, t)` |
| `TimeLeSome` | `stopping_time_le(t, some(n)) ⇔ ∃k. t = some(k) ∧ k ≤ n` |
| `TimeMinNatClauses` | `stopping_time_le(t, some(n)) ⇒ some(stopping_time_min_nat(t, n)) = t`, and otherwise `stopping_time_min_nat(t, n) = n` |
| `StoppingConstants` | stopping_time_on(Ω, F, λx:A. some(n)) ∧ stopping_time_on(Ω, F, λx:A. none) |
| `StoppingMinMax` | stopping_time_on(Ω, F, λx:A. COND(stopping_time_le(T(x), U(x)), T(x), U(x))) ∧ stopping_time_on(Ω, F, λx:A. COND(stopping_time_le(T(x), U(x)), U(x), T(x))) |
| `StoppingTruncation` | stopping_time_on(Ω, F, λx:A. some(stopping_time_min_nat(T(x), n))) ∧ (∀x:A. stopping_time_min_nat(T(x), n) ≤ n) |
| `FirstEntranceStopping` | stopping_time_on(Ω, F, first_entrance(B, M)) — card |
| `StoppedSigmaAlgebra` | sigma_algebra_on(Ω, stopped_sigma(Ω, S, F, T)) ∧ stopped_sigma(Ω, S, F, T) ⊆ S for a stopping time T, assuming only sigma_algebra_on(Ω, S) and sigma_algebra_on(Ω, F(n)) for every n |
| `StoppedSigmaMono` | stopped_sigma(Ω, S, F, T) ⊆ stopped_sigma(Ω, S, F, U) — card |
| `StoppedValueSome` | `T(x) = some(k) ⇒ stopped_value(M, T, x) = M(k, x)` |
| `StoppedProcessAtBound` | `stopping_time_le(T(x), some(N)) ⇒ stopped_process(M, T, N, x) = stopped_value(M, T, x)` |
| `StoppedValueAtTruncation` | `stopped_value(M, λx. some(stopping_time_min_nat(T(x), n))) = stopped_process(M, T, n)` |
| `StoppedValueMeasurable` | real_measurable(Ω, stopped_sigma(Ω, S, F, T), stopped_value(M, T)) ∧ adapted_process(Ω, F, stopped_process(M, T)) |
| `StoppedAmbientMeasurable` | real_measurable(Ω, S, stopped_value(M, T)) ∧ (∀n:num. real_measurable(Ω, S, stopped_process(M, T, n))) for an adapted process in a filtration |
| `StoppingTimeLevelSets` | `{x ∈ Ω \| T(x) = some(n)} ∈ F(n)` for every n and `{x ∈ Ω \| T(x) = none} ∈ S` for a stopping time in a filtration |
| `StoppingTimeExtendedMeasurable` | `extended_measurable(Ω, S, λx. stopping_time_extended(T(x)))` when S is a sigma algebra and T is a stopping time for the constant family S |
| `StoppedIncrement` | stopped_process(M, T, n + 1, x) - stopped_process(M, T, n, x) = COND(stopping_time_le(T(x), some(n)), &0, M(n + 1, x) - M(n, x)) |
