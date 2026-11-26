# lebesgue_integral — the Lebesgue integral on the real line

The chapter keeps the Lebesgue integral's definitions on the line and the bridges that read it as the general integral of a measure space at the instance (𝕌, the Lebesgue measurable sets, λ*). Its theorems — measurable functions, simple functions and their integral, monotone convergence, Fatou's lemma, integrable functions and the laws of the integral, dominated convergence — are proved once, for an arbitrary measure space, in `measure/measure_integral` and `measure/integral_convergence`, and read on the line through the bridges.

## Definitions (definitions.go)

A function is measurable when every upper level set {x | c < f(x)} is
measurable. A nonnegative simple function is a measurable function with
finitely many values, all nonnegative, and its integral sums its values
times the measures of their level sets, in ⟦0, ∞⟧, where 0 · ∞ = 0. The
integral of a nonnegative function is the supremum, in ⟦0, ∞⟧, of the
integrals of the simple functions below it; where f is negative somewhere
no simple function lies below it, and the integral is 0, the empty
supremum. A function is integrable when it is measurable and the integral
of |f| is finite, and the integral of a real function is the difference
of the integrals of its positive and negative parts, max(f, 0) and
max(−f, 0).

## The bridges (general_bridge.go, integral_bridge.go)

Each definition is the general one read on the whole line with the
σ-algebra of Lebesgue measurable sets (`lebesgue_measure.LebesgueSigmaAlgebra`)
and the outer measure λ* restricted to it, a measure there
(`lebesgue_measure.LebesgueMeasureOn`). A function is Lebesgue measurable
exactly when it is `real_measurable` for that σ-algebra, both asking the
same of every upper ray (`MeasurableFunctionIffRealMeasurable`, through
`measurable_function.RealMeasurableIffRay`). The simple functions and their
integral are `measure_simple` and `measure_simple_integral` there
(`LebesgueSimpleIff`, `LebesgueSimpleIntegralEq`). On a nonnegative f the
integral is the general `nonneg_integral` of f's embedding in ⟦0, ∞⟧, the
two suprema ranging over the same simple integrals
(`LebesgueNonnegIntegralEq`); the nonnegativity is needed, since where f
is negative somewhere the chapter's integral is 0 while the general one is
that of the positive part. The embedding reads a real at its positive
part, so the integral of max(f, 0) is the general integral of f's
embedding at every f (`LebesguePositivePartEq`). Integrability is
`real_integrable` (`LebesgueIntegrableIff`) and the integral is
`measure_integral` at every function (`LebesgueIntegralEq`).

## Where the results live

A result about the Lebesgue integral is the general member read at the
instance: `X.Read(lebesgue_measure.LebesgueMeasureOn)` where X is stated
over a measure, `X.At(𝕌, {s | lebesgue_measurable(s)}, …)` with
`LebesgueSigmaAlgebra` or `LebesgueMeasureOn` where it asks one as a
hypothesis, and the bridges above turn its general spelling into the
chapter's.

| result on the line | general member |
|---|---|
| measurability of constants, level sets, −f, k·f, f + g, max, min, \|f\|, the two parts, pointwise suprema, infima and limits, scaled indicators and the integer part | `measurable_function.RealMeasurableConst`, `measurable_function.RealMeasurableAtMost`, `measurable_function.RealMeasurableBelow`, `measurable_function.RealMeasurableAtLeast`, `measurable_function.RealMeasurableNeg`, `measurable_function.RealMeasurableScale`, `measurable_function.RealMeasurableAdd`, `measurable_function.RealMeasurableMax`, `measurable_function.RealMeasurableMin`, `measurable_function.RealMeasurableAbs`, `measurable_function.RealMeasurableParts`, `measurable_function.RealMeasurableSup`, `measurable_function.RealMeasurableInf`, `measurable_function.RealMeasurableLimit`, `measurable_function.RealMeasurableIndicator`, `measurable_function.RealMeasurableIntegerPart` |
| simple functions: level sets, sums, nonnegative multiples, pairs of values, the integral on a partition, of an indicator, of a multiple, of a refinement and of a restriction, its monotonicity and additivity | `measure_simple.SimpleLevelSets`, `measure_simple.SimpleAdd`, `measure_simple.SimpleScale`, `measure_simple.SimplePairsFinite`, `measure_simple.SimpleIntegralPartition`, `measure_simple.SimpleIntegralIndicator`, `measure_simple.SimpleIntegralScale`, `measure_simple.SimpleIntegralRefine`, `measure_simple.SimpleIntegralRestrict`, `measure_simple.SimpleIntegralMono`, `measure_simple.SimpleIntegralAdd` |
| approximation by simple functions, through the integer part | `measure_simple.IntegerPartSimple`, `measure_simple.SimpleApproximation` |
| the nonnegative integral: monotone, 0 on the zero function, a simple function's own integral, scaling, additivity | `nonneg_integral.NonnegIntegralMono`, `nonneg_integral.NonnegIntegralZero`, `nonneg_integral.NonnegIntegralSimple`, `nonneg_integral.NonnegIntegralScale`, `nonneg_integral.NonnegIntegralAdd` |
| monotone convergence | `nonneg_integral.MonotoneConvergence`, `nonneg_integral.MonotoneConvergenceSimple` |
| integrable functions: domination, finite parts, sums, multiples, differences | `measure_integral.IntegrableDominated`, `measure_integral.IntegrablePartsFinite`, `measure_integral.IntegrableAdd`, `measure_integral.IntegrableScale`, `measure_integral.IntegrableSub` |
| the integral: of a nonnegative function, nonnegative and, where integrable, its nonnegative integral, of −f, monotone, \|∫f\| ≤ ∫\|f\|, of a difference u − v, additive, homogeneous, of a difference f − g | `measure_integral.IntegralNonneg`, `measure_integral.IntegralNonnegEmbedding`, `measure_integral.IntegralNeg`, `measure_integral.IntegralMono`, `measure_integral.IntegralAbsLe`, `measure_integral.IntegralNonnegDifference`, `measure_integral.IntegralAdd`, `measure_integral.IntegralScale`, `measure_integral.IntegralSub` |
| Fatou's lemma | `integral_convergence.Fatou` |
| dominated convergence: the limit integrable, the lower bound, convergence of the integrals | `integral_convergence.DominatedLimitIntegrable`, `integral_convergence.DominatedLowerLimit`, `integral_convergence.DominatedConvergence` |

## Members

| entry | statement |
|---|---|
| `LebesgueMeasurableFunctionDef` | `lebesgue_measurable_function(f) ⇔ ∀c. lebesgue_measurable({x \| c < f(x)})` |
| `lebesgueSimpleDef` | `lebesgue_simple(f) ⇔ lebesgue_measurable_function(f) ∧ finite(image(f, 𝕌)) ∧ (∀x. &0 ≤ f(x))` |
| `LebesgueSimpleIntegralDef` | `lebesgue_simple_integral(f) = Σ_{y∈image(f, 𝕌)} extended_of_real(y) * lebesgue_outer_measure({x \| f(x) = y})` |
| `LebesgueNonnegIntegralDef` | `lebesgue_nonneg_integral(f) = extended_sup({m \| ∃s. lebesgue_simple(s) ∧ (∀x. s(x) ≤ f(x)) ∧ m = lebesgue_simple_integral(s)})` |
| `LebesgueIntegrableDef` | `lebesgue_integrable(f) ⇔ lebesgue_measurable_function(f) ∧ lebesgue_nonneg_integral(λx. real_abs(f(x))) ≠ extended_infinity` |
| `LebesgueIntegralDef` | `lebesgue_integral(f) = extended_to_real(lebesgue_nonneg_integral(λx. max(f(x), &0))) − extended_to_real(lebesgue_nonneg_integral(λx. max(−f(x), &0)))` |
| `MeasurableFunctionIffRealMeasurable` | `lebesgue_measurable_function(f) ⇔ real_measurable(𝕌, {s \| lebesgue_measurable(s)}, f)` |
| `ContinuousLebesgueMeasurable` | `real_continuous_on(𝕌, f) ⇒ real_measurable(𝕌, {s \| lebesgue_measurable(s)}, f)` |
| `LebesgueSimpleIff` | `lebesgue_simple(s) ⇔ measure_simple(𝕌, {u \| lebesgue_measurable(u)}, s)` |
| `LebesgueSimpleIntegralEq` | `lebesgue_simple_integral(s) = measure_simple_integral(𝕌, lebesgue_outer_measure, s)` |
| `LebesgueNonnegIntegralEq` | `(∀x. &0 ≤ f(x)) ⇒ lebesgue_nonneg_integral(f) = nonneg_integral(𝕌, {s \| lebesgue_measurable(s)}, lebesgue_outer_measure, λx. extended_of_real(f(x)))` |
| `LebesguePositivePartEq` | `lebesgue_nonneg_integral(λx. max(f(x), &0)) = nonneg_integral(𝕌, {s \| lebesgue_measurable(s)}, lebesgue_outer_measure, λx. extended_of_real(f(x)))` |
| `LebesgueIntegrableIff` | `lebesgue_integrable(f) ⇔ real_integrable(𝕌, {s \| lebesgue_measurable(s)}, lebesgue_outer_measure, f)` |
| `LebesgueIntegralEq` | `lebesgue_integral(f) = measure_integral(𝕌, {s \| lebesgue_measurable(s)}, lebesgue_outer_measure, f)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
