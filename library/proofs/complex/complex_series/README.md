# complex_series — series of complex numbers

A complex series sums to `s` when its real parts sum to `re(s)` and its
imaginary parts to `im(s)`: `complex_sums(a, s) ⇔ real_sums(λn. re(a(n)),
re(s)) ∧ real_sums(λn. im(a(n)), im(s))`. That is convergence in the
plane, since a point's distance from `s` is at most the sum of the
distances of its two parts and at least each of them. Taking it as the
definition is what makes the chapter short: every law of the first section but one is a law of
`real/real_series`, read once on the real parts and once on the
imaginary parts. Each proof unfolds the definition, applies the real law
to each part as a step of its own, and reads the two results back as the
parts of the complex statement (`complex_field.Parts`). The one law that
mixes the parts is the bound on a sum (`ComparisonBound`): multiplied by
the conjugate of its sum s, the series sums to |s|², a real number; each
of its real parts is at most |s|·b(n), so the real comparison bound gives
|s|² ≤ |s|·t, and |s| ≤ t follows. So a series dominated termwise in
modulus by a summable real series has a sum, within the real sum in
modulus (`Comparison`). A series sums to s exactly when its
partial sums tend to s (`SumsIffPartialSums`): re and im carry the
partial sums to the parts' partial sums, and these converge as the parts
do (`complex_topology.ConvergesIffParts`).

## The definition and the laws

| member | statement |
|---|---|
| `ComplexSumsDef` | `complex_sums(a, s) ⇔ real_sums(λn. re(a(n)), re(s)) ∧ real_sums(λn. im(a(n)), im(s))` |
| `SumsUnique` | `complex_sums(a, s) ∧ complex_sums(a, t) ⇒ s = t` |
| `SumsAdd` | `complex_sums(a, s) ∧ complex_sums(b, t) ⇒ complex_sums(λn. a(n) + b(n), s + t)` |
| `SumsScale` | `complex_sums(a, s) ⇒ complex_sums(λn. c * a(n), c * s)` |
| `SumsPair` | `complex_sums(a, s) ⇒ complex_sums(λn. a(2 * n) + a(2 * n + 1), s)` |
| `SumsOfReal` | `complex_sums(λn. complex_of_real(a(n)), complex_of_real(s)) ⇔ real_sums(a, s)` |
| `AbsoluteConvergence` | `real_sums(λn. complex_abs(a(n)), t) ⇒ ∃s. complex_sums(a, s)` |
| `SumsSub` | `complex_sums(a, s) ∧ complex_sums(b, t) ⇒ complex_sums(λn. a(n) − b(n), s − t)` |
| `SumsShift` | `complex_sums(a, s) ⇔ complex_sums(λn. a(n + 1), s − a(0))` |
| `ComparisonBound` | `(∀n. \|a(n)\| ≤ b(n)) ∧ complex_sums(a, s) ∧ real_sums(b, t) ⇒ \|s\| ≤ t` |
| `Comparison` | `(∀n. \|a(n)\| ≤ b(n)) ∧ real_sums(b, t) ⇒ ∃s. complex_sums(a, s) ∧ \|s\| ≤ t` |
| `SumsIffPartialSums` | `complex_sums(a, s) ⇔ (λn. Σ_{k∈0 .. n} a(k)) ⟶ s` |

Multiplying by a complex constant is the one law that mixes the parts:
the real part of `c · a(n)` is `re(c)·re(a(n)) − im(c)·im(a(n))`, so it
needs the real series' differences as well as their sums and multiples
(`real_series.SumsSub`). On real terms the imaginary parts are zeros,
which sum to 0 (`real_series.SumsZero`), so a real series and its
complex image converge together. A series whose sizes have a sum has
one: each part of a term is at most the term's size
(`complex_abs.ReLessEqAbs`, `ImLessEqAbs`), so each part converges by
comparison, and the number with those two sums as its parts is the
series' sum.

## Finite sums, an offset, and regrouping a double series (finite_sums.go)

A finite complex sum's linearity, exchange and interval laws are cited
where they stand — `module.ModuleSumAdd`, `ModuleSumNeg` and
`ModuleSumSmul` at ℂ's regular module, `monoidal.Swap`, `Fibres`,
`PeelRight`, `Shift` — and the three readings here are the ones cited
often enough to be stated in the Σ spelling: the parts of a sum, the
modulus of a sum, and summation by parts. `SumsOffset` drops the first
m + 1 terms of a series. `DoubleSeriesRegroup` sums an absolutely
convergent double series along the fibres of a map with finite fibres;
the Dirichlet product reads it along (m, n) ↦ m·n.

| member | statement |
|---|---|
| `SumParts` | `∀s:set(A). ∀f:(A → complex). finite(s) ⇒ re(Σ_{i∈s} f(i)) = Σ_{i∈s} re(f(i)) ∧ im(Σ_{i∈s} f(i)) = Σ_{i∈s} im(f(i))` |
| `AbsSumLessEq` | `∀s:set(A). ∀f:(A → complex). finite(s) ⇒ \|Σ_{i∈s} f(i)\| ≤ Σ_{i∈s} \|f(i)\|` |
| `SummationByParts` | `∀m n:num. ∀f g:(num → complex). m ≤ n ⇒ Σ_{k∈m .. n} f(k) * (g(k + 1) - g(k)) = f(n + 1) * g(n + 1) - f(m) * g(m) - Σ_{k∈m .. n} g(k + 1) * (f(k + 1) - f(k))` |
| `SumsOffset` | `complex_sums(a, s) ⇔ complex_sums(λn. a(n + m + 1), s − Σ_{k∈0 .. m} a(k))` |
| `DoubleSeriesRegroup` | `∀u:(num → num → complex). ∀φ:(num → num → num). ∀R:(num → real). ∀T:real. (∀m:num. real_sums(λn:num. \|u(m, n)\|, R(m))) ∧ real_sums(R, T) ∧ (∀k:num. finite({p:prod(num, num) \| φ(fst(p), snd(p)) = k})) ⇒ ∃r:(num → complex). ∃S:complex. (∀m:num. complex_sums(λn:num. u(m, n), r(m))) ∧ complex_sums(r, S) ∧ complex_sums(λk:num. Σ_{p∈{p:prod(num, num) \| φ(fst(p), snd(p)) = k}} u(fst(p), snd(p)), S)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
