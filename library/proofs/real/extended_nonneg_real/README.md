# extended_nonneg_real — the extended nonnegative reals ⟦0, ∞⟧

Lengths, measures and integrals of nonnegative functions take values in ⟦0, ∞⟧: the nonnegative reals with a top element ∞. The order is complete, so every set has a supremum, and every series of nonnegative terms has a sum, its partial sums' supremum. The chapter defines the type, its order, addition and multiplication (with 0 · ∞ = 0), suprema and countable sums, and proves the laws measure theory uses.

## How the chapter is organized

An extended value is an optional real: absent for ∞, present and
nonnegative otherwise. Only ∞ and the embedding `extended_of_real` read
that representation; the embedding clamps a negative real to 0, so it is
total and monotone. Every other operation is defined by cases on ∞
through the finite value `extended_to_real` (0 at ∞), and the compound
laws are argued in two halves: when its sides are ∞ (`AddEqInfinity`,
`MulEqInfinity`), and what their finite values are (`ToRealAdd`,
`ToRealMul`); `ExtendedEq` joins the two halves. Sums and products read
`x + y` and `x * y` on the type, and the order `x ≤ y` and `x < y`
(`extended_le`, `extended_lt`), and 0 · ∞ = 0. A numeral is written
`&n` where a value of ⟦0, ∞⟧ is meant (`&0`, `&1`); the embedding
applied to a real keeps its name, `extended_of_real(x)`, since a
negative real goes to 0.

**Sums, suprema and series.** Finite sums are the fold at extended
addition, so Σ reads on the type. Every set has a supremum and an
infimum: a set with no finite upper bound has supremum ∞, and otherwise
its supremum is the image of the real supremum of its finite values; the
infimum is the supremum of the lower bounds. A series sums to the
supremum of its partial sums, which rise, so every series of ⟦0, ∞⟧
terms has a sum. A double series sums to the same value in either order
(`SeriesExchange`); regrouped, it sums along any map of its index pairs
(below, "Regrouping a double series"). A sum of zeros is zero
(`ExtendedSumZero`); the supremum of a finite sum of rising sequences is
the sum of their suprema (`SupSequenceSum`), and a lower bound of every
term lies below the infimum (`InfSequenceGreatest`). A series whose
terms vanish past N is its partial sum to N (`SeriesEventuallyZero`),
and a bound on every partial sum plus y bounds the series plus y
(`SeriesAddLe`).

**Bounds against + and ·.** A bound that holds within every e > 0
holds (`LeOfLeAddPositive`), and one that holds at every scale c < 1
holds (`LeOfScaledLe`); a finite summand cancels from both sides
(`AddLeCancel`).

## Members

| entry | statement |
|---|---|
| `ExtendedNonnegRealInhabited` | `∃o:option(real). ∀r:real. o = some(r) ⇒ &0 ≤ r` |
| `ExtendedNonnegRealRetraction` | the type of the options whose value, if any, is nonnegative: `extended_of_option(option_of_extended(a)) = a` |
| `ExtendedNonnegRealMembership` | `(∀s. r = some(s) ⇒ &0 ≤ s) ⇔ option_of_extended(extended_of_option(r)) = r` |
| `ExtendedInfinityDef` | `extended_infinity = extended_of_option(none)` |
| `ExtendedOfRealDef` | `extended_of_real(r) = extended_of_option(some(max(r, &0)))` |
| `ExtendedToRealDef` | `extended_to_real(x) = if x = extended_infinity then &0 else εr. &0 ≤ r ∧ extended_of_real(r) = x` |
| `ExtendedLeDef` | `x ≤ y ⇔ y = extended_infinity ∨ (x ≠ extended_infinity ∧ extended_to_real(x) ≤ extended_to_real(y))` |
| `ExtendedLtDef` | `x < y ⇔ x ≤ y ∧ x ≠ y` |
| `ExtendedAddDef` | `x + y = if x = extended_infinity ∨ y = extended_infinity then extended_infinity else extended_of_real(extended_to_real(x) + extended_to_real(y))` |
| `ExtendedMulDef` | `x * y` is 0 if either factor is 0, else ∞ if either is ∞, else `extended_of_real(extended_to_real(x) · extended_to_real(y))` |
| `ExtendedCases` | `x = extended_infinity ∨ (∃r. &0 ≤ r ∧ x = extended_of_real(r))` |
| `OfRealRepresentative` | `option_of_extended(extended_of_real(r)) = some(max(r, &0))` |
| `OfRealNotInfinity` | `extended_of_real(r) ≠ extended_infinity` |
| `ZeroNotInfinity` | `&0 ≠ extended_infinity` |
| `OfRealInjective` | `&0 ≤ r ∧ &0 ≤ s ⇒ (extended_of_real(r) = extended_of_real(s) ⇔ r = s)` |
| `OfRealNeg` | `r ≤ &0 ⇒ extended_of_real(r) = &0` |
| `ToRealOfReal` | `&0 ≤ r ⇒ extended_to_real(extended_of_real(r)) = r` |
| `ToRealOfRealMax` | `extended_to_real(extended_of_real(r)) = max(r, &0)` |
| `ToRealInfinity` | `extended_to_real(extended_infinity) = &0` |
| `ToRealZero` | `extended_to_real(&0) = &0` |
| `OfRealToReal` | `x ≠ extended_infinity ⇒ extended_of_real(extended_to_real(x)) = x` |
| `ToRealNonneg` | `&0 ≤ extended_to_real(x)` |
| `ExtendedEq` | `x = y ⇔ (x = extended_infinity ⇔ y = extended_infinity) ∧ extended_to_real(x) = extended_to_real(y)` |
| `LeRefl` | `x ≤ x` |
| `LeTrans` | `x ≤ y ∧ y ≤ z ⇒ x ≤ z` |
| `LeAntisym` | `x ≤ y ∧ y ≤ x ⇒ x = y` |
| `LeTotal` | `x ≤ y ∨ y ≤ x` |
| `ZeroLe` | `&0 ≤ x` |
| `LeInfinity` | `x ≤ extended_infinity` |
| `EqInfinityIffAboveNaturals` | `y = extended_infinity ⇔ ∀n. &n < y` |
| `OfRealLe` | `&0 ≤ s ⇒ (extended_of_real(r) ≤ extended_of_real(s) ⇔ r ≤ s)` |
| `LtIffNotLe` | `x < y ⇔ ¬(y ≤ x)` |
| `OfRealLt` | `extended_of_real(r) < extended_of_real(y) ⇔ r < y ∧ &0 < y` |
| `OfRealMono` | `extended_of_real` is monotone |
| `OfRealPositivePart` | `extended_of_real(max(r, &0)) = extended_of_real(r)` |
| `AddEqInfinity` | `x + y = extended_infinity ⇔ x = extended_infinity ∨ y = extended_infinity` |
| `ToRealAdd` | `x ≠ extended_infinity ∧ y ≠ extended_infinity ⇒ extended_to_real(x + y) = extended_to_real(x) + extended_to_real(y)` |
| `AddInfinity` | `x + extended_infinity = extended_infinity` |
| `AddComm` | `x + y = y + x` |
| `AddZero` | `x + &0 = x` |
| `OfRealAdd` | `&0 ≤ r ∧ &0 ≤ s ⇒ extended_of_real(r) + extended_of_real(s) = extended_of_real(r + s)` |
| `AddAssoc` | `x + y + z = x + (y + z)` |
| `AddLeMono` | `x ≤ y ⇒ x + z ≤ y + z` |
| `AddLeAdd` | `x₁ ≤ x₂ ∧ y₁ ≤ y₂ ⇒ x₁ + y₁ ≤ x₂ + y₂` |
| `LeAddRight` | `x ≤ x + y` |
| `AddLeCancel` | `x + z ≤ y + z ∧ z ≠ extended_infinity ⇒ x ≤ y` |
| `LeOfLeAddPositive` | `(∀e. &0 < e ⇒ x ≤ y + extended_of_real(e)) ⇒ x ≤ y` |
| `AddEqZero` | `x + y = &0 ⇔ x = &0 ∧ y = &0` |
| `MulEqInfinity` | `x * y = extended_infinity ⇔ x = extended_infinity ∧ y ≠ &0 ∨ y = extended_infinity ∧ x ≠ &0` |
| `ToRealMul` | `extended_to_real(x * y) = extended_to_real(x) · extended_to_real(y)` |
| `MulEqZero` | `x * y = &0 ⇔ x = &0 ∨ y = &0` |
| `MulComm` | `x * y = y * x` |
| `MulZero` | `x * &0 = &0` |
| `MulInfinity` | `x ≠ &0 ⇒ x * extended_infinity = extended_infinity` |
| `OfRealMul` | `&0 ≤ r ⇒ extended_of_real(r) * extended_of_real(s) = extended_of_real(r * s)` |
| `MulOne` | `x * &1 = x` |
| `MulAssoc` | `x * y * z = x * (y * z)` |
| `MulAddDistrib` | `x * (y + z) = x * y + x * z` |
| `MulLeMono` | `x ≤ y ⇒ z * x ≤ z * y` |
| `LeOfScaledLe` | `(∀c. &0 < c ∧ c < &1 ⇒ extended_of_real(c) * x ≤ y) ⇒ x ≤ y` |
| `ExtendedSumDef` | `extended_sum = iterated_op(extended_add)` — Σ over ⟦0, ∞⟧, written `Σ_{i∈s} f(i)` |
| `AddMonoid` | `comm_monoid(extended_add, &0)` |
| `MonoidalAdd` | `monoidal_op(extended_add)` |
| `NeutralAdd` | `neutral_elem(extended_add) = &0` |
| `SumClauses` | `sum(∅, f) = &0`; `finite(s) ⇒ sum(insert(x, s), g) = if x ∈ s then sum(s, g) else g(x) + sum(s, g)` |
| `SumAdd` | `finite(s) ⇒ Σ_{i∈s} (f(i) + g(i)) = Σ_{i∈s} f(i) + Σ_{i∈s} g(i)` |
| `SumScale` | `finite(s) ⇒ c * (Σ_{i∈s} f(i)) = Σ_{i∈s} c * f(i)` |
| `SumMono` | `finite(s) ∧ (∀i. i ∈ s ⇒ f(i) ≤ g(i)) ⇒ Σ_{i∈s} f(i) ≤ Σ_{i∈s} g(i)` |
| `ExtendedSumZero` | `(∀i. i ∈ s ⇒ f(i) = &0) ⇒ Σ_{i∈s} f(i) = &0` |
| `SumSubsetLe` | `finite(t) ∧ s ⊆ t ⇒ Σ_{i∈s} f(i) ≤ Σ_{i∈t} f(i)` |
| `SumEqInfinity` | `finite(s) ⇒ (Σ_{i∈s} f(i) = extended_infinity ⇔ ∃i. i ∈ s ∧ f(i) = extended_infinity)` |
| `SumOfReal` | `finite(s) ∧ (∀i. i ∈ s ⇒ &0 ≤ f(i)) ⇒ Σ_{i∈s} extended_of_real(f(i)) = extended_of_real(Σ_{i∈s} f(i))` |
| `SumSegmentZero` | `Σ_{i∈0 .. 0} a(i) = a(0)` |
| `SumSegmentPeel` | `Σ_{i∈0 .. n + 1} a(i) = Σ_{i∈0 .. n} a(i) + a(n + 1)` |
| `ExtendedSupDef` | `extended_sup(s) = εa. (∀x. x ∈ s ⇒ x ≤ a) ∧ ∀b. (∀x. x ∈ s ⇒ x ≤ b) ⇒ a ≤ b` |
| `ExtendedInfDef` | `extended_inf(s)` is the chosen greatest lower bound of s, defined the same way |
| `SupExists` | every set of ⟦0, ∞⟧ has a least upper bound |
| `SupUpper` | `x ∈ s ⇒ x ≤ extended_sup(s)` |
| `SupLeast` | `(∀x. x ∈ s ⇒ x ≤ z) ⇒ extended_sup(s) ≤ z` |
| `InfExists` | every set of ⟦0, ∞⟧ has a greatest lower bound |
| `InfLower` | `x ∈ s ⇒ extended_inf(s) ≤ x` |
| `InfGreatest` | `(∀x. x ∈ s ⇒ z ≤ x) ⇒ z ≤ extended_inf(s)` |
| `InfSequenceGreatest` | `(∀n. z ≤ a(n)) ⇒ z ≤ extended_inf(image(a, 𝕌))` |
| `SupEmpty` | `extended_sup(∅) = &0` |
| `InfEmpty` | `extended_inf(∅) = extended_infinity` |
| `SupMono` | `s ⊆ t ⇒ extended_sup(s) ≤ extended_sup(t)` |
| `InfAntitone` | `s ⊆ t ⇒ extended_inf(t) ≤ extended_inf(s)` |
| `SupApprox` | `x < extended_sup(s) ⇒ ∃y. y ∈ s ∧ x < y` |
| `InfApprox` | `extended_inf(s) < x ⇒ ∃y. y ∈ s ∧ y < x` |
| `SupSequenceUpper` | `a(n) ≤ extended_sup(image(a, 𝕌))` |
| `SupSequenceLeast` | `(∀n. a(n) ≤ z) ⇒ extended_sup(image(a, 𝕌)) ≤ z` |
| `IncreasingLe` | `(∀k. a(k) ≤ a(k + 1)) ∧ m ≤ n ⇒ a(m) ≤ a(n)` |
| `SupAddLe` | `s ≠ ∅ ∧ (∀x. x ∈ s ⇒ x + y ≤ z) ⇒ extended_sup(s) + y ≤ z` |
| `SupSequenceAdd` | `(∀n. a(n) ≤ a(n + 1)) ∧ (∀n. b(n) ≤ b(n + 1)) ⇒ extended_sup(image(λn. a(n) + b(n), 𝕌)) = extended_sup(image(a, 𝕌)) + extended_sup(image(b, 𝕌))` |
| `SupSequenceOfReal` | `(∀n. &0 ≤ a(n)) ∧ (∀n. a(n) ≤ a(n + 1)) ∧ &0 ≤ l ⇒ (a ⟶ l ⇔ extended_sup(image(λn. extended_of_real(a(n)), 𝕌)) = extended_of_real(l))` |
| `SupScale` | `c * extended_sup(T) = extended_sup(image(λx. c * x, T))` for every c ∈ ⟦0, ∞⟧ and every set T (0·∞ = 0; T = ∅ gives 0) |
| `SupSequenceScaleExtended` | `c * extended_sup(image(a, 𝕌)) = extended_sup(image(λn. c * a(n), 𝕌))` for every c ∈ ⟦0, ∞⟧, no monotonicity |
| `SupSequenceScale` | `&0 ≤ c ⇒ extended_sup(image(λn. extended_of_real(c) * a(n), 𝕌)) = extended_of_real(c) * extended_sup(image(a, 𝕌))` |
| `SupSequenceSum` | `finite(k) ∧ (∀i n. i ∈ k ⇒ a(i)(n) ≤ a(i)(n + 1)) ⇒ extended_sup(image(λn. Σ_{i∈k} a(i)(n), 𝕌)) = Σ_{i∈k} extended_sup(image(a(i), 𝕌))` |
| `ExtendedSeriesDef` | `extended_series(a) = extended_sup(image(λn. Σ_{i∈0 .. n} a(i), 𝕌))` |
| `SeriesPartialLe` | `Σ_{i∈0 .. n} a(i) ≤ extended_series(a)` |
| `SeriesLeast` | `(∀n. Σ_{i∈0 .. n} a(i) ≤ z) ⇒ extended_series(a) ≤ z` |
| `SeriesEventuallyZero` | `(∀n. N < n ⇒ a(n) = &0) ⇒ extended_series(a) = Σ_{i∈0 .. N} a(i)` |
| `SeriesAddLe` | `(∀n. Σ_{i∈0 .. n} a(i) + y ≤ z) ⇒ extended_series(a) + y ≤ z` |
| `SeriesMono` | `(∀n. a(n) ≤ b(n)) ⇒ extended_series(a) ≤ extended_series(b)` |
| `SeriesAdd` | `extended_series(λn. a(n) + b(n)) = extended_series(a) + extended_series(b)` |
| `SeriesScale` | `&0 ≤ c ⇒ extended_series(λn. extended_of_real(c) * a(n)) = extended_of_real(c) * extended_series(a)` |
| `SeriesZero` | `extended_series(λn. &0) = &0` |
| `SeriesOfRealPartialLe` | `(∀k. &0 ≤ a(k)) ∧ extended_series(λk. extended_of_real(a(k))) ≠ extended_infinity ⇒ Σ_{i∈0 .. n} a(i) ≤ extended_to_real(extended_series(λk. extended_of_real(a(k))))` |
| `SeriesOfReal` | `(∀n. &0 ≤ a(n)) ∧ real_sums(a, s) ⇒ extended_series(λn. extended_of_real(a(n))) = extended_of_real(s)` |
| `SeriesFinite` | `(∀n. &0 ≤ a(n)) ∧ extended_series(λn. extended_of_real(a(n))) ≠ extended_infinity ⇒ real_sums(a, extended_to_real(extended_series(λn. extended_of_real(a(n)))))` |
| `SeriesGeometric` | `&0 ≤ e ⇒ extended_series(λn. extended_of_real(e / real_pow(&2, n + 1))) = extended_of_real(e)` |
| `SeriesSegmentSum` | `Σ_{m∈0 .. M} extended_series(λn. a(m, n)) = extended_series(λn. Σ_{m∈0 .. M} a(m, n))` |
| `SeriesExchange` | `extended_series(λm. extended_series(λn. a(m, n))) = extended_series(λn. extended_series(λm. a(m, n)))` |

## Regrouping a double series (regroup.go)

A double series of extended nonnegative reals may be summed along the
fibres of any map of its index pairs (`SeriesRegroup`, from
`SeriesExchange`). On finite supports, the double series is the finite
sum (`SeriesFinitePairs`). Along an enumeration σ of the index pairs,
the regrouping along σ's inverse, whose fibres are single points, gives
the enumerated series (`SeriesPairing`). The real embedding carries
regrouping to nonnegative real series (`NonnegativeSummableRegroup`).
For signed reals the same holds when the series is absolutely summable
and the fibres are finite, by positive and negative parts
(`AbsolutelySummableRegroup`).

In the regrouping statements, `«fibre»(k)` denotes the set of pairs
`{p:prod(num, num) | φ(fst(p), snd(p)) = k}`.

| member | statement |
|---|---|
| `SeriesSingleton` | `extended_series(λn:num. COND(n = N, x, &0)) = x` |
| `SeriesRegroup` | `∀a:(num → num → extended_nonneg_real). ∀φ:(num → num → num). extended_series(λk:num. extended_series(λm:num. extended_series(λn:num. COND(φ(m, n) = k, a(m, n), &0)))) = extended_series(λm:num. extended_series(λn:num. a(m, n)))` |
| `SeriesFinitePairs` | `finite(s) ⇒ extended_series(λm. extended_series(λn. COND((m, n) ∈ s, a(m, n), &0))) = Σ_{p∈s} a(fst(p), snd(p))` |
| `SeriesPairing` | `injective_on(𝕌, σ) ∧ image(σ, 𝕌) = 𝕌 ⇒ extended_series(λk. a(fst(σ(k)), snd(σ(k)))) = extended_series(λm. extended_series(λn. a(m, n)))` |
| `NonnegativeSummableRegroup` | `(∀m n. &0 ≤ u(m, n)) ∧ (∀m. real_sums(λn. u(m, n), R(m))) ∧ real_sums(R, T) ∧ (∀k. finite({p \| φ(fst(p), snd(p)) = k})) ⇒ real_sums(λk. Σ_{p∈{p \| φ(fst(p), snd(p)) = k}} u(fst(p), snd(p)), T)` |
| `AbsolutelySummableRegroup` | `∀u:(num → num → real). ∀φ:(num → num → num). ∀R:(num → real). ∀T:real. (∀m:num. real_sums(λn:num. \|u(m, n)\|, R(m))) ∧ real_sums(R, T) ∧ (∀k:num. finite({p:prod(num, num) \| φ(fst(p), snd(p)) = k})) ⇒ ∃r:(num → real). ∃S:real. (∀m:num. real_sums(λn:num. u(m, n), r(m))) ∧ real_sums(r, S) ∧ real_sums(λk:num. Σ_{p∈{p:prod(num, num) \| φ(fst(p), snd(p)) = k}} u(fst(p), snd(p)), S)` |

## Lower limits

The lower limit is the supremum of tail infima. For a nonnegative real sequence, a real lower bound of that extended lower limit is eventually attained up to every positive error (`LowerLimitEventually`).

| Entry | Statement |
| --- | --- |
| `ExtendedLiminfDef` | The supremum of the infima of the tails |
| `LowerLimitEventually` | A lower bound of the extended lower limit is approached from below up to any positive error |
| `LimitLeLiminf` | The limit of a convergent real sequence lies below the extended lower limit of its embedding: `a ⟶ l ⇒ extended_of_real(l) ≤ extended_liminf(λn. extended_of_real(a(n)))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
