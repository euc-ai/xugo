# lebesgue_measure — Lebesgue measure on the real line

The outer measure of a set of reals is the infimum of the total lengths of the countable families of intervals that cover it. Carathéodory's criterion selects the measurable sets. They form a σ-algebra containing the intervals and the Borel sets, and on them the outer measure is countably additive.

## The covering lemmas (cover.go)

The length of ⟦a, b⟧ is b − a because a cover of it by open intervals
is at least that long. A closed interval ⟦a, b⟧ covered by open
intervals ⟬c(i), d(i)⟭ is shorter than their total length, an empty
interval counting with length 0. For finitely many intervals this is an
induction on their number: set aside the interval that holds a; if it
reaches past b it is long enough alone, and otherwise the others cover
⟦d(j), b⟧. For a sequence of intervals, Heine–Borel cuts the cover down
to finitely many, which lie in an initial segment 0 .. N.

## The outer measure (definitions.go, outer.go)

A countable cover of s is a pair of sequences of interval ends a, b with
every point of s in some ⟬a(n), b(n)⟭; its total length is the ⟦0, ∞⟧
series of the lengths b(n) − a(n), an empty interval counting 0 because
`extended_of_real` clamps. λ*(s) is the infimum of these lengths. It is
monotone, a cover of a superset covering the subset; it lies below
every cover's length, and above some cover's length less e when finite.
A set inside an open interval ⟬c, d⟭ measures at most d − c — the
interval itself, then empty intervals — so the empty set measures 0.
Countable subadditivity is proved within every e > 0
(`extended_nonneg_real.LeOfLeAddPositive`): if the sum is finite, each
A(n) has a cover within $\frac{e}{2^{n+1}}$ of its measure, and listing all those
intervals along a bijection of the naturals with the pairs of naturals
covers the union, whose length `extended_nonneg_real.SeriesPairing`
turns into the double series, at most the
sum plus e.

## Intervals (interval.go)

⟦a, b⟧ measures b − a: from above it lies inside ⟬a − e/2, b + e/2⟭ for
every e > 0; from below, `CountableCoverLength` puts b − a under an
initial segment of any cover's lengths, which lies below the cover's
total length. ⟬a, b⟭ lies inside ⟦a, b⟧ and, for e ≤ b − a, contains
⟦a + e/2, b − e/2⟧. A point is the degenerate interval ⟦c, c⟧.

## The measurable sets (measurable.go)

A set s is measurable when it cuts every set t additively:
λ*(t) = λ*(t ∩ s) + λ*(t ∖ s). That is Carathéodory's criterion for λ*
on the carrier 𝕌 (`MeasurableIffCaratheodory`). The facts about the
measurable sets are therefore `measure/caratheodory`'s, proved there for
an arbitrary outer measure and read at λ* — the outer measure
`LebesgueOuterMeasureOn` — through that equivalence; the chapter does
not restate them. They are the one-inequality criterion
(`caratheodory.MeasurableIffLe`); ∅, the carrier, complements and null
sets (`EmptyMeasurable`, `CarrierMeasurable`, `ComplementMeasurable`,
`NullMeasurable`); the union, intersection and difference of two sets
and the union of finitely many (`UnionMeasurable`, `InterMeasurable`,
`DiffMeasurable`, `FiniteUnionMeasurable`); additivity over the pieces
that disjoint measurable sets cut from any t (`DisjointAdditive`,
`FiniteAdditive`); countable unions and intersections
(`CountableUnionMeasurable`, `CountableInterMeasurable`); and countable
additivity (`CountablyAdditive`). Finite subadditivity is
`outer_measure.Subadditive` at λ*.

The chapter keeps the construction, the instances and the results
particular to the line. The measurable sets form a σ-algebra on the
line (`LebesgueSigmaAlgebra`, `caratheodory.SigmaAlgebra` at λ*, in
`sigma_algebra`'s sense), whose axioms give the complements and
countable unions the Borel sets are built from, and λ* on them is a
measure (`LebesgueMeasureOn`, below), at which the laws of
`measure/measure_space` read.

## Borel sets (borel.go)

A half-line ⟬c, ∞⟭ cuts every set additively, so it is measurable by
Carathéodory's one-inequality criterion read at λ*. A point c cuts an
open interval ⟬a, b⟭ into two pieces that measure at most b − a
together; cutting every interval of a near-optimal cover of t this way,
countable subadditivity bounds the two pieces of t by the cover's
length, hence by λ*(t) + e for every e > 0. The σ-algebra's complements
and the union of the sets $⟬-\infty, c - \frac{1}{n+1}⟧$, then its
intersections (`sigma_algebra.SigmaFiniteOperations` at
`LebesgueSigmaAlgebra`), give every half-line and interval. An open set
is a countable union of open intervals, and the measurable sets are a
σ-algebra holding the open sets, so they hold every Borel set.
Continuity of the measure along an increasing sequence, and along a
decreasing one of finite first measure, is
`measure_space.MeasureContinuousIncreasing` and
`MeasureContinuousDecreasing` at `LebesgueMeasureOn`.

## Members

| entry | statement |
|---|---|
| `FiniteCoverLength` | `finite(k) ∧ a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ ∃i. i ∈ k ∧ c(i) < x ∧ x < d(i)) ⇒ b − a < Σ_{i∈k} max(d(i) − c(i), &0)` |
| `CountableCoverLength` | `a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ ∃n. c(n) < x ∧ x < d(n)) ⇒ ∃N. b − a < Σ_{n∈0 .. N} max(d(n) − c(n), &0)` |
| `LebesgueOuterMeasureDef` | `lebesgue_outer_measure(s) = extended_inf({m \| ∃a b. (∀x. x ∈ s ⇒ ∃n. a(n) < x ∧ x < b(n)) ∧ m = extended_series(λn. extended_of_real(b(n) − a(n)))})` |
| `OuterMeasureMono` | `s ⊆ t ⇒ lebesgue_outer_measure(s) ≤ lebesgue_outer_measure(t)` |
| `OuterMeasureCoverBound` | `(∀x. x ∈ s ⇒ ∃n. a(n) < x ∧ x < b(n)) ⇒ lebesgue_outer_measure(s) ≤ extended_series(λn. extended_of_real(b(n) − a(n)))` |
| `OuterMeasureCoverApprox` | `lebesgue_outer_measure(s) ≠ extended_infinity ∧ &0 < e ⇒ ∃a b. (∀x. x ∈ s ⇒ ∃n. a(n) < x ∧ x < b(n)) ∧ extended_series(λn. extended_of_real(b(n) − a(n))) ≤ lebesgue_outer_measure(s) + extended_of_real(e)` |
| `OuterMeasureInsideInterval` | `s ⊆ ⟬c, d⟭ ⇒ lebesgue_outer_measure(s) ≤ extended_of_real(d − c)` |
| `OuterMeasureEmpty` | `lebesgue_outer_measure(∅) = &0` |
| `OuterMeasureCountableSubadditive` | `lebesgue_outer_measure({x \| ∃n. x ∈ A(n)}) ≤ extended_series(λn. lebesgue_outer_measure(A(n)))` |
| `OuterMeasureClosedInterval` | `a ≤ b ⇒ lebesgue_outer_measure(⟦a, b⟧) = extended_of_real(b − a)` |
| `OuterMeasureOpenInterval` | `a ≤ b ⇒ lebesgue_outer_measure(⟬a, b⟭) = extended_of_real(b − a)` |
| `OuterMeasureSingleton` | `lebesgue_outer_measure({c}) = &0` |
| `LebesgueMeasurableDef` | `lebesgue_measurable(s) ⇔ ∀t. lebesgue_outer_measure(t) = lebesgue_outer_measure(t ∩ s) + lebesgue_outer_measure(t ∖ s)` |
| `LebesgueSigmaAlgebra` | `sigma_algebra_on(𝕌, {s \| lebesgue_measurable(s)})` |
| `OuterMeasureIntervalCut` | `lebesgue_outer_measure(⟬a, b⟭ ∩ {x \| c < x}) + lebesgue_outer_measure(⟬a, b⟭ ∖ {x \| c < x}) ≤ extended_of_real(b − a)` |
| `OuterMeasureHalfLineCut` | `(∀x. x ∈ t ⇒ ∃n. a(n) < x ∧ x < b(n)) ⇒ lebesgue_outer_measure(t ∩ {x \| c < x}) + lebesgue_outer_measure(t ∖ {x \| c < x}) ≤ extended_series(λn. extended_of_real(b(n) − a(n)))` |
| `MeasurableHalfLine` | `lebesgue_measurable({x \| c < x})` |
| `MeasurableAtMost` | `lebesgue_measurable({x \| x ≤ c})` |
| `MeasurableBelow` | `lebesgue_measurable({x \| x < c})` |
| `MeasurableAtLeast` | `lebesgue_measurable({x \| c ≤ x})` |
| `MeasurableOpenInterval` | `lebesgue_measurable(⟬a, b⟭)` |
| `MeasurableClosedInterval` | `lebesgue_measurable(⟦a, b⟧)` |
| `MeasurableOpen` | `u ∈ real_topology ⇒ lebesgue_measurable(u)` |
| `MeasurableBorel` | `s ∈ borel_sets(real_topology) ⇒ lebesgue_measurable(s)` |

## General measure instances

The interval-cover construction satisfies the general outer-measure axioms by its empty-set, monotonicity, and countable-subadditivity laws. Lebesgue measurability is Carathéodory's criterion for this outer measure (`MeasurableIffCaratheodory`), so Carathéodory's theorem, `caratheodory.MeasureOnCaratheodory`, gives the general measure instance.

| Entry | Statement |
| --- | --- |
| `LebesgueOuterMeasureOn` | `outer_measure_on(𝕌, lebesgue_outer_measure)` |
| `LebesgueMeasureOn` | `measure_on(𝕌, {s:set(real) \| lebesgue_measurable(s)}, lebesgue_outer_measure)` |
| `LebesgueSigmaFinite` | `sigma_finite_on(𝕌, {E \| lebesgue_measurable(E)}, lebesgue_outer_measure)` |
| `MeasurableIffCaratheodory` | `lebesgue_measurable(s) ⇔ s ∈ caratheodory_sets(𝕌, lebesgue_outer_measure)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
