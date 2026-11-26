# caratheodory — Caratheodory measurable sets of an outer measure

A set is Caratheodory measurable if it splits every subset of the carrier additively. This criterion extracts a complete measure from an outer measure without choosing a completion of a pre-existing sigma algebra. The Carathéodory sets of an outer measure are closed under complements in the carrier and under finite and countable unions and intersections, so they form a sigma algebra; the outer measure is countably additive on it, and every set of outer measure zero belongs to it. Carathéodory's theorem, MeasureOnCaratheodory, puts these together as measure_on. Two facts ask nothing of μ: complements, and additivity over a disjoint sequence. The real line's Lebesgue measure is the instance at lebesgue_outer_measure.

## Members

| Entry | Statement |
| --- | --- |
| `CaratheodorySetsDef` | caratheodory_sets |
| `MeasurableIffLe` | s ∈ caratheodory_sets(Ω, μ) ⇔ (∀t:set(A). t ⊆ Ω ⇒ μ(t ∩ s) + μ(t ∖ s) ≤ μ(t)) |
| `ComplementMeasurable` | Ω ∖ s ∈ caratheodory_sets(Ω, μ) |
| `EmptyMeasurable` | ∅ ∈ caratheodory_sets(Ω, μ) |
| `CarrierMeasurable` | Ω ∈ caratheodory_sets(Ω, μ) |
| `NullMeasurable` | s ∈ caratheodory_sets(Ω, μ) |
| `UnionMeasurable` | s ∪ u ∈ caratheodory_sets(Ω, μ) |
| `InterMeasurable` | s ∩ u ∈ caratheodory_sets(Ω, μ) |
| `DiffMeasurable` | s ∖ u ∈ caratheodory_sets(Ω, μ) |
| `FiniteUnionMeasurable` | {x:A \| ∃k:num. k < n ∧ x ∈ E(k)} ∈ caratheodory_sets(Ω, μ) |
| `DisjointAdditive` | μ(t ∩ {x:A \| ∃k:num. k ≤ n ∧ x ∈ E(k)}) = Σ_{k∈0 .. n} μ(t ∩ E(k)) |
| `FiniteAdditive` | μ(t ∩ {x:A \| ∃i:B. i ∈ k ∧ x ∈ E(i)}) = Σ_{i∈k} μ(t ∩ E(i)) |
| `CountableUnionMeasurable` | ⋃image(a, 𝕌) ∈ caratheodory_sets(Ω, μ) |
| `CountableInterMeasurable` | ⋂image(a, 𝕌) ∈ caratheodory_sets(Ω, μ) |
| `CountablyAdditive` | μ(⋃image(a, 𝕌)) = extended_series(λn:num. μ(a(n))) |
| `SigmaAlgebra` | sigma_algebra_on(Ω, caratheodory_sets(Ω, μ)) |
| `MeasureOnCaratheodory` | measure_on(Ω, caratheodory_sets(Ω, μ), μ) |
