# product_measure — the product of two measures and the exchange of integrals

The product of a measure μ on (Ω, S) and a measure ν on (V, T) gives a
set E of pairs the mass ∫ ν(E_x) μ(dx), E_x = {y | (x, y) ∈ E} its
section at x (`ProductMeasureDef`). The formula is defined for every set
and asks nothing of the factors; the theorems ask that ν be σ-finite for
the section masses to be measurable, and that both be σ-finite for
uniqueness and for integrating in the other order. Sections of sets of
the product σ-algebra are measurable, the product is a measure there
with mass μ(s) ν(t) on each rectangle, it is the only such measure, and
a function on the product integrates in either order: Tonelli for
nonnegative functions, Fubini for integrable ones.

A function on the product is written curried, f(x, y), and read on the
pairs through the projections.

| Member | Statement |
|---|---|
| `ProductMeasureDef` | `product_measure(Ω, S, μ, ν, E) = nonneg_integral(Ω, S, μ, λx. ν({y \| (x, y) ∈ E}))` |
| `ProductSectionMeasurable` | every section of a set of the product σ-algebra is measurable; of the first factor only `S ⊆ {s \| s ⊆ Ω}` is asked |
| `ProductSectionMassMeasurable` | for σ-finite ν the section mass x ↦ ν(E_x) is measurable |
| `ProductMeasureOn` | for σ-finite ν the product is a measure on the product σ-algebra |
| `ProductMeasureRectangle` | `product_measure(Ω, S, μ, ν, set_cross(s, t)) = μ(s) * ν(t)` for a measure μ, `s ∈ S` and any ν with `ν(∅) = &0` |
| `ProductMeasureUnique` | for σ-finite factors a measure with the product mass on rectangles is the product measure |
| `ProductNonnegIntegral` | Tonelli: for σ-finite factors the inner integrals are measurable and the integral over the product is either iterated integral |
| `ProductIntegral` | Fubini: for σ-finite factors the integral of an integrable function over the product is either iterated integral |

The framework mechanics are the standard ones — see
`library/chapter_constitution.md`.
