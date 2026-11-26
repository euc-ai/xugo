# real_continuous — continuous real functions

A function `f : ℝ → ℝ` is continuous at c when the values near c are
near f(c): every `ε > 0` has a `δ > 0` with `|f(x) − f(c)| < ε`
whenever `|x − c| < δ`. Unlike a limit, the point c itself is not
excluded — the value there is what the nearby values are measured
against. Continuity on a set s compares only points of s, so that an
interval's endpoint asks nothing of the function outside the interval.

This chapter is where the readings of continuity meet: its own ε-δ
definition, the limit of `real_function_limits` (continuity at c is
tending to f(c) there), and the open-set reading of
`topology/continuous`, at the topology `real/real_topology` puts on the
line. Through that meeting the two headline theorems of elementary
analysis become corollaries of the abstract chapter: a continuous map
carries connected sets to connected sets, and on the line the connected
sets are the intervals — the intermediate value theorem; it carries
compact sets to compact sets, and a compact set of reals holds its
greatest and least elements — the extreme value theorem.

Statements write `connected_in(s)` for the line's: the family binds the
one topology it works at, and family.go says how.

## The chapter has five movements

**1. Continuity at a point and on a set.** Continuity at c is the limit
with the centre put back in: `f` is continuous at c exactly when it
tends to f(c) at c, the same radius answering the same ε both ways,
because at c itself the value is at distance 0 from f(c). A function
continuous at c carries every sequence tending to c to one tending to
f(c) — the sequential reading, which unlike the limit's needs no term to
avoid c. Continuity at every point of s gives continuity on s, and
continuity on s gives it on every subset.

**2. The algebra of continuity.** A constant is continuous on every set.
Sums, negatives and products of functions continuous on a set are
continuous there too: `ContinuousOnIffMap` identifies them with
continuous maps from the subspace to the real line, where the general
algebra laws apply. Differences follow by addition and negation.
Composition on sets uses the same bridge: a continuous `g` carrying
`s` into `t` is a map into the subspace `t`, so composing with a
continuous map from `t` gives continuity on `s` (`ContinuousOnCompose`).
At a point, product continuity follows from the product limit, while
composition passes the radius requested by `f` to `g` as its tolerance.

**3. Two readings of continuity.** A function continuous on s is exactly
a continuous map from the subspace s to the line: the preimage of an
open set is the trace on s of a union of balls — the balls about the
points of s on which s lands in the open set — and a union of balls is
always open; conversely the preimage of a ball about f(c) is open in the
subspace, so it holds a whole ball about c cut to s. On the whole line
the two readings agree outright: a continuous map of the line to itself
is a function continuous at every point. A real polynomial function is a
continuous map of the line, read on the open-set side: the polynomial
functions are generated from the identity and the constants by sums and
products (`real_polynomial`'s induction principle), and each of these is
a continuous map (`topology/continuous`, `topology/real_valued`).

**4. What continuity carries.** A function continuous on a connected or
compact set maps it onto a connected or compact set: the set is
connected or compact in the subspace s as it is in the line
(the trace lemmas of `topology/connected` and `topology/compact`), f is a continuous map from that
subspace, and the abstract chapter's image theorems apply. On the line
a continuous image of an interval is an interval, so the values of a
function continuous on ⟦a, b⟧ form an interval holding f(a) and f(b),
and the function takes every value between the two, whichever is the
larger — the intermediate value theorem, in its two forms. A function
continuous and injective on an interval is therefore strictly increasing
or strictly decreasing there: between two points of the interval it takes
every value strictly between theirs at a point strictly between them, and
an injective map with that property is strictly monotone in any ordered
field (`ordered_field.IntermediateValueInjectiveMonotone`, read at ℝ
through `real_ordered_instance`). The values on ⟦a, b⟧ also form a
non-empty compact set, ⟦a, b⟧ being compact, and a non-empty compact set
holds its supremum and infimum, so the function takes a greatest and a
least value there — the extreme value theorem.

**5. Uniform continuity, and inverses.** A function is uniformly
continuous on s when one radius serves every centre at once for each ε,
and such a function is continuous on s. On a compact set the converse
holds (Heine–Cantor). Were some ε to have no radius, each radius
$\frac{1}{n+1}$ would be beaten by a pair of points of s, and the pairs form
two sequences. Compactness gives a subsequence of the first tending to
a point l of s, and the second follows it there, its distance from the
first being below $\frac{1}{k+1}$ along the subsequence. Continuity at l then
puts the two values within ε of each other after all. On a closed
interval this is the form the integral reads. Order alone makes an
inverse continuous: a local right inverse g of a function f strictly
increasing on a set holding a ball about g(c) is continuous at c. f puts
c strictly between its values at g(c) ± r, and a strictly increasing f
reflects the strict order, so every y close enough to c has g(y)
between g(c) − r and g(c) + r.

## Members

| entry | statement |
|---|---|
| `RealContinuousAtDef` | `real_continuous_at(f, c) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. real_abs(x − c) < δ ⇒ real_abs(f(x) − f(c)) < ε` |
| `RealContinuousOnDef` | `real_continuous_on(s, f) ⇔ ∀c. c ∈ s ⇒ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x. x ∈ s ∧ real_abs(x − c) < δ ⇒ real_abs(f(x) − f(c)) < ε` |
| `RealIncreasingOnDef` | `real_increasing_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ x ≤ y ⇒ f(x) ≤ f(y)` |
| `RealStrictlyIncreasingOnDef` | `real_strictly_increasing_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(x) < f(y)` |
| `RealDecreasingOnDef` | `real_decreasing_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ x ≤ y ⇒ f(y) ≤ f(x)` |
| `RealStrictlyDecreasingOnDef` | `real_strictly_decreasing_on(s, f) ⇔ ∀x y. x ∈ s ∧ y ∈ s ∧ x < y ⇒ f(y) < f(x)` |
| `ContinuousAtIffLimit` | `real_continuous_at(f, c) ⇔ f ⟶ f(c) (at c)` |
| `ContinuousAtSequential` | `real_continuous_at(f, c) ∧ a ⟶ c ⇒ f ∘ a ⟶ f(c)` |
| `ContinuousAtOn` | `(∀c. c ∈ s ⇒ real_continuous_at(f, c)) ⇒ real_continuous_on(s, f)` |
| `ContinuousAtInterior` | `real_continuous_on(s, f) ∧ &0 < δ ∧ (∀x. real_abs(x − c) < δ ⇒ x ∈ s) ⇒ real_continuous_at(f, c)` |
| `ContinuousOnSubset` | `real_continuous_on(s, f) ∧ t ⊆ s ⇒ real_continuous_on(t, f)` |
| `ContinuousOnConst` | `real_continuous_on(s, λx. k)` |
| `ContinuousOnId` | `real_continuous_on(s, λx. x)` |
| `ContinuousOnAdd` | `real_continuous_on(s, f) ∧ real_continuous_on(s, g) ⇒ real_continuous_on(s, λx. f(x) + g(x))` |
| `ContinuousOnNeg` | `real_continuous_on(s, f) ⇒ real_continuous_on(s, λx. −f(x))` |
| `ContinuousOnSub` | `real_continuous_on(s, f) ∧ real_continuous_on(s, g) ⇒ real_continuous_on(s, λx. f(x) − g(x))` |
| `ContinuousOnMul` | `real_continuous_on(s, f) ∧ real_continuous_on(s, g) ⇒ real_continuous_on(s, λx. f(x) · g(x))` |
| `ContinuousOnAbs` | `real_continuous_on(s, f) ⇒ real_continuous_on(s, λx. \|f(x)\|)` |
| `ContinuousAtMul` | `real_continuous_at(f, c) ∧ real_continuous_at(g, c) ⇒ real_continuous_at(λx. f(x) · g(x), c)` |
| `ContinuousAtCompose` | `real_continuous_at(g, c) ∧ real_continuous_at(f, g(c)) ⇒ real_continuous_at(f ∘ g, c)` |
| `ContinuousOnCompose` | `real_continuous_on(s, g) ∧ real_continuous_on(t, f) ∧ (∀x. x ∈ s ⇒ g(x) ∈ t) ⇒ real_continuous_on(s, f ∘ g)` |
| `ContinuousOnIffMap` | `real_continuous_on(s, f) ⇔ continuous_map(subtopology(s), real_topology, f)` |
| `ContinuousOnUnivIffMap` | `real_continuous_on(𝕌, f) ⇔ continuous_map(real_topology, real_topology, f)` |
| `ContinuousMapIffPointwise` | `continuous_map(real_topology, real_topology, f) ⇔ ∀c. real_continuous_at(f, c)` |
| `PolynomialFunctionContinuous` | `polynomial_function(f) ⇒ continuous_map(real_topology, real_topology, f)` |
| `ContinuousImageConnected` | `real_continuous_on(s, f) ∧ connected_in(s) ⇒ connected_in(image(f, s))` |
| `ContinuousImageCompact` | `real_continuous_on(s, f) ∧ compact_in(s) ⇒ compact_in(image(f, s))` |
| `ContinuousImageInterval` | `real_continuous_on(s, f) ∧ real_interval(s) ⇒ real_interval(image(f, s))` |
| `ValuesInterval` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ real_interval(image(f, ⟦a, b⟧)) ∧ f(a) ∈ … ∧ f(b) ∈ …` |
| `IntermediateValue` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ∧ f(a) ≤ y ∧ y ≤ f(b) ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ f(x) = y` |
| `IntermediateValueDecreasing` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ∧ f(b) ≤ y ∧ y ≤ f(a) ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ f(x) = y` |
| `ContinuousInjectiveMonotone` | `real_interval(s) ∧ real_continuous_on(s, f) ∧ injective_on(s, f) ⇒ real_strictly_increasing_on(s, f) ∨ real_strictly_decreasing_on(s, f)` |
| `ValuesCompact` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ compact_in(image(f, ⟦a, b⟧)) ∧ image(f, ⟦a, b⟧) ≠ ∅` |
| `ExtremeValueMax` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ ∀y. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(x)` |
| `ExtremeValueMin` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ ∃x. a ≤ x ∧ x ≤ b ∧ ∀y. a ≤ y ∧ y ≤ b ⇒ f(x) ≤ f(y)` |
| `MonotoneInverseContinuous` | `real_strictly_increasing_on(s, f) ∧ &0 < e ∧ (∀y. real_abs(y − c) < e ⇒ g(y) ∈ s ∧ f(g(y)) = y) ∧ &0 < d ∧ (∀x. real_abs(x − g(c)) < d ⇒ x ∈ s) ⇒ real_continuous_at(g, c)` |
| `RealUniformlyContinuousOnDef` | `real_uniformly_continuous_on(s, f) ⇔ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀x y. x ∈ s ∧ y ∈ s ∧ real_abs(x − y) < δ ⇒ real_abs(f(x) − f(y)) < ε` |
| `UniformlyContinuousContinuous` | `real_uniformly_continuous_on(s, f) ⇒ real_continuous_on(s, f)` |
| `ContinuousCompactUniformlyContinuous` | `compact_in(s) ∧ real_continuous_on(s, f) ⇒ real_uniformly_continuous_on(s, f)` |
| `ContinuousClosedIntervalUniformlyContinuous` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ real_uniformly_continuous_on(⟦a, b⟧, f)` |
| `NonexpansiveUniformlyContinuous` | `(∀x y. \|f(x) - f(y)\| ≤ \|x - y\|) ⇒ real_uniformly_continuous_on(𝕌, f)` |
| `ClampedUniformlyContinuous` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ real_uniformly_continuous_on(𝕌, λx. f(max(a, min(b, x))))` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
