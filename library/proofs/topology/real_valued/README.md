# real_valued — continuous real-valued functions on a space: Urysohn's lemma, Tietze's extension and complete regularity

Normality matters through two theorems that produce real-valued
functions: Urysohn's lemma, a continuous function into ⟦0, 1⟧ that is 0
on one closed set and 1 on a disjoint one, and Tietze's theorem, that a
continuous real function on a closed set extends to the whole space,
within the same bounds when it is bounded. Both read the line's
topology, so the chapter sits above ℝ, beside `metric_space`, while the
separation axioms themselves — what `normal_space` and `regular_space`
say with open and closed sets alone — are `separation`'s, below it. A
space in which a point and a closed set not holding it are separated by
such a function is completely regular,
`completely_regular_space(T)`; the definition reads the line, so it is
minted here.

## The definition

| member | statement |
|---|---|
| `CompletelyRegularSpaceDef` | `completely_regular_space(T) ⇔ ∀c. ∀x. closed_in(T, c) ∧ x ∈ ⋃T ∧ x ∉ c ⇒ ∃f. continuous_map(T, real_topology, f) ∧ (∀y. y ∈ ⋃T ⇒ &0 ≤ f(y) ∧ f(y) ≤ &1) ∧ f(x) = &0 ∧ (∀y. y ∈ c ⇒ f(y) = &1)` |

## Real-valued maps on a space (real_valued.go, abs_quotient.go, urysohn.go)

A real-valued map on a space is continuous exactly when the points
where it lies below a and where it lies above a form open sets, for
every a — the criterion the Urysohn function is checked against. A
uniform limit of continuous real functions is continuous, which is what
makes the sum of Tietze's series continuous. A function of two reals,
jointly continuous, carries two continuous real functions to a
continuous one, so their sum, difference and product are continuous, and
by induction so is a finite sum; the
negative of one is its product with −1; the absolute value of a
continuous real function is continuous, and so is its quotient by a
positive one, read through the rays (f/g lies below a exactly where
f − a·g is negative); and the distance from a fixed
point of a metric space is continuous; what composing with a continuous
function of the line gives is `continuous.Compose` after
`real_continuous`'s laws. On a nonempty compact set a continuous real
function attains a least value and a greatest one:
its values there form a compact, nonempty set of reals, which holds its
infimum and its supremum.

| member | statement |
|---|---|
| `ContinuousIntoRealIff` | `continuous_map(T, real_topology, f) ⇔ ∀a. {x \| x ∈ ⋃T ∧ f(x) < a} ∈ T ∧ {x \| x ∈ ⋃T ∧ a < f(x)} ∈ T` |
| `UniformLimitContinuous` | `is_topology(T) ∧ (∀n. continuous_map(T, real_topology, f(n))) ∧ (∀ε. &0 < ε ⇒ ∃N. ∀n. ∀x. N ≤ n ∧ x ∈ ⋃T ⇒ \|f(n)(x) - g(x)\| < ε) ⇒ continuous_map(T, real_topology, g)` |
| `ContinuousRealJoint` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ∧ continuous_map(T, real_topology, g) ∧ (∀a b ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀c d. \|c - a\| < δ ∧ \|d - b\| < δ ⇒ \|F(c, d) - F(a, b)\| < ε) ⇒ continuous_map(T, real_topology, λx. F(f(x), g(x)))` |
| `ContinuousRealAdd` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ∧ continuous_map(T, real_topology, g) ⇒ continuous_map(T, real_topology, λx. f(x) + g(x))` |
| `ContinuousRealSub` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ∧ continuous_map(T, real_topology, g) ⇒ continuous_map(T, real_topology, λx. f(x) - g(x))` |
| `ContinuousRealAbs` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ⇒ continuous_map(T, real_topology, λx. \|f(x)\|)` |
| `ContinuousRealDiv` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ∧ continuous_map(T, real_topology, g) ∧ (∀x. x ∈ ⋃T ⇒ &0 < g(x)) ⇒ continuous_map(T, real_topology, λx. f(x) / g(x))` |
| `ContinuousRealMul` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ∧ continuous_map(T, real_topology, g) ⇒ continuous_map(T, real_topology, λx. f(x) * g(x))` |
| `ContinuousRealSum` | `is_topology(T) ∧ (∀j. j < k ⇒ continuous_map(T, real_topology, F(j))) ⇒ continuous_map(T, real_topology, λx. Σ_{j<k} F(j, x))` |
| `ContinuousRealNeg` | `is_topology(T) ∧ continuous_map(T, real_topology, f) ⇒ continuous_map(T, real_topology, λx. -f(x))` |
| `MetricDistanceContinuous` | `metric_space(M, d) ∧ a ∈ M ⇒ continuous_map(metric_topology, real_topology, λx. d(a, x))` |
| `ContinuousCompactMinimum` | `continuous_map(T, real_topology, f) ∧ compact_in(T, K) ∧ K ≠ ∅ ⇒ ∃u. u ∈ K ∧ (∀v. v ∈ K ⇒ f(u) ≤ f(v))` |
| `ContinuousCompactMaximum` | `continuous_map(T, real_topology, f) ∧ compact_in(T, K) ∧ K ≠ ∅ ⇒ ∃u. u ∈ K ∧ (∀v. v ∈ K ⇒ f(v) ≤ f(u))` |
| `LocallyCompactUrysohn` | `is_topology(T) ∧ locally_compact_space(T) ∧ hausdorff(T) ∧ compact_in(T, k) ∧ w ∈ T ∧ k ⊆ w ⇒ ∃f l. continuous_map(T, real_topology, f) ∧ compact_in(T, l) ∧ l ⊆ w ∧ f ∈ ⟦0, 1⟧ on ⋃T, 1 on k, 0 off l` — card |

## Urysohn and Tietze (urysohn.go)

Urysohn's function is built from open sets V(n, k) indexed by the
dyadic rationals k/2ⁿ of ⟦0, 1⟧, each closure inside the next
(`UrysohnChain`): normality's shrinking step `separation.NormalShrink`
is chosen once as a function, the levels are built by recursion on n,
the even indices of level n + 1 repeat level n and each odd one is the
shrink of a closure inside the next set. Two sets of the chain are
compared across levels by lifting both to one level
(`UrysohnChainMonotone`). The function is the infimum of the dyadic
indices whose set holds the point, and it is continuous because the
points where it lies below or above a value form unions of those open
sets or of complements of their closures — the dyadics between two reals
of ⟦0, 1⟧ (`DyadicBetween`) supply the indices. Conversely the two halves of such a function's range
pull back to disjoint open sets, so normality is exactly the existence
of these functions. Tietze's extension is the sum of a series of
Urysohn functions, each a third of the remaining error, which converges
uniformly: one step (`TietzeStep`) rescales a Urysohn function for the
points where the residual is at least a third of its bound; the steps,
chosen once as a function of the residual and built by recursion
(`TietzeApproximation`), are dominated by the drops of c·(2/3)ⁿ, so
their partial sums converge uniformly to a continuous limit
(`TelescopingUniformLimit`). An unbounded function is squashed into
⟬−1, 1⟭ by $t \mapsto \frac{t}{1 + \lvert t \rvert}$ and extended; a Urysohn function that is 0
where the extension reaches ±1 and 1 on s pushes it off ±1, and
$y \mapsto \frac{y}{1 - \lvert y \rvert}$ unsquashes it. The topology of a distance is normal:
about each point of one closed set a ball misses the other, and the
balls of half those radii about the two sets do not meet.

| member | statement |
|---|---|
| `MetricNormal` | `normal_space(metric_topology)` |
| `DyadicBetween` | `&0 ≤ a ∧ a < b ∧ b ≤ &1 ⇒ ∃n k. k ≤ 2 ^ n ∧ a < &k / &2 ^ n ∧ &k / &2 ^ n < b` |
| `UrysohnChain` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ u ∈ T ∧ s ⊆ u ⇒ ∃V. (∀n k. k ≤ 2 ^ n ⇒ V(n, k) ∈ T ∧ s ⊆ V(n, k)) ∧ (∀n. V(n, 2 ^ n) = u) ∧ (∀n k. V(n + 1, 2 * k) = V(n, k)) ∧ (∀n k. k < 2 ^ n ⇒ closure(V(n, k)) ⊆ V(n, k + 1))` |
| `UrysohnChainMonotone` | `(∀p i. V(p + 1, 2 * i) = V(p, i)) ∧ (∀p i. i < 2 ^ p ⇒ closure(V(p, i)) ⊆ V(p, i + 1)) ∧ j ≤ 2 ^ m ∧ k * 2 ^ m < j * 2 ^ n ⇒ closure(V(n, k)) ⊆ V(m, j)` |
| `Urysohn` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ closed_in(t) ∧ s ∩ t = ∅ ⇒ ∃f. continuous_map(T, real_topology, f) ∧ (∀x. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ (∀x. x ∈ s ⇒ f(x) = &0) ∧ (∀x. x ∈ t ⇒ f(x) = &1)` |
| `UrysohnIff` | `normal_space(T) ⇔ ∀s t. closed_in(s) ∧ closed_in(t) ∧ s ∩ t = ∅ ⇒ ∃f. continuous_map(T, real_topology, f) ∧ (∀x. x ∈ ⋃T ⇒ &0 ≤ f(x) ∧ f(x) ≤ &1) ∧ (∀x. x ∈ s ⇒ f(x) = &0) ∧ (∀x. x ∈ t ⇒ f(x) = &1)` |
| `TietzeStep` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ &0 < c ∧ continuous_map(subtopology(s), real_topology, h) ∧ (∀x. x ∈ s ⇒ \|h(x)\| ≤ c) ⇒ ∃k. continuous_map(T, real_topology, k) ∧ (∀x. x ∈ ⋃T ⇒ \|k(x)\| ≤ c / &3) ∧ (∀x. x ∈ s ⇒ \|h(x) - k(x)\| ≤ &2 * c / &3)` |
| `TietzeApproximation` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ &0 < c ∧ continuous_map(subtopology(s), real_topology, f) ∧ (∀x. x ∈ s ⇒ \|f(x)\| ≤ c) ⇒ ∃G. (∀x. G(0)(x) = &0) ∧ (∀n. continuous_map(T, real_topology, G(n))) ∧ (∀n x. x ∈ ⋃T ⇒ \|G(n + 1)(x) - G(n)(x)\| ≤ c * (&2 / &3) ^ n / &3) ∧ (∀n x. x ∈ s ⇒ \|f(x) - G(n)(x)\| ≤ c * (&2 / &3) ^ n)` |
| `TelescopingUniformLimit` | `is_topology(T) ∧ (∀n. continuous_map(T, real_topology, G(n))) ∧ (∀n x. x ∈ ⋃T ⇒ \|G(n + 1)(x) - G(n)(x)\| ≤ e(n) - e(n + 1)) ∧ e ⟶ &0 ⇒ ∃g. continuous_map(T, real_topology, g) ∧ (∀x. x ∈ ⋃T ⇒ (λn. G(n)(x)) ⟶ g(x)) ∧ (∀n x. x ∈ ⋃T ⇒ \|G(n)(x) - g(x)\| ≤ e(n))` |
| `Tietze` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ a ≤ b ∧ continuous_map(subtopology(s), real_topology, f) ∧ (∀x. x ∈ s ⇒ a ≤ f(x) ∧ f(x) ≤ b) ⇒ ∃g. continuous_map(T, real_topology, g) ∧ (∀x. x ∈ ⋃T ⇒ a ≤ g(x) ∧ g(x) ≤ b) ∧ (∀x. x ∈ s ⇒ g(x) = f(x))` |
| `TietzeUnbounded` | `is_topology(T) ∧ normal_space(T) ∧ closed_in(s) ∧ continuous_map(subtopology(s), real_topology, f) ⇒ ∃g. continuous_map(T, real_topology, g) ∧ (∀x. x ∈ s ⇒ g(x) = f(x))` |

## Completely regular spaces (completely_regular.go)

A completely regular space is regular: the two halves of the separating
function's range pull back to disjoint open sets about the point and
around the closed set. A normal space whose points are closed is
completely regular, by Urysohn's lemma at the point and the closed set;
so the topology of a distance is. A subspace of a completely regular
space is completely regular, the separating function restricting to it.

| member | statement |
|---|---|
| `CompletelyRegularImpRegular` | `completely_regular_space(T) ⇒ regular_space(T)` |
| `NormalT1ImpCompletelyRegular` | `is_topology(T) ∧ normal_space(T) ∧ t1_space(T) ⇒ completely_regular_space(T)` |
| `CompletelyRegularSubtopology` | `completely_regular_space(T) ⇒ completely_regular_space(subtopology(T, s))` |
| `MetricCompletelyRegular` | `completely_regular_space(metric_topology)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
