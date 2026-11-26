# real_integral — the Riemann integral on a closed interval

A function has integral I on ⟦a, b⟧ when its Riemann sums over tagged partitions tend to I as the partitions' mesh shrinks. The chapter builds the integral's algebra, shows that continuous and monotone functions are integrable, and bounded functions continuous off finitely many points, and connects the integral with the derivative through the two parts of the fundamental theorem of calculus. Differentiation under the integral sign asks of the integrand a first-order expansion in the parameter whose remainder is quadratic in the step, uniformly over the interval (`DerivativeUnderIntegral`). Three moving averages turn a bounded uniformly continuous function into one with three bounded derivatives, uniformly within ε of it (`UniformSmoothApproximation`).

## How the chapter is organized

**The relation is the object**, as in the derivative chapter:
`real_has_integral(f, a, b, I)` says that f has integral I on ⟦a, b⟧,
and every theorem names the integral it is about. A tagged partition
cuts ⟦a, b⟧ into n + 1 pieces p(k) ≤ p(k + 1), with a tag t(k) in each
piece; f has integral I when every partition whose pieces are all
shorter than some δ has its Riemann sum Σ f(t(k))·(p(k + 1) − p(k))
within ε of I. `a ≤ b` is part of the definition: a reversed interval
has no partition, so without the clause the condition would hold
vacuously and every number would be its integral. The value
`real_integral(f, a, b)` is for the theorems that need the integral as
a function of its bounds; it is oriented, ∫ from b to a being the
negative of ∫ from a to b.

**Partitions.** Fine partitions exist: a nondegenerate ⟦a, b⟧ is cut into
N + 1 equal pieces, N from Archimedes (`UniformFinePartition`), and a
point is one piece of length 0. An interval over which f has an
integral is ordered (`HasIntegralOrdered`). Two integrals over one interval share a mesh
(`CommonMesh`), and that one fact gives uniqueness, the sum and the
order of integrals. The value reads the integral off by uniqueness.
Every tag lies in ⟦a, b⟧, which is what lets a pointwise inequality on
⟦a, b⟧ compare two Riemann sums.

**The algebra.** A constant's Riemann sum telescopes to c·(b − a). The
sum, the scalar multiple, the negative (the multiple by −1) and the
difference (the sum with the negative) carry over from the sums, and a finite sum is integrated term by
term (`HasIntegralSum`); the
integral respects the order, and |f| ≤ M bounds the integral by
M·(b − a).

**Comparing partitions.** Two partitions of one interval are compared
without a common refinement. The overlaps of an interval with the pieces
of a partition add up to its length: the overlap is the rise of a clamp
across the piece, so the overlaps telescope (`PartitionOverlapSum`). A
sum over the pieces of p and one over the pieces of q are therefore one
double sum over pairs of pieces weighted by their overlaps, which
compares termwise (`PartitionSumsCompare`, `PartitionSumsClose`); on one
partition, two functions within η of each other have sums within
η·(b − a) (`RiemannSumsClose`). The
Cauchy criterion (`IntegrableCauchy`) chooses sums on finer and finer
partitions and takes their limit; the comparison is what checks the
criterion, for the integrability of continuous functions (uniform continuity bounds the
termwise differences) and of monotone ones (the left- and right-end
sums bracket every Riemann sum and differ by at most δ·(f(b) − f(a))).
Additivity clamps a partition of ⟦a, b⟧ to ⟦a, c⟧ and to ⟦c, b⟧; the
error from splitting the one piece that straddles c is at most 4Mδ, M
bounding f (`IntegrableBounded`). Partitions of adjacent intervals, run one
after the other, are a partition of their union whose Riemann sum is the
sum of theirs (`PartitionJoin`); joined on both sides to fixed fine
partitions of ⟦a, c⟧ and ⟦d, b⟧, two partitions of ⟦c, d⟧ carry the
Cauchy criterion from ⟦a, b⟧ down to ⟦c, d⟧ (`IntegrableSubinterval`).

**Integrability up to finitely many points.** Two
functions that agree on ⟦a, b⟧ have the same integrals
(`HasIntegralCongruence`), so two that agree between a and b, whichever
way round, have the same oriented integral from a to b
(`IntegralCongruence`); two that agree on ⟦c, d⟧ ⊆ ⟦a, b⟧ and differ
by at most M have Riemann sums within M·((c − a) + (b − d) + 2δ) on a
partition finer than δ (`RiemannSumsAgreeInside`). So a bounded function
with an integral on every closed interval inside ⟬a, b⟭ has one on
⟦a, b⟧ (`IntegrableFromInterior`): frozen at its values at a + η and
b − η outside them it has an integral, and its sums differ from f's only
on the end strips. A bounded function continuous off finitely many
points has an integral (`IntegrableOffFinite`), by induction on the
exceptional set, splitting at an exceptional point inside.

**The fundamental theorem.** If F is continuous on ⟦a, b⟧ with
derivative f strictly inside, any integral f has over ⟦a, b⟧ is
F(b) − F(a) (`NewtonLeibniz`). The mean value theorem tags each piece of
a fine partition at a point where f times the piece's length is F's
increment across it, and at those tags the Riemann sum telescopes to
F(b) − F(a). The theorem asks nothing of f beyond having an integral:
the hypothesis supplies I, and the theorem identifies it. Finitely many
points where F has no derivative f change nothing
(`NewtonLeibnizOffFinite`): by induction on them, splitting the
interval at one inside. A continuous f with antiderivative F
has integral F(b) − F(a) (`NewtonLeibnizContinuous`). Integration by
parts is Newton–Leibniz applied to f·g. The integral of a continuous f,
read as a function of its upper bound, has derivative f inside the
interval (`IntegralDerivative`): near x the integral over a short span
is f(x) times the span's length up to ε/2 times that length
(`HasIntegralNearConstant`), and additivity turns the increment into
that span. Substitution is Newton–Leibniz applied to the composite of
that antiderivative with g; g is taken strictly inside ⟬l, r⟭, so the
antiderivative has a derivative wherever the chain rule meets it.

In the table «partition»(a, b, n, p), «finePartition»(a, b, δ, n, p, t),
«riemannSum»(f, n, p, t) and «sumsWithin»(f, a, b, δ, ε) are the
chapter's abbreviations (family.go).

## Members

| entry | statement |
|---|---|
| `RealHasIntegralDef` | `real_has_integral(f, a, b, I) ⇔ a ≤ b ∧ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ ∀n p t. p(0) = a ∧ p(n + 1) = b ∧ (∀k. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1) ∧ p(k + 1) − p(k) < δ) ⇒ real_abs(Σ_{k∈0 .. n} f(t(k)) · (p(k + 1) − p(k)) − I) < ε` |
| `RealIntegralDef` | `real_integral(f, a, b) = if a ≤ b then (εI. real_has_integral(f, a, b, I)) else −(εI. real_has_integral(f, b, a, I))` |
| `UniformFinePartition` | `a < b ∧ &0 < δ ⇒ ∃n p h. &0 < h ∧ «finePartition»(a, b, δ, n, p, p) ∧ ∀i. i ≤ n ⇒ p(i + 1) − p(i) = h` |
| `FinePartitionExists` | `a ≤ b ∧ &0 < δ ⇒ ∃n p t. «finePartition»(a, b, δ, n, p, t)` |
| `FinePartitionMono` | `«finePartition»(a, b, δ₁, n, p, t) ∧ δ₁ ≤ δ₂ ⇒ «finePartition»(a, b, δ₂, n, p, t)` |
| `FinePartitionIsPartition` | `«finePartition»(a, b, δ, n, p, t) ⇒ «partition»(a, b, n, p)` |
| `PartitionPiecesInInterval` | `«partition»(a, b, n, p) ∧ k ≤ n ⇒ a ≤ p(k) ∧ p(k) ≤ p(k + 1) ∧ p(k + 1) ≤ b` |
| `PartitionTagsInInterval` | `p(0) = a ∧ p(n + 1) = b ∧ (∀j. j ≤ n ⇒ p(j) ≤ t(j) ∧ t(j) ≤ p(j + 1)) ∧ k ≤ n ⇒ a ≤ t(k) ∧ t(k) ≤ b` |
| `PartitionPieceContains` | `p(0) ≤ x ∧ x ≤ p(n + 1) ⇒ ∃k. k ≤ n ∧ p(k) ≤ x ∧ x ≤ p(k + 1)` |
| `RiemannSumRetag` | `k ≤ n ⇒ «riemannSum»(f, n, p, λi. if i = k then x else t(i)) = «riemannSum»(f, n, p, t) + (f(x) − f(t(k))) · (p(k + 1) − p(k))` |
| `HasIntegralOrdered` | `real_has_integral(f, a, b, I) ⇒ a ≤ b` |
| `CommonMesh` | `real_has_integral(f, a, b, I) ∧ real_has_integral(g, a, b, J) ∧ &0 < ε ⇒ ∃δ. &0 < δ ∧` every partition of ⟦a, b⟧ finer than δ brings both Riemann sums within ε of I and of J |
| `HasIntegralUnique` | `real_has_integral(f, a, b, I) ∧ real_has_integral(f, a, b, J) ⇒ I = J` |
| `HasIntegralValue` | `real_has_integral(f, a, b, I) ⇒ real_integral(f, a, b) = I` |
| `HasIntegralConst` | `a ≤ b ⇒ real_has_integral(λx. c, a, b, c · (b − a))` |
| `HasIntegralAdd` | `real_has_integral(f, a, b, I) ∧ real_has_integral(g, a, b, J) ⇒ real_has_integral(λx. f(x) + g(x), a, b, I + J)` |
| `HasIntegralSum` | `(∀k. k ≤ n ⇒ real_has_integral(u(k), a, b, c(k))) ⇒ real_has_integral(λx. Σ_{k∈0 .. n} u(k)(x), a, b, Σ_{k∈0 .. n} c(k))` |
| `HasIntegralScale` | `real_has_integral(f, a, b, I) ⇒ real_has_integral(λx. c · f(x), a, b, c · I)` |
| `RiemannIntegralScale` | `real_has_integral(f, a, b, I) ⇒ real_integral(λx. c * f(x), a, b) = c * real_integral(f, a, b)` |
| `HasIntegralNeg` | `real_has_integral(f, a, b, I) ⇒ real_has_integral(λx. −f(x), a, b, −I)` |
| `HasIntegralSub` | `real_has_integral(f, a, b, I) ∧ real_has_integral(g, a, b, J) ⇒ real_has_integral(λx. f(x) − g(x), a, b, I − J)` |
| `HasIntegralLessEq` | `(∀x. a ≤ x ∧ x ≤ b ⇒ f(x) ≤ g(x)) ∧ real_has_integral(f, a, b, I) ∧ real_has_integral(g, a, b, J) ⇒ I ≤ J` |
| `RiemannIntegralNonneg` | `real_has_integral(f, a, b, I) ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ &0 ≤ f(x)) ⇒ &0 ≤ real_integral(f, a, b)` |
| `HasIntegralBound` | `(∀x. a ≤ x ∧ x ≤ b ⇒ real_abs(f(x)) ≤ M) ∧ real_has_integral(f, a, b, I) ⇒ real_abs(I) ≤ M · (b − a)` |
| `HasIntegralNearConstant` | `(∀x. a ≤ x ∧ x ≤ b ⇒ real_abs(f(x) − c) ≤ M) ∧ real_has_integral(f, a, b, I) ⇒ real_abs(I − c · (b − a)) ≤ M · (b − a)` |
| `PartitionOverlapSum` | `«partition»(a, b, m, q) ∧ a ≤ u ∧ u ≤ v ∧ v ≤ b ⇒ Σ_{j∈0 .. m} max(&0, min(v, q(j + 1)) − max(u, q(j))) = v − u` |
| `PartitionSumsCompare` | two partitions of ⟦a, b⟧, g(k) ≤ h(j) wherever piece k of p meets piece j of q ⇒ `Σ_k g(k) · (p(k + 1) − p(k)) ≤ Σ_j h(j) · (q(j + 1) − q(j))` |
| `PartitionSumsClose` | the same with `real_abs(g(k) − h(j)) ≤ η` on overlaps ⇒ the two sums differ by at most `η · (b − a)` |
| `RiemannSumsClose` | `(∀x. a ≤ x ∧ x ≤ b ⇒ real_abs(f(x) − g(x)) ≤ η) ∧ p(0) = a ∧ p(n + 1) = b ∧ (∀k. k ≤ n ⇒ p(k) ≤ t(k) ∧ t(k) ≤ p(k + 1)) ⇒ real_abs(Σ_{k∈0 .. n} f(t(k)) · (p(k + 1) − p(k)) − Σ_{k∈0 .. n} g(t(k)) · (p(k + 1) − p(k))) ≤ η · (b − a)` |
| `HasIntegralCongruence` | `(∀x. a ≤ x ∧ x ≤ b ⇒ f(x) = g(x)) ∧ real_has_integral(f, a, b, I) ⇒ real_has_integral(g, a, b, I)` |
| `IntegralCongruence` | `(∀x. min(a, b) ≤ x ∧ x ≤ max(a, b) ⇒ f(x) = g(x)) ⇒ real_integral(f, a, b) = real_integral(g, a, b)` |
| `RiemannSumsAgreeInside` | `(∀x. a ≤ x ∧ x ≤ b ⇒ real_abs(f(x) − g(x)) ≤ M) ∧ (∀x. c ≤ x ∧ x ≤ d ⇒ f(x) = g(x)) ∧ a ≤ c ∧ c ≤ d ∧ d ≤ b ∧ «finePartition»(a, b, δ, n, p, t) ⇒ real_abs(«riemannSum»(f, n, p, t) − «riemannSum»(g, n, p, t)) ≤ M · ((c − a) + (b − d) + 2 · δ)` |
| `PartitionJoin` | `«finePartition»(a, c, δ, n₁, p₁, t₁) ∧ «finePartition»(c, b, δ, n₂, p₂, t₂) ⇒ ∃n p t. «finePartition»(a, b, δ, n, p, t) ∧ «riemannSum»(f, n, p, t) = «riemannSum»(f, n₁, p₁, t₁) + «riemannSum»(f, n₂, p₂, t₂)` |
| `IntegrableBounded` | `real_has_integral(f, a, b, I) ⇒ ∃B. ∀x. a ≤ x ∧ x ≤ b ⇒ real_abs(f(x)) ≤ B` |
| `IntegrableCauchy` | `(∃I. real_has_integral(f, a, b, I)) ⇔ a ≤ b ∧ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ «sumsWithin»(f, a, b, δ, ε)` |
| `ContinuousIntegrable` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ ∃I. real_has_integral(f, a, b, I)` |
| `ContinuousHasIntegral` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ⇒ real_has_integral(f, a, b, real_integral(f, a, b))` |
| `IncreasingSumBracket` | `real_increasing_on(⟦a, b⟧, f)`, a partition finer than δ ⇒ the sum tagged at left ends ≤ `«riemannSum»(f, n, p, t)` ≤ the sum tagged at right ends, which differ by at most `δ · (f(b) − f(a))` |
| `IncreasingIntegrable` | `a ≤ b ∧ real_increasing_on(⟦a, b⟧, f) ⇒ ∃I. real_has_integral(f, a, b, I)` |
| `DecreasingIntegrable` | `a ≤ b ∧ real_decreasing_on(⟦a, b⟧, f) ⇒ ∃I. real_has_integral(f, a, b, I)` |
| `IntegrableFromInterior` | `a ≤ b ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ real_abs(f(t)) ≤ B) ∧ (∀c d. a < c ∧ c ≤ d ∧ d < b ⇒ ∃I. real_has_integral(f, c, d, I)) ⇒ ∃I. real_has_integral(f, a, b, I)` |
| `IntegrableOffFinite` | `a ≤ b ∧ finite(k) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ real_abs(f(t)) ≤ B) ∧ real_continuous_on(⟦a, b⟧ ∖ k, f) ⇒ ∃I. real_has_integral(f, a, b, I)` |
| `HasIntegralSplit` | `a ≤ c ∧ c ≤ b ∧ real_has_integral(f, a, c, I) ∧ real_has_integral(f, c, b, J) ⇒ real_has_integral(f, a, b, I + J)` |
| `IntegrableSubinterval` | `real_has_integral(f, a, b, I) ∧ a ≤ c ∧ c ≤ d ∧ d ≤ b ⇒ ∃J. real_has_integral(f, c, d, J)` |
| `IntegralAdditiveOrdered` | `a ≤ b ∧ b ≤ c ∧ real_has_integral(f, a, b, I) ∧ real_has_integral(f, b, c, J) ⇒ real_integral(f, a, b) + real_integral(f, b, c) = real_integral(f, a, c)` |
| `IntegralReverse` | `real_has_integral(f, a, b, I) ⇒ real_integral(f, b, a) = −real_integral(f, a, b)` |
| `IntegralAdditive` | `real_continuous_on(⟦l, r⟧, f)` ∧ a, b, c in ⟦l, r⟧ `⇒ real_integral(f, a, b) + real_integral(f, b, c) = real_integral(f, a, c)` |
| `NonnegIntegralZeroVanishes` | `a < b ∧ real_continuous_on(⟦a, b⟧, f) ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ &0 ≤ f(t)) ∧ real_integral(f, a, b) = &0 ∧ a ≤ x ∧ x ≤ b ⇒ f(x) = &0` — were f(x) > 0, continuity would keep f above f(x)/2 on a stretch of positive length about x, and the integral, split there, would be positive |
| `NewtonLeibniz` | `real_continuous_on(⟦a, b⟧, F) ∧ (∀x. a < x ∧ x < b ⇒ real_derivative_at(F, x, f(x))) ∧ real_has_integral(f, a, b, I) ⇒ I = F(b) − F(a)` |
| `NewtonLeibnizOffFinite` | `finite(k) ∧ real_continuous_on(⟦a, b⟧, F) ∧ (∀t. a < t ∧ t < b ∧ t ∉ k ⇒ real_derivative_at(F, t, f(t))) ∧ real_has_integral(f, a, b, I) ⇒ I = F(b) − F(a)` |
| `NewtonLeibnizContinuous` | `a ≤ b ∧ real_continuous_on(⟦a, b⟧, f) ∧ real_continuous_on(⟦a, b⟧, F) ∧ (∀x. a < x ∧ x < b ⇒ real_derivative_at(F, x, f(x))) ⇒ real_has_integral(f, a, b, F(b) − F(a))` |
| `IntegrationByParts` | `a ≤ b ∧ (∀x. a ≤ x ∧ x ≤ b ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x))) ∧ real_continuous_on(⟦a, b⟧, f') ∧ real_continuous_on(⟦a, b⟧, g') ⇒ real_integral(λx. f(x) · g'(x), a, b) = f(b) · g(b) − f(a) · g(a) − real_integral(λx. f'(x) · g(x), a, b)` |
| `IntegralDerivative` | `real_continuous_on(⟦a, b⟧, f) ∧ a < x ∧ x < b ⇒ real_derivative_at(λy. real_integral(f, a, y), x, f(x))` |
| `IntegralContinuousOn` | `real_continuous_on(⟦a, b⟧, f) ∧ a ≤ c ∧ c ≤ b ⇒ real_continuous_on(⟦a, b⟧, λy. real_integral(f, c, y))` |
| `IntegralAffineSubstitution` | `real_continuous_on(⟦l, r⟧, f) ∧ l ≤ β ∧ β ≤ r ∧ l ≤ β + α ∧ β + α ≤ r ⇒ real_integral(λt. f(β + α * t) * α, &0, &1) = real_integral(f, β, β + α)` |
| `RiemannIntegralAffineChange` | `real_continuous_on(⟦c, d⟧, f) ∧ l ≤ u ∧ c ≤ p + q * l ∧ p + q * l ≤ d ∧ c ≤ p + q * u ∧ p + q * u ≤ d ⇒ real_integral(λy. f(p + q * y) * q, l, u) = real_integral(f, p + q * l, p + q * u)`, q of either sign |
| `IntegralSubstitution` | `a ≤ b ∧ (∀t. a ≤ t ∧ t ≤ b ⇒ real_derivative_at(g, t, g'(t)) ∧ l < g(t) ∧ g(t) < r) ∧ real_continuous_on(⟦a, b⟧, g') ∧ real_continuous_on(⟦l, r⟧, f) ⇒ real_integral(λt. f(g(t)) · g'(t), a, b) = real_integral(f, g(a), g(b))` |
| `DerivativeUnderIntegral` | `&0 < d ∧ (∀s. \|s - t\| < d ⇒ real_has_integral(F(s), a, b, real_integral(F(s), a, b))) ∧ real_has_integral(G(t), a, b, real_integral(G(t), a, b)) ∧ (∀h x. \|h\| < d ∧ a ≤ x ∧ x ≤ b ⇒ \|F(t + h, x) - F(t, x) - G(t, x) * h\| ≤ K * h ^ 2) ⇒ real_derivative_at(λs. real_integral(F(s), a, b), t, real_integral(G(t), a, b))` |
| `UniformSmoothApproximation` | `real_uniformly_continuous_on(𝕌, f)`, f bounded and `&0 < ε` ⇒ some D(0) with derivatives D(1), D(2), D(3), the four bounded together, lies within ε of f everywhere |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
