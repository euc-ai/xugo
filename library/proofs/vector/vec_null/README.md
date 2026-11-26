# vec_null — null sets in Euclidean space by countable cube covers

A subset of ℝⁿ is null when it has countable open cube covers of
arbitrarily small total n-volume. The volume series uses `real_sums`;
no measure or integration of characteristic functions is involved.
Every set is constrained to the zero-padded n-vector carrier.

In positive dimension cube j has centre c(j), radius r(j) ≥ 0 and
strict coordinate inequalities |x(i) − c(j)(i)| < r(j) for i < n.
A radius-zero cube is empty and contributes zero to the sum, so empty
and finite covers are sequences too. In dimension zero only the
empty set is null; the singleton ℝ⁰ has volume one.

## The null ideal

Subsets and countable unions preserve nullity. A bounded coordinate
subspace can be covered with cubes whose total volume tends to zero
when its dimension is smaller than the ambient dimension. A nonempty
open set, on the other hand, contains a closed cube of positive side
length; compactness and the finite covering volume inequality prevent
its volume from being arbitrarily small.

| member | statement |
|---|---|
| `NullSetDef` | `vec_null_set⟨n⟩(S)`: countable cube covers of arbitrarily small total volume, with only the empty set null at n = 0 |
| `NullEmpty` | the empty set is null in every dimension — card |
| `NullZeroDimension` | `vec_null_set⟨0⟩(S) ⇔ S = ∅` — card |
| `NullSubset` | `S ⊆ T ∧ vec_null_set⟨n⟩(T) ⇒ vec_null_set⟨n⟩(S)` — card |
| `NullCountableUnion` | the union of a countable family of null sets is null — card |
| `NullCoordinateSubspace` | `a < b ⇒ vec_null_set⟨b⟩({x \| vec⟨a⟩(x)})` — card |
| `OpenNonemptyNotNull` | a nonempty open subset of positive-dimensional ℝⁿ is not null — card |

## Images

A locally Lipschitz map preserves null sets in equal dimensions.
The hypotheses use `lipschitz_map` on an open neighbourhood of every
point; this includes the requirement that the image lies in the target
carrier. A covering cube need not stay inside such a neighbourhood:
choose a point of its intersection with the set and centre the image
cube there. A countable neighbourhood cover reduces the local result
to the countable-union law.

For a map from ℝᵃ to ℝᵇ with a < b, extend it to an open cylinder by
ignoring the last b − a coordinates. Its original domain is null in
ℝᵇ, so the same-dimensional result gives null image. This result is
independent of Sard and serves Euclidean projection arguments for
immersions and embeddings.

| member | statement |
|---|---|
| `LocallyLipschitzPreservesNull` | a locally Lipschitz map on an open subset of ℝⁿ carries every null subset to a null set — card |
| `LowerDimensionalImageNull` | a locally Lipschitz map on an open subset of ℝᵃ has null image in ℝᵇ when a < b — card |

## Compact slices

The slice of K ⊆ ℝⁿ⁺¹ at last coordinate t is represented by
`{x | vec⟨n⟩(x) ∧ (λi. COND(i = n, t, x(i))) ∈ K}`. Compactness
makes a small finite cover of one slice cover all nearby slices.
A finite subdivision in t then controls the full volume. This is a
compact-set theorem; it makes no claim about arbitrary sets with
null slices.

| member | statement |
|---|---|
| `CompactNullSlices` | for n > 0, a compact K ⊆ ℝⁿ⁺¹ whose every n-dimensional slice is null is null — card |

The cards are statements awaiting proofs; their notes describe the
arguments and their dependencies expose the remaining card frontier.
