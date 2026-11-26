# real_completeness — the completeness spur

The tower's crown: Dedekind completeness of the real numbers. This
family sits atop `real_construction/` (which delivers `real` as an ordered field
with `real_le`) and packages the last theorem the tower ships to
downstream analysis:

> `RealComplete`: every non-empty set of reals bounded above has a
> least upper bound.

Every member below is either a step on the chain that leads there, or
a tool used along the way.

## The chain

Completeness climbs the tower one representation at a time:

- **Archimedean, nadd side.** `Arch` — every Cauchy-slope is bounded
  above by some `nadd_of_num n`. The nadd layer's own upper-bound
  fact; the base of the completeness climb.
- **`ArchZero` → `ArchLemma`.** A slope whose natural multiples are
  all bounded by one fixed slope is equivalent to zero. `ArchLemma`
  uses this principle to remove fixed slack from comparisons of
  scaled slopes.
- **`NaddComplete`.** The full completeness of the slope
  representation — every non-empty bounded set of slopes has a
  least upper bound (up to `nadd_eq`). This is the analytic
  workhorse; the later completeness theorems transport this fact
  through the representation correspondences.
- **`HrealComplete`.** Transport across the `nadd_eq` quotient onto
  the nonnegative-real class layer, using `eudoxus_slope.NaddEqRefl/Sym/Trans`
  + `eudoxus_slope.LessEqWellDef` to lift the slope-side statement.
- **`RealHrealLemma1` / `RealHrealLemma2`.** The cross-representation
  bridges. LEMMA1 gives an order-faithful embedding of hreal whose
  image is exactly the nonnegative reals. LEMMA2 packages this
  correspondence as a single `∃h ∃r` over four
  laws — `h∘r = id` on hreal, `r∘h = id` on the nonnegative reals, `r`
  nonnegative-valued, `r` order-faithful — the shape the downstream
  completeness transport wants.
- **`RealCompleteSomePos`.** Completeness restricted to sets
  containing at least one NONNEGATIVE real — the specialization that
  the correspondence of LEMMA2 covers directly, since its embedding's
  image is exactly the nonnegative reals.
- **`RealComplete`.** The general theorem: reduce a set with any
  upper bound to a shifted set with a nonnegative element via a
  translation argument; cite `RealCompleteSomePos` on the shift.

## The Archimedean chain, in one paragraph

`NaddComplete` constructs an upper bound from a function of discrete
maxima: at each natural scale, take the greatest natural value
attainable below a scaled member of the set. Comparing these maxima
across scales proves that the function is a slope. Its defining
estimates make the represented slope an upper bound and place it
below every other upper bound; `ArchLemma` removes the fixed slack
in those comparisons. `HrealComplete` transports this construction
to the quotient, and `RealComplete` carries it to all reals.

## Members

| member | Statement (informal)                   |
|-------------------|----------------------------------------|
| `Arch`            | every slope is dominated by some `n`   |
| `ArchZero`        | uniformly bounded natural multiples force a slope to be zero |
| `ArchLemma`       | ε-of-your-choice refinement of Arch    |
| `NaddComplete`    | slope-side LUB — the analytic workhorse|
| `HrealComplete`   | LUB transported to the nonneg_real quotient |
| `RealHrealLemma1` | every real is a difference of nonneg reals |
| `RealHrealLemma2` | packaged ∃-form of the real↔hreal correspondence |
| `RealCompleteSomePos` | LUB for sets with a nonneg element |
| `RealComplete`    | **Dedekind completeness of ℝ**         |

## Where things live

- [family.go](family.go) — registry handle, `//go:embed real_completeness.cnf.pb`.
- **[complete.go](complete.go)** — the whole chain, one part per
  movement; each theorem registers its statement and proof through
  `family.Add` and exposes a typed wrapper.
- The completeness movement opens with the construction's
  **vocabulary**: text builders for the properties its section
  statements are composed from:
  `isNumericalMaxText` (`r_fn` picks the max of the set at every
  scale), `isTightBoundText`, `isSlopeEstimateText`, `destComputesText`,
  `isUpperBoundText`. The maximum itself is spelled by
  `attainableText`, `maximalText` and `isMaxAtText`, which
  `isNumericalMaxText` composes. `display.go` registers these properties
  so the section statements display their mathematical structure.
- [display.go](display.go) registers the same properties as DISPLAY
  abbreviations (ext/render.go): goals shown during
  construction and replay render `⟦isNumericalMax(P₀, r_fn₀)⟧`
  instead of the expanded formula. Display only — the ⟦⟧ marks a
  name that is NOT parseable syntax; terms, keys and recorded CNF
  trajectories are untouched, and each pattern is parsed from the
  builder it names, so the two cannot drift.

## Family posture

- **Cross-layer.** Members cite eudoxus_slope (bottom), nonneg_real (mid), nonneg_real_formal_diff
  (mid), axioms (top) — all four internal layers plus axioms. That
  depth is intentional; the whole tower funnels here.
