# biaffine_scheme — the scheme a biaffine datum glues from the spectra of its two charts

A biaffine datum (`scheme/lattice_pair`) holds a curve by the coordinate
rings A₀ and A₁ of two affine charts inside the ring R of their overlap,
R = A₀[1/t] = A₁[1/s] with t · s = one. This chapter builds the scheme
those rings describe — Spec A₀ and Spec A₁ glued along Spec R, which is
the basic open set D(t) of the first and D(s) of the second — and shows
that it is a scheme, so that what the lattice-pair chapters say with
modules over the two charts is said about this scheme. Nothing in the
curve chapters stands on it; it is the bridge between the two-chart
picture and the sheaf-theoretic one.

A point is held by its ideal in each chart: a prime of the chart ring, or
the chart ring itself where the point lies off that chart, the two
generating one ideal of R, a proper one when the point lies on both
charts. Over each prime of a chart ring lies exactly one point — a prime
of A₀ holding t is paired with A₁, one missing t with the trace on A₁ of
the prime it generates in R — so the projection to either ideal is
one-to-one on its chart. A k-rational point of the datum is held by the
same pair of ideals, and is a closed point. A set of points is open when
its part on each chart, read through the projection as a set of primes,
is Zariski open; each chart is then open and homeomorphic to the
spectrum of its ring, and the points on both charts are D(t) on one and
D(s) on the other.

A section over an open set U is a pair: a section of the structure sheaf
of A₀ over the part of U on chart 0, and one of A₁ over the part on
chart 1, whose fractions agree at each point of U on both charts once
read in R localized at the prime the point generates. Restriction and
the ring operations act chart by chart. Over an open set inside one
chart the other component is fixed by that agreement, so the sections
are the chart's structure sections; the global sections are A₀ ∩ A₁, both
chart rings lying in R; the stalks are the local rings of the charts; and
each chart with the sheaf on it is the spectrum of its ring, which makes
the glued space a scheme. The projective line inside a field, k[t] and
k[1/t] glued along k[t, 1/t], is one.

Points are pairs of ideals and sections pairs of structure sections, both
of types built from the ring's carrier type, so no type is minted and
nothing is transported. The topology, record-valued section family and
restriction are named together as `biaffine_sheaf(R, A₀, A₁)`. The ring
records of sections over U and germs at P are
`biaffine_section_ops(R, A₀, A₁, U)` and
`biaffine_stalk_ops(R, A₀, A₁, P)`.

## Members

### The definitions

| Member | Statement |
|---|---|
| `biaffinePointsDef` | `biaffine_points(R, A₀, A₁)`: pairs of chart ideals, each a prime or its chart ring, not both the rings, generating one ideal of R, a proper one on both charts |
| `biaffineTraceDef` | `biaffine_trace(S, projection, U)`: the ideals other than S that the points of U project to |
| `biaffineTopologyDef` | `biaffine_topology(R, A₀, A₁)`: the sets of points whose traces on both charts are Zariski open |
| `biaffineSectionsDef` | `biaffine_sections(R, A₀, A₁, U)`: pairs of structure sections over the two traces of U, agreeing in R localized at each point on both charts |
| `biaffineRestrictDef` | `biaffine_restrict(A₀, A₁, U, V, σ)`: each component restricted to the trace of V |
| `biaffineAddDef` | `biaffine_add(R, A₀, A₁, U, σ, τ)`: the sum, chart by chart |
| `biaffineZeroDef` | `biaffine_zero(R, A₀, A₁, U)`: the zero section, chart by chart |
| `biaffineNegDef` | `biaffine_neg(R, A₀, A₁, U, σ)`: the negation, chart by chart |
| `biaffineMulDef` | `biaffine_mul(R, A₀, A₁, U, σ, τ)`: the product, chart by chart |
| `biaffineOneDef` | `biaffine_one(R, A₀, A₁, U)`: the one section, chart by chart |
| `biaffineSubDef` | `biaffine_sub(R, A₀, A₁, U, σ, τ)`: the difference, chart by chart |

### The points and the topology

| Member | Statement |
|---|---|
| `BiaffinePointOverPrime` | over each prime of a chart ring lies exactly one point — card |
| `BiaffineOverlapPrime` | a point on both charts generates a prime of R, misses t and s, and each chart ideal is that prime met with its chart ring — card |
| `BiaffineIsTopology` | the sets of points open on both charts form a topology — card |
| `BiaffineSpace` | the topology's points are the points, which trace the whole spectrum of each chart ring — card |
| `BiaffineChartOpen` | each chart is open, its projection a homeomorphism onto the spectrum of its ring — card |
| `BiaffineOverlapBasicOpen` | the points on both charts form an open set, D(t) on chart 0 and D(s) on chart 1 — card |
| `RationalPointIsClosedPoint` | a rational point over a subfield inside both charts is a closed point — card |

### The sheaf and the scheme

| Member | Statement |
|---|---|
| `BiaffineSheafPresheaf` | the pairs of chart sections, restricted chart by chart, form a presheaf — card |
| `BiaffineSheafIsSheaf` | the presheaf is a sheaf — card |
| `BiaffineSheafOfRings` | with the chartwise operations it is a sheaf of rings — card |
| `BiaffineChartSections` | over an open set inside a chart, the projection is a ring isomorphism onto the chart's structure sections — card |
| `BiaffineGlobalSections` | the global sections are A₀ ∩ A₁, through a ↦ (a / one, a / one) — card |
| `BiaffineStalkLocal` | the ring of germs at each point is local — card |
| `BiaffineLocallyRinged` | the glued space with its sheaf is a locally ringed space — card |
| `BiaffineChartIsSpec` | each chart with the sheaf on it is isomorphic to the spectrum of its ring — card |
| `BiaffineScheme` | the glued space with its sheaf is a scheme — card |
| `ProjectiveLineScheme` | k[t] and k[1/t] inside a field, t ≠ zero, glue to a scheme — card |
