# lattice_pair — modules over the two charts of a biaffine datum glued on the overlap, and their two-term Čech cohomology

A curve covered by two affine charts is held here without sheaves. A
biaffine datum is a ring R with two subrings A₀ and A₁ and an element t
of A₀ whose inverse s lies in A₁, with R equal to A₀[1/t] and to A₁[1/s]:
the coordinate rings of the two charts and of their overlap. A module on
the curve is then a lattice pair: a module V over R and a pair
M = (M₀, M₁), M₀ an A₀-submodule and M₁ an A₁-submodule of V, which span
the same R-submodule of V — the module of sections over the overlap.
The cover has two charts, so the Čech complex has two terms and the
cohomology is read off directly: H⁰(M) = M₀ ∩ M₁, and H¹(M) is the
overlap's sections modulo M₀ + M₁.

V is a container, not the overlap's sections: a lattice pair inside a
field takes V to be the field, and the pairs built from functions — the
dualizing pair, the derivation pair — take V to be a module of
functions. Over a subfield k of R the dimensions of H⁰ and H¹ and the
Euler characteristic χ(M) = dim H⁰(M) − dim H¹(M) are defined; they
determine numbers only where both cohomology modules are finite over k,
which the statements take as a hypothesis.

What is built on lattice pairs is in the chapters after this one: the
rational points of the datum (scheme/biaffine_rational_point), the
six-term sequence of a sub-pair and the Euler characteristic it counts
(scheme/lattice_pair_sequence), maps and isomorphisms of lattice pairs
(scheme/lattice_pair_map), lattice pairs inside a field and the
invertible ones (scheme/invertible_lattice_pair), and twisting at a point
(scheme/lattice_pair_twist).

## Members

### The definitions

| Member | Statement |
|---|---|
| `BiaffineDef` | `biaffine(R, A₀, A₁, t, s)`: two subrings of R, t ∈ A₀ and s ∈ A₁ inverse to each other, R = A₀[1/t] = A₁[1/s] |
| `LatticePairDef` | `lattice_pair(R, A₀, A₁, V, M)`: an A₀-submodule and an A₁-submodule of the R-module V spanning the same R-submodule |
| `LatticePairAmbientDef` | `lattice_pair_ambient(R, V, M)`: the R-submodule spanned by fst(M) |
| `LatticePairH0Def` | `lattice_pair_h0(V, M)`: H⁰(M) = fst(M) ∩ snd(M) |
| `LatticePairH1Def` | `lattice_pair_h1(R, V, M)`: H¹(M), the ambient modulo fst(M) + snd(M) |
| `LatticePairDifferenceDef` | `lattice_pair_difference(V, z)`: the Čech difference m₀ − m₁ |
| `LatticePairH0DimDef` | `lattice_pair_h0_dim(R, k, V, M)`: dim_k H⁰(M) |
| `LatticePairH1DimDef` | `lattice_pair_h1_dim(R, k, V, M)`: dim_k H¹(M) |
| `LatticePairFiniteDef` | `lattice_pair_finite(R, k, V, M)`: H⁰(M) and H¹(M) are finite-dimensional over k |
| `LatticePairEulerDef` | `lattice_pair_euler(R, k, V, M)`: χ(M) = dim H⁰(M) − dim H¹(M) |

### The datum

| Member | Statement |
|---|---|
| `BiaffineSwap` | the datum read with its charts exchanged is a datum |
| `BiaffineChartLocalization` | each chart's inclusion into the overlap is the localization at the powers of its element |
| `ChartSubsetInOverlap` | a set lying in chart 0 lies in the overlap R |
| `ChartFieldSubring` | a field k under R's operations lying in chart 0 is a subring of R |
| `StructurePairLattice` | (A₀, A₁) is a lattice pair in R over itself, with ambient R |

### The ambient

| Member | Statement |
|---|---|
| `AmbientContains` | the ambient is an R-submodule of V holding both charts |
| `ChartSpanAway` | the R-span of an A₀-submodule M₀ of V is the set of v ∈ V with tⁿ · v ∈ M₀ for some n |
| `ChartSpanInter` | over a biaffine datum, the R-span of the meet of two A₀-submodules of V is the meet of their spans |
| `AmbientOfIntersection` | the chartwise meet of two lattice pairs is a lattice pair whose ambient is the meet of their ambients |
| `LatticePairByPowers` | two chart submodules form a lattice pair exactly when powers of t bring chart 1 into chart 0 and powers of s chart 0 into chart 1 — card |

### Localizing a chart quotient

| Member | Statement |
|---|---|
| `StableImageSurjectsOnLocalization` | with M₀/N₀ finite over k, every v ∈ M₀ has w ∈ M₀ and j with tʲ · (v − tⁿ · w) ∈ N₀ |
| `QuotientLocalizes` | with M₀/N₀ finite over k, span_R(M₀) = M₀ + span_R(N₀) |
| `QuotientDimLocalizes` | with M₀/N₀ finite over k, span_R(M₀)/span_R(N₀) is finite of dimension at most dim M₀/N₀ |
| `ContractedQuotientDimLocalizes` | A chart quotient whose smaller module is contracted from its span keeps its dimension on the overlap |

### The two-term Čech complex

| Member | Statement |
|---|---|
| `H0IsIntersection` | the kernel of the Čech difference on M₀ × M₁ is the diagonal of H⁰(M) — card |
| `H1IsCokernel` | the image of the Čech difference is M₀ + M₁, inside the ambient — card |
| `RestrictedPairCohomology` | The cohomology of a pair inside a subset of a ring, read in the ring's regular module |

### The chart sum, sub-pairs and smaller scalars

| Member | Statement |
|---|---|
| `ChartSumInAmbient` | M₀ + M₁ lies in the ambient and holds zero |
| `SubpairInclusions` | for M' ⊆ M chart by chart, ambient(M') ⊆ ambient(M) and M'₀ + M'₁ ⊆ M₀ + M₁ |
| `PairModuleOn` | the V of a lattice pair is a module over its ring R |
| `PairOverSubring` | over any subring S of both charts, V is an S-module and M₀, M₁, M₀ + M₁ and the ambient are S-submodules of it |
| `H1OverSubring` | over any subring S of both charts, the ambient is an S-module with M₀ + M₁ an S-submodule, H¹(M) is an S-module and the class map onto it is S-linear |
| `H0Submodule` | H⁰ of a lattice pair is a submodule over any scalars lying in both charts |

### Direct sums

| Member | Statement |
|---|---|
| `DirectSumH0` | for a direct sum M of lattice pairs M₁, M₂ (charts the sums, ambients meeting only in zero) over a field k in both charts, H⁰(M) is finite when H⁰(M₁), H⁰(M₂) are, and h⁰(M) = h⁰(M₁) + h⁰(M₂) |
| `DirectSumH1` | likewise H¹: h¹(M) = h¹(M₁) + h¹(M₂) |
