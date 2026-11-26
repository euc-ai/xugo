# smooth_manifold — atlases, smooth maps, partitions of unity, immersions and diffeomorphisms

The points of a manifold live in a simple type A; its carrier is the
union of a topology T, not necessarily all of A. A chart is a pair
`c : prod(set(A), A → num → real)`. Its domain is `fst(c)` and its
coordinate map is `snd(c)`. The predicate `manifold_chart⟨n⟩(T, c)`
requires an open domain and a homeomorphism to an open subset of the
zero-padded n-vectors. The inverse is `inverse_on(fst(c), snd(c))`:
only its values on the coordinate image are determined or used.

A `smooth_atlas⟨n⟩(T, 𝒜)` covers the carrier and has smooth changes
of coordinates on the overlap images. The topology axiom is included
even when the atlas is empty. A `compatible_chart⟨n⟩(T, 𝒜, c)` is a
chart with smooth transitions in both directions with every atlas
member. Compatibility of two such charts follows locally through an
original chart containing the point. Consequently all compatible
charts form an atlas, and completing the atlas this way does not
change compatibility. This predicate indexes geometric objects;
there is no chosen maximal atlas stored as additional data.

`smooth_manifold⟨n⟩(T, 𝒜)` requires the topology, Hausdorffness,
second countability and the smooth atlas. The dimension n is fixed,
including on disconnected spaces. Empty manifolds are admitted in
every dimension; the empty topology is `{∅}`, with empty carrier.
Dimension zero uses the singleton carrier of zero-padded zero-vectors,
so its chart domains are empty or singletons. Second countability
provides a countable subatlas with exactly the same compatible charts.

`smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)` includes both manifold
conditions and continuity of the carrier map. For every source chart
c and target chart d, it asks that

    snd(d) ∘ f ∘ inverse_on(fst(c), snd(c))

be smooth on

    image(snd(c), {x | x ∈ fst(c) and f(x) ∈ fst(d)}).

Continuity makes this domain open. A source chart need not map into
one target chart, and the criterion remains valid when either
dimension is zero. The same tests may use all compatible charts.
Smoothness composes, restricts to open submanifolds, is local on the
source, and depends only on the map's values on the source carrier.
No smoothness across a chart boundary is asserted.

The canonical Euclidean atlas consists of the identity chart on an
open U. Its manifold maps are exactly the existing Euclidean smooth
maps with image in the target open set. The open submanifold atlas
consists of all original compatible charts whose domains lie in U.
Its compatible charts are precisely those same charts; no extensions
or choices of coordinates are needed.

The product topology carries the atlas of chart pairs. Coordinates
concatenate the first n-vector and second m-vector, with an explicit
zero tail from index n+m. The block projections and pairing are
smooth, and Hausdorffness and second countability use the existing
product theorems. Zero-dimensional and empty factors are included.

## Definitions

| Member | Constant |
|---|---|
| `ChartDef` | `manifold_chart⟨n⟩(T, c)` |
| `AtlasDef` | `smooth_atlas⟨n⟩(T, 𝒜)` |
| `CompatibleChartDef` | `compatible_chart⟨n⟩(T, 𝒜, c)` |
| `ManifoldDef` | `smooth_manifold⟨n⟩(T, 𝒜)` |
| `ImmersionDef` | `smooth_manifold_immersion⟨n, m⟩(T, 𝒜, S, ℬ, f)` |
| `DiffeomorphismDef` | `smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)` |
| `EmbeddingDef` | `smooth_manifold_embedding⟨n, m⟩(T, 𝒜, S, ℬ, f)` |
| `SmoothMapDef` | `smooth_manifold_map⟨n, m⟩(T, 𝒜, S, ℬ, f)` |
| `EuclideanAtlasDef` | `euclidean_atlas(U)` |
| `OpenAtlasDef` | `open_submanifold_atlas⟨n⟩(T, 𝒜, U)` |
| `ProductAtlasDef` | `smooth_product_atlas⟨n, m⟩(𝒜, ℬ)` |

## Atlas and manifold cards

| Member | Statement |
|---|---|
| `ChartRestrict` | Restrict a chart to an open subset of its domain — card |
| `AtlasMemberCompatible` | Every original chart is compatible — card |
| `CompatibleTransition` | Compatible charts have diffeomorphic overlap images — card |
| `CompatibleAtlas` | All compatible charts form a smooth atlas — card |
| `CompatibleAtlasInvariant` | Atlas completion preserves compatibility — card |
| `AtlasSubcover` | A covering subatlas has the same compatible charts — card |
| `CountableAtlas` | A manifold admits a countable original subatlas with the same compatibility — card |
| `EuclideanManifold` | An open subset of R^n with its identity chart is a manifold — card |
| `EmptyManifold` | The empty space with the empty atlas is a manifold in every dimension — card |
| `OpenSubmanifold` | An open subset with its restricted compatible atlas is a manifold — card |
| `OpenCompatibleChart` | Submanifold compatibility is original compatibility with domain in U — card |
| `ProductManifold` | The product charts give the sum-dimensional product manifold — card |
| `ProductCompatibleChart` | Any two compatible factor charts give a compatible product chart — card |

## Smooth map cards

| Member | Statement |
|---|---|
| `SmoothMapCompatibleCharts` | Test smoothness in all compatible charts — card |
| `SmoothMapIdentity` | The identity map is smooth — card |
| `SmoothMapCompose` | Smooth maps compose — card |
| `SmoothMapConstant` | A constant map to a point of the target carrier is smooth — card |
| `SmoothMapCongruence` | Carrier agreement preserves smoothness — card |
| `SmoothMapRestrict` | Restrict a smooth map between open submanifolds — card |
| `SmoothMapLocal` | Smoothness on an open source neighbourhood of every point suffices — card |
| `SmoothOpenInclusion` | Open submanifold inclusion is smooth — card |
| `SmoothMapEuclidean` | Identity-chart smoothness agrees with Euclidean smoothness and image containment — card |
| `SmoothProductProjections` | Both product projections are smooth — card |
| `SmoothProductPair` | A pair of smooth maps is smooth into the product — card |

The definitions use the topology, countability, product topology and
Euclidean smooth-map chapters. The [tangent chapter](../tangent/README.md)
constructs chart-indexed tangent vectors and their paired total space;
the [differential-form chapter](../differential_form/README.md) constructs
compatible Euclidean form families, wedge, exterior derivative and
smooth pullback.

## Convex Euclidean contraction

A nonempty convex Euclidean open U contracts smoothly to any specified
point a. The homotopy is defined on U times the entire real time line,
fixes a, and runs from the constant map at time zero to the identity at
time one. A smooth clock θ with values in [0,1] keeps
`(1−θ(t))a + θ(t)x` inside U for every time. One may take θ = 1−φ
for a bump φ equal to one near zero and zero at distance at least one.
The linear clock t itself would leave a bounded U beyond the endpoints.

| Member | Statement |
|---|---|
| `ConvexOpenContraction` | A convex open with a specified point has a smooth contraction on the whole time line — card |

## Normalized functions and compact partitions

`smooth_manifold_function⟨n⟩(T, 𝒜, f)` requires smooth scalar expressions
in every compatible chart and zero values outside the base carrier.
The normalization makes the correspondence with zero-forms one-to-one.
A constant scalar on the manifold is therefore normalized to zero off
its carrier. Addition, multiplication and finite sums are pointwise;
a reciprocal is normalized after taking its coordinate values.

Smoothness is local on open submanifolds. Restricting f to U normalizes
it to U, so a smooth function on that submanifold already has the same
host type as its zero extension. The extension is smooth when its
support in U is closed in the whole manifold. Its complement then gives
an open neighbourhood where the function is identically zero. Compact
support supplies this ambient closedness because manifolds are Hausdorff.
Support uses [function_support](../../topology/function_support/README.md).

`FunctionBump` puts a compactly supported function inside any open U
containing a compact K, with values in [0,1] and value one on an open
neighbourhood of K. Coordinate bumps with nested radii extend by zero;
a finite cover of K combines them. For an open cover C of K,
`manifold_partition_of_unity⟨n⟩(T, 𝒜, K, C, N, ψ)` has N nonnegative
smooth functions, each compactly supported inside one member of C.
Their sum is at most one on the manifold and exactly one on an open
neighbourhood of K. Values at indices i ≥ N are unused.

To construct the partition, add finitely many subordinate bumps to get
s > 0 near K. Choose a compact cutoff χ inside the open positive set of
s, equal to one near K. Normalize the bumps there by χ/s, then extend by
zero. This keeps the supports inside the covering sets and makes the
sum χ; no division at a zero of s is needed. Empty K admits N = 0 and
an empty neighbourhood. The neighbourhood condition also makes the
derivative of the sum zero near K.

| Member | Statement |
|---|---|
| `SmoothFunctionDef` | `smooth_manifold_function⟨n⟩(T, 𝒜, f)` |
| `PartitionOfUnityDef` | `manifold_partition_of_unity⟨n⟩(T, 𝒜, K, C, N, ψ)` |
| `FunctionConstant` | A normalized constant is smooth — card |
| `FunctionAdd` | Pointwise sums preserve smooth functions — card |
| `FunctionMul` | Pointwise products preserve smooth functions — card |
| `FunctionFiniteSum` | Finite sums preserve smooth functions, including the empty sum — card |
| `FunctionReciprocal` | A nowhere-zero function has a smooth normalized reciprocal — card |
| `FunctionContinuous` | Smooth scalar functions are continuous — card |
| `FunctionLocal` | Local smoothness gives a smooth function after carrier normalization — card |
| `FunctionRestrict` | Normalized restriction to an open submanifold is smooth — card |
| `FunctionExtendZero` | Ambient closed support makes submanifold zero extension smooth — card |
| `FunctionBump` | A compact subset of an open set admits a compact smooth cutoff — card |
| `PartitionOfUnity` | An open cover of a compact set admits a finite subordinate partition near it — card |

## Immersions and embeddings

An immersion is a smooth map whose Jacobian at every active compatible
chart pair acts injectively on normalized source vectors. It is enough
to check the original atlas pairs: the change of coordinates has an
invertible Jacobian. Immersions compose and can be checked locally on
the source. A nonempty n-manifold can immerse in an m-manifold only
when n≤m; nonemptiness is necessary because an empty manifold is allowed
in every dimension.

A smooth embedding is an immersion that is also a topological embedding
into its image with the subspace topology. A compact injective immersion
has this property because the target is Hausdorff. No equivalence with
an arbitrary smooth injective map is asserted. The
[tangent chapter](../tangent/README.md) identifies the immersion test
with injectivity of the intrinsic tangent differential, and
[manifold_embedding](../manifold_embedding/README.md) embeds every compact manifold in a
Euclidean space.

| Member | Statement |
|---|---|
| `ImmersionAtlasCriterion` | original atlas pairs suffice for the injective Jacobian test — card |
| `ImmersionCompose` | smooth immersions compose — card |
| `ImmersionLocal` | a map that is an immersion on an open cover is an immersion — card |
| `ImmersionDimensionBound` | an immersion with nonempty source has n≤m — card |
| `CompactInjectiveImmersion` | a compact injective immersion is a smooth embedding — card |

## Smooth diffeomorphisms

`smooth_manifold_diffeomorphism⟨n⟩(T, 𝒜, S, ℬ, f)` combines a
smooth map, a homeomorphism onto the target carrier, and smoothness
of `inverse_on(⋃T, f)`. The two displayed dimensions are the same;
values of the total inverse outside the target carrier are irrelevant.
This predicate does not choose an orientation.

An equal-dimensional immersion is locally a diffeomorphism by the
coordinate inverse function theorem. If it is globally injective,
its image is open and the local inverses glue to a smooth inverse on
that image. Compactness is not needed. Diffeomorphisms invert and
restrict to an open and its actual image, with the compatible atlases
restricted from the ambient manifolds.

| Member | Statement |
|---|---|
| `DiffeomorphismInverse` | the carrier inverse of a smooth diffeomorphism is a smooth diffeomorphism — card |
| `DiffeomorphismOpenRestrict` | restriction to an open and its image is a smooth diffeomorphism — card |
| `ImmersionLocalDiffeomorphism` | an equal-dimensional immersion is a diffeomorphism on neighbourhoods of each source point — card |
| `InjectiveImmersionDiffeomorphism` | an injective equal-dimensional immersion is a diffeomorphism onto its open image — card |
