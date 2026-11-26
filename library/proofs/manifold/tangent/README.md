# tangent — tangent vectors, the tangent bundle and differentials of smooth maps

For a manifold with point type A, a tangent vector at x is a function

    v : prod(set(A), A → num → real) → num → real.

It supplies a padded n-vector in every compatible chart containing x.
If c and d are two such charts, the components satisfy

    v(d) = D(phi_d ∘ phi_c^-1)(phi_c(x)) v(c).

Every incompatible chart, and every chart not containing x, has zero
component. The predicate `tangent_vector_on⟨n⟩(T, 𝒜, x, v)` includes
the manifold condition and x in its carrier. Normalization makes
equality of tangent vectors literal equality of their component
functions; no quotient or choice of chart representative is needed.

`tangent_from_chart⟨n⟩(T, 𝒜, c, x, u)` propagates one component by
the transition Jacobians, and is zero on inactive charts. The
transition cocycle and Euclidean chain rule make it a tangent vector.
Evaluation in c recovers u, and propagation of v(c) recovers v.
Thus evaluation is an isomorphism from the tangent fiber module to
the existing function module of padded n-vectors. Compatible data on
the original atlas extend uniquely to all compatible charts; values
on other original indices need not be prescribed. This is the
tangent-vector instance of extension from a covering chart family.

The total-space host type is

    prod(A, prod(set(A), A → num → real) → num → real).

`tangent_bundle⟨n⟩(T, 𝒜)` consists of pairs (x,v) with v tangent at
x. Keeping the base point is essential: the component function of a
zero vector is the same at every base, but the pairs are distinct.
Projection is `fst`, and `tangent_zero_section(x)` pairs x with the
zero component function.

An induced chart over c reads (phi_c(x),v(c)) as two n-coordinate
blocks with a zero tail from index 2n. Its domain consists of tangent
pairs based in c's domain; its image is the open coordinate image of
c times all n-vectors. The explicit inverse reconstructs the base
with `inverse_on` and the fiber with `tangent_from_chart`.
The induced transition is

    (y,u) ↦ (tau(y), D tau(y)u).

`tangent_topology⟨n⟩(T, 𝒜)` consists of subsets of the tangent
carrier whose images in every induced chart are Euclidean open.
The carrier-subset condition excludes arbitrary off-carrier pairs.
`tangent_atlas⟨n⟩(T, 𝒜)` uses all compatible base charts. Smooth
transition Jacobians give the smooth 2n-dimensional atlas; the base
Hausdorff condition and separation within a common chart give
Hausdorffness. A countable base subatlas lifts to a countable open
cover by second countable coordinate domains. No countability of
the full compatible-chart set is claimed.

For a smooth map f, `manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x)`
maps the tangent fiber at x linearly to the fiber at f(x). Its
definition chooses one compatible source chart containing x and
uses the coordinate Jacobian in every active target chart, with zero
components elsewhere. `DifferentialCoordinate` gives the same formula
using any active source chart, removing the choice from subsequent
arguments. The target chart need only contain f(x), since continuity
makes its preimage in a source chart an open neighbourhood.

`tangent_map⟨n, m⟩(T, 𝒜, S, ℬ, f)` pairs f with its differential. In
induced coordinates it reads (y,u)↦(F(y),D F(y)u), so smooth partial
derivatives make it a smooth bundle map. The Euclidean chain rule
gives the differential and tangent-map composition laws. Identity
and composition are asserted on tangent carriers, where normalization
holds; arbitrary component functions outside those carriers are not
fixed by the identity differential. Empty manifolds and zero source
or target dimensions are included throughout.

The `manifold/riemannian` chapter pairs these normalized tangent vectors
using compatible positive definite coordinate metrics. Its pairing can be
computed in any active chart and is positive definite on each fiber.

## Definitions

| Member | Constant |
|---|---|
| `TangentVectorDef` | `tangent_vector_on⟨n⟩(T, 𝒜, x, v)` |
| `TangentFromChartDef` | `tangent_from_chart⟨n⟩(T, 𝒜, c, x, u)` |
| `TangentModuleDef` | `tangent_module⟨n⟩(T, 𝒜, x)` |
| `TangentBundleDef` | `tangent_bundle⟨n⟩(T, 𝒜)` |
| `TangentChartDef` | `tangent_chart⟨n⟩(T, 𝒜, c)` |
| `TangentAtlasDef` | `tangent_atlas⟨n⟩(T, 𝒜)` |
| `TangentTopologyDef` | `tangent_topology⟨n⟩(T, 𝒜)` |
| `ZeroSectionDef` | `tangent_zero_section(x)` |
| `DifferentialDef` | `manifold_differential⟨n, m⟩(T, 𝒜, S, ℬ, f, x, v)` |
| `TangentMapDef` | `tangent_map⟨n, m⟩(T, 𝒜, S, ℬ, f, p)` |

## Fiber and bundle cards

| Member | Statement |
|---|---|
| `TangentModule` | The tangent fiber at a carrier point is a real module — card |
| `TangentFromChart` | Propagation constructs a tangent vector with the prescribed component — card |
| `TangentChartReconstruct` | One active component determines the whole tangent vector — card |
| `TangentChartIsomorphism` | Chart evaluation identifies a fiber with the padded n-vector module — card |
| `TangentAtlasExtension` | Compatible original-atlas components extend uniquely — card |
| `TangentChartImage` | The induced coordinate image is an open base-image cylinder — card |
| `TangentChartInverse` | Reconstruct the base and fiber blocks explicitly — card |
| `TangentChartTransition` | The induced transition is (tau, D tau acting on the fiber) — card |
| `TangentManifold` | The tangent topology has the paired carrier and a smooth 2n-dimensional atlas — card |
| `TangentProjection` | Projection to the base is smooth — card |
| `TangentZeroSection` | The zero section is smooth — card |

## Differential and map cards

| Member | Statement |
|---|---|
| `DifferentialCoordinate` | Any active source chart gives the same differential component — card |
| `DifferentialTangent` | The differential carries tangent vectors to the image-point fiber — card |
| `DifferentialLinear` | Each fiber differential is a real module homomorphism — card |
| `DifferentialIdentity` | The identity differential fixes tangent vectors — card |
| `DifferentialCompose` | The differential satisfies the chain rule — card |
| `TangentMapSmooth` | A smooth map induces a smooth map of tangent bundles — card |
| `TangentMapIdentity` | The identity tangent map fixes the tangent carrier — card |
| `TangentMapCompose` | Tangent maps compose on their carriers — card |

## Immersions

The coordinate definition of a smooth immersion is equivalent to
injectivity of `manifold_differential` on each tangent module carrier.
Evaluation at an active chart is a tangent-module isomorphism, so this
is a change of coordinates of the same linear map. Injectivity on all
chart-indexed host functions is neither required nor claimed. Empty
source manifolds and singleton zero-dimensional tangent carriers are
included.

| Member | Statement |
|---|---|
| `ImmersionDifferentialIff` | a smooth map is an immersion exactly when every tangent differential is injective on its carrier — card |

## Euclidean differentials

For a smooth map i:M→R^N, `manifold_euclidean_differential⟨n,N⟩`
evaluates its intrinsic differential in the global identity chart of
the Euclidean target. The result is a normalized N-vector, linear in
the tangent vector and smooth on the total tangent bundle. When i is
an immersion it is injective on each normalized tangent fiber.

[manifold_diagonal](../manifold_diagonal/README.md) measures
tangent disks by this differential of an embedding.

| Member | Statement |
|---|---|
| `EuclideanDifferentialDef` | the Euclidean identity-chart value of the intrinsic differential |
| `EuclideanDifferentialCoordinate` | the Euclidean differential is the coordinate Jacobian applied to the tangent coordinates — card |
| `EuclideanDifferentialLinear` | the Euclidean differential is linear from each tangent module to normalized N-vectors — card |
| `EuclideanDifferentialInjective` | an immersion gives an injective Euclidean differential on every tangent fiber — card |
| `EuclideanDifferentialBundleSmooth` | the Euclidean differential is smooth on the total tangent bundle — card |
