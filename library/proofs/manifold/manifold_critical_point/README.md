# manifold_critical_point — null sets, critical points and regular values on manifolds: Sard's theorem and regular level submanifolds

The chapter is Sard's theorem on manifolds and what stands around it.
It has the null sets of a manifold, tested chart by chart; the
critical points of a smooth map and the regular values of its target;
the theorem that critical values are null and regular values dense,
reduced over a countable atlas to the Euclidean one
([vec_critical_point](../../vector/vec_critical_point/README.md)); and
the atlas a regular level set carries as an embedded submanifold.
Atlases, smooth maps and embeddings are
[smooth_manifold](../smooth_manifold/README.md)'s.

## Null sets, Sard and regular values

`manifold_null_set⟨n⟩(T, 𝒜, K)` requires K to lie in the manifold
carrier and have a null coordinate image in every compatible chart.
It is enough to test the original atlas: second countability supplies
a countable covering subatlas, and smooth transitions preserve null
sets by local Lipschitzness. The union argument uses this countable
cover even if the original atlas has uncountably many charts.
Compatible covering atlas changes, open restriction and equal-dimensional
smooth diffeomorphisms preserve nullity. No orientation or measure is
chosen. In dimension zero, only the empty set is null.

`manifold_critical_point⟨n,m⟩(T, 𝒜, S, ℬ, f, x)` asks for an active
compatible chart pair whose coordinate differential at x fails to map
the normalized n-vectors onto the normalized m-vectors. Its definition
includes x in the source carrier; the laws also require f to be smooth.
Invertible transition differentials show that every active chart pair
gives the same answer. All coordinate comparisons use the open preimage
of the target-chart domain, since one source chart need not map into
one target chart.

For a smooth f, `manifold_regular_value⟨n,m⟩` requires a point of the
target carrier with no critical preimage. Points with empty fibers are
regular. Manifold Sard reduces to Euclidean Sard in a countable source
atlas, for each target chart separately. Thus the critical values are
null and regular values are dense in the whole target carrier; neither
compactness nor surjectivity is assumed.

| Member | Statement |
|---|---|
| `NullSetDef` | chartwise nullity with an explicit manifold-carrier guard |
| `CriticalPointDef` | failure of coordinate-differential surjectivity in an active chart pair |
| `RegularValueDef` | a target-carrier point with no critical preimage |
| `NullEmpty` | the empty set is null — card |
| `NullSubset` | subsets of null sets are null — card |
| `NullCountableUnion` | countable unions of null sets are null — card |
| `NullAtlasCriterion` | the original covering atlas suffices to test nullity — card |
| `NullAtlasInvariant` | a compatible covering atlas determines the same null sets — card |
| `NullOpenRestrict` | open-submanifold nullity agrees with ambient nullity — card |
| `NullEuclidean` | nullity in the canonical Euclidean open atlas is Euclidean nullity — card |
| `NullZeroDimension` | only the empty subset of a zero-dimensional manifold is null — card |
| `NullOpenIffEmpty` | a null open subset is empty, in every dimension — card |
| `NullDiffeomorphism` | an equal-dimensional smooth diffeomorphism preserves and reflects nullity — card |
| `CriticalPointCoordinate` | any active chart pair tests the same criticality — card |
| `RegularPointDimensionBound` | a regular source point forces target dimension at most source dimension — card |
| `RegularValueIff` | regular values are the target-carrier complement of the critical-value image — card |
| `ManifoldSard` | critical values of a smooth manifold map are null — card |
| `RegularValuesDense` | the closure of the regular values is the whole target carrier — card |

## Regular level submanifolds

At a regular source point, append linear coordinates to the coordinate
expression of f so that the augmented differential is invertible. The
smooth inverse theorem then gives a compatible source chart on which
f is exactly the projection onto the first m coordinates. The chart
is contained in the preimage of the chosen target chart.

Fixing a regular value fixes these m coordinates. The remaining n−m
coordinates give compatible charts on the actual fiber, whose topology
is the source subspace topology. Their inclusion into the source has
injective differential and is a topological embedding. Hausdorffness
and second countability pass to the subspace.

The level theorem explicitly assumes m≤n. A nonempty regular fiber
already implies this bound by `RegularPointDimensionBound`; an empty
fiber supplies no such dimension information, and is allowed with an
empty atlas. Density of regular values does not assert that a regular
fiber is nonempty.

| Member | Statement |
|---|---|
| `RegularPointCoordinates` | near a regular source point, compatible charts make f a coordinate projection — card |
| `RegularLevelSubmanifold` | a regular fiber with m≤n admits an (n−m)-manifold atlas whose inclusion is a smooth embedding — card |
