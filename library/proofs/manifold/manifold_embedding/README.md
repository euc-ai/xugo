# manifold_embedding — compact manifolds in Euclidean space: finite embeddings, the weak Whitney bounds and tubular retractions

The chapter places a compact smooth manifold in Euclidean space. A
finite chart cover and a partition of unity give a smooth embedding
into some ℝᴺ; projections along directions outside null sets lower N
to 2n+1 for embeddings and to 2n for immersions; and an embedding has
an open neighbourhood that retracts smoothly onto the manifold.
Everything is stated at the level of atlases
([smooth_manifold](../smooth_manifold/README.md)): no tangent bundle
and no Sard theorem is read, only the null images of lower-dimensional
maps ([vec_null](../../vector/vec_null/README.md)).

## Compact Euclidean embeddings

A finite chart cover and a subordinate partition of unity give a finite
Euclidean embedding. Its blocks are ρ and ρ times the coordinates of
the associated chart. The support lies inside that chart, so these
products extend smoothly by zero. Wherever ρ>0 their ratios recover the
coordinates, separating points; the differentials of both kinds of
blocks force the kernel to vanish. Compactness then gives the image
topology. The first target dimension need only be finite.

To lower it from N, avoid two chartwise images: the secant cone
`t(i(x)−i(y))`, of parameter dimension 2n+1, and the tangent cone
`Di(x)v`, of parameter dimension 2n. Smoothness gives local Lipschitz
regularity, so each image is null when its parameter dimension is below
N. A countable chart cover suffices, and the immersion step reads no
compactness. A nonzero direction outside their
union gives a projection with injective point map and differential;
its perpendicular hyperplane is identified linearly with normalized
(N−1)-space. For immersions only the tangent cone must be avoided.
Choose the direction in the punctured Euclidean carrier, which handles
the empty source as well.

Iteration gives the compact weak Whitney embedding bound 2n+1 and
immersion bound 2n. In dimension zero the immersion can identify all
points in zero-space; the embedding instead uses one-space. These
statements use chartwise null images and do not require the full Sard
theorem or the tangent bundle's manifold structure.

| Member | Statement |
|---|---|
| `CompactSmoothEmbedding` | a compact smooth manifold embeds in some finite Euclidean space — card |
| `PointEmbedding` | a point is a compact manifold embedded at the origin of every Euclidean space — card |
| `EmbeddingProjectionStep` | above 2n+1, a linear projection lowers the embedding dimension by one — card |
| `ImmersionProjectionStep` | above 2n, a linear projection lowers the immersion dimension by one — card |
| `WhitneyEmbedding` | a compact n-manifold smoothly embeds in $\mathbb{R}^{2n+1}$ — card |
| `WhitneyImmersion` | a compact n-manifold smoothly immerses in $\mathbb{R}^{2n}$ — card |

## Tubular retraction

For a supplied compact Euclidean embedding i, local orthonormal normal
frames make the endpoint map `(x,w) ↦ i(x)+w` a local diffeomorphism
near the zero section. Compactness supplies a uniform small radius and
rules out collisions from different base points. The image of that
normal neighbourhood is open, and the inverse base component is the
smooth retraction r. This global step is needed in addition to the
local inverse function theorem.

The conclusion gives the open Euclidean set U, the smooth corestriction
of i to U, the smooth map r:U→M, and r∘i=id on the manifold carrier.
It supplies precisely the data used by compact cohomology comparisons;
no closest-point minimization claim, isometric embedding or homotopy
equivalence of a prescribed neighbourhood is included. Empty manifolds
use U empty, and dimension zero is included.

| Member | Statement |
|---|---|
| `CompactTubularRetraction` | every supplied compact Euclidean embedding has a smooth open-neighbourhood retraction — card |
| `CompactEuclideanRetract` | a compact manifold admits Euclidean neighbourhood retraction data — card |
