# projection_bundle — finite complex projection bundles and their stable operations

A bundle is a Hermitian projection with one ambient dimension bound over the entire base. Its matrix entries are continuous and vanish outside the base carrier and the finite square. Rectangular maps act between the images of two projections; invertibility means inverse maps on those images, not invertibility on the ambient spaces.

Block sum and tensor product retain their ambient dimensions. The total space is the set of pairs of a base point and a vector of the image there (`projection_total_space`); its topology is inherited from the base times finite complex coordinates (`projection_total_topology`); the rank at a point is the trace of the projection there, and can differ on different components.

## Members

| Member | Statement or role |
|---|---|
| `ProjectionDef` | Definition of `continuous_projection_bundle` |
| `TrivialDef` | Definition of `projection_trivial` |
| `MapDef` | Definition of `continuous_projection_map` |
| `InverseDef` | Definition of `projection_inverse_on` |
| `IsomorphicDef` | Definition of `projection_isomorphic` |
| `SumDef` | Definition of `projection_sum` |
| `TensorDef` | Definition of `projection_tensor` |
| `PullbackDef` | Definition of `projection_pullback` |
| `RankDef` | Definition of `projection_rank` |
| `TotalSpaceDef` | Definition of `projection_total_space` |
| `TotalTopologyDef` | Definition of `projection_total_topology` |
| `TrivialBundle` | Trivial finite projections define continuous bundles — card |
| `IsomorphismEquivalence` | Bundle isomorphism is an equivalence relation — card |
| `SumBundle` | Direct sums are continuous projection bundles — card |
| `TensorBundle` | Tensor products are continuous projection bundles — card |
| `SumIsomorphism` | Direct sum respects bundle isomorphism — card |
| `TensorIsomorphism` | Tensor product respects bundle isomorphism — card |
| `PullbackBundle` | Continuous pullback defines a projection bundle — card |
| `RankTrace` | Where the matrix is idempotent, the rank is its trace, at most the ambient dimension — card |
| `PointIsomorphicIffRank` | Over a one-point base, bundles are isomorphic exactly when their ranks agree — card |
| `ProjectionsCloseIsomorphic` | Bundles of one ambient dimension within Hilbert–Schmidt distance one are isomorphic — card |
| `HomotopicPullbacks` | Homotopic maps from a compact base give isomorphic pullback bundles — card |
| `TotalSpaceLocallyCompact` | The total space of a finite projection bundle is locally compact Hausdorff — card |
