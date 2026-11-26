# smooth_projection_bundle — smooth Hermitian projections over a manifold and the smooth maps between their images

A smooth projection bundle of ambient size r is a matrix function whose real and imaginary entries are smooth on the manifold, which vanishes outside the base carrier and the r×r square, and which is a Hermitian idempotent at every point of the base. Its image is the bundle; the rank may vary between components of a disconnected base. A smooth bundle map from im P to im Q is a smooth rectangular matrix function fixed by Q on the left and P on the right.

These are the smooth counterparts of [projection_bundle](../../topology/projection_bundle/README.md)'s continuous bundles and maps. Sobolev sections, connections and characteristic forms, frames and total spaces are built on them in their own chapters.

## Members

| Member | Statement or role |
|---|---|
| `SmoothProjectionDef` | Definition of `smooth_projection_bundle` |
| `SmoothBundleMapDef` | Definition of `smooth_projection_map` |
| `RealifiedDeterminant` | The realification of a complex matrix has determinant the squared modulus of its determinant — card |
| `SmoothNormalizedInverse` | A normalized inverse of a smooth map between smooth Hermitian projections has smooth entries — card |
| `SmoothBundleContinuous` | A smooth projection bundle is a continuous projection bundle — card |
