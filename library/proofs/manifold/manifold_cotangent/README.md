# manifold_cotangent — covectors, the cotangent manifold and metric comparison

A covector is a normalized family of linear coordinate functionals at one base point. Compatibility is expressed by equal pairing with every tangent vector; equivalently its components transform by the inverse transpose Jacobian. The cotangent charts put the base coordinates before the fibre coordinates.

A Riemannian metric gives a smooth fibrewise isomorphism from tangent vectors to covectors. This is a proper map on total spaces even though the projection to the base is generally not proper. Compact-support K theory is transported through this actual map.

## Members

| Member | Statement or role |
|---|---|
| `CovectorDef` | Definition of `cotangent_covector` |
| `BundleDef` | Definition of `cotangent_bundle` |
| `FromChartDef` | Definition of `cotangent_from_chart` |
| `chartDef` | Definition of `cotangent_chart` |
| `AtlasDef` | Definition of `cotangent_atlas` |
| `TopologyDef` | Definition of `cotangent_topology` |
| `MetricFlatDef` | Definition of `cotangent_metric_flat` |
| `ScaleDef` | Definition of `cotangent_scale` |
| `CoordinateCovector` | Inverse-transpose transport constructs a covector with the prescribed chart value — card |
| `CoordinateReconstruction` | A covector is reconstructed from its value in one active chart — card |
| `CotangentManifold` | The cotangent bundle is a smooth manifold of twice the base dimension — card |
| `ProjectionSmooth` | The cotangent projection is smooth — card |
| `MetricIdentification` | A Riemannian metric gives a smooth proper tangent-to-cotangent homeomorphism — card |
