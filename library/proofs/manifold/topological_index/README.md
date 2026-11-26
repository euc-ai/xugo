# topological_index — the complex normal orientation of the tangent embedding and the topological index

A compact manifold is embedded in a real Euclidean space. Its orthogonal real normal projection is complexified and pulled back to TM. The complex tangent embedding is (x,v)↦f(x)+i dfₓ(v); its normal orientation is supplied by the doubled real normal bundle.

The tubular germ includes the derivative of the normal projection: in normal coordinates it is (x,v,u,w)↦(f(x)+u, dfₓ(v)+dPνₓ(v)u+w). This is the tangent of a real tubular map and fixes the complex normal convention. Pushforward through this germ and the chosen Bott generator define the integer. Tubular extension independence has its own card. TopologicalIndexOnEmbedding compares every embedding, ambient dimension and auxiliary metric with the selected index.

## Members

| Member | Statement or role |
|---|---|
| `TangentNormalDef` | Definition of `index_tangent_normal` |
| `tangentEmbeddingDef` | Definition of `index_tangent_embedding` |
| `normalDerivativeDef` | Definition of `index_normal_derivative` |
| `tangentGermDef` | Definition of `index_tubular_germ` |
| `TangentTubeDef` | Definition of `index_tangent_tube` |
| `EuclideanBottTripleDef` | Definition of `index_bott_triple` |
| `bottMultipleDef` | Definition of `index_bott_multiple` |
| `EmbeddingIndexDef` | Definition of `embedding_topological_index` |
| `IndexDef` | Definition of `topological_index` |
| `NormalProjectionSmooth` | The orthogonal normal projection of an immersion is smooth — card |
| `TangentEmbeddingProper` | The induced tangent embedding of a compact immersed manifold is proper and has closed image — card |
| `TangentNormalComplexOrientation` | The tangent normal bundle has the specified complex projection and rank — card |
| `TangentTubeExists` | The induced tangent embedding admits the specified tubular presentation — card |
| `EuclideanBottNormalization` | The Euclidean Koszul Bott class freely generates compact-support K theory — card |
| `EmbeddingIndexDefined` | The pushed class is the Bott multiple selected by the embedding index — card |
| `PointPushforward` | The unit class of a point pushes forward to the Bott generator — card |
| `TubularChoiceIndependent` | The embedding index is independent of the tubular choice — card |
| `TopologicalIndexOnEmbedding` | The topological index equals the value from any embedding and metric — card |
| `TopologicalIndexHomomorphism` | The topological index is a group homomorphism — card |
