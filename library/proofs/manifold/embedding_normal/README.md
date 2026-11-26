# embedding_normal — the normal and complexified tangent projections of a Euclidean embedding

An embedding f of an n-manifold in ℝ^N has, at each base point, the orthogonal projection of ℝ^N onto the vectors orthogonal to the image of the differential: `embedding_normal_projection`, a real symmetric idempotent N×N matrix, zero off the base carrier. `embedding_normal_bundle` reads it as a complex projection bundle of ambient size N, the complexified normal bundle, and `embedding_complex_tangent` is its complement in ℂ^N, the complexified tangent bundle. The projection is a choice, made by its image; it is the unique such matrix: `NormalProjectionSpec` states the choice's clauses at every base point, and `NormalProjectionChart` its formula I − J(JᵀJ)⁻¹Jᵀ in a chart.

The topological index pushes forward through the normal bundle, the Todd class of the tangent bundle is read on its complexified projection, and a Spin structure is laid on the tangent frames of the embedded metric, in their own chapters.

## Members

| Member | Statement or role |
|---|---|
| `NormalProjectionDef` | Definition of `embedding_normal_projection` |
| `NormalBundleDef` | Definition of `embedding_normal_bundle` |
| `ComplexTangentDef` | Definition of `embedding_complex_tangent` |
| `NormalProjectionSpec` | At a carrier point the selected normal projection is a padded symmetric idempotent whose image is the normal space — card |
| `NormalProjectionChart` | In a compatible chart the normal projection of an immersion is I − J(JᵀJ)⁻¹Jᵀ — card |
