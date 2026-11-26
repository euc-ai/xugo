# cohomological_index — Todd correction and the cohomological index formula

The cotangent charts store base coordinates before covector coordinates. The symplectic atlas reorders them as (x1, xi1, ..., xn, xin), giving the orientation of -d(theta)=sum dxj wedge dxij. It exists without an orientation of the base.

With the Lambda E Koszul convention and ch=tr exp(-F/(2 pi i)), the formula in this orientation has factor $(-1)^n$. This sign follows from the separately computed Bott character. The tangent Todd class is the characteristic class of the complexified real tangent projection supplied by an embedding, and independence is a theorem. No numerical index is used to define any characteristic class.

## Members

| Member | Statement or role |
|---|---|
| `symplecticAtlasDef` | Definition of `cotangent_symplectic_atlas` |
| `TangentToddDef` | Definition of `tangent_todd_class` |
| `IntegrandDef` | Definition of `index_character_class` |
| `CohomologicalIndexDef` | Definition of `cohomological_index` |
| `CotangentOrientation` | Both block and interleaved cotangent atlases are oriented — card |
| `ComplexTangent` | The embedded complex tangent projection has rank n and complements the normal projection — card |
| `EmbeddedTangentIsomorphic` | The tangent projections of any two Euclidean embeddings are isomorphic — card |
| `TangentToddOnEmbedding` | The tangent Todd class is represented by any embedded tangent projection — card |
| `NormalToddCorrection` | The inverse dual-normal Todd class is the tangent Todd class — card |
| `IntegrandCarrier` | The index integrand is a compact top-degree cohomology class — card |
| `AtiyahSingerCohomological` | The analytic index equals the signed Chern–Todd integral — card |
