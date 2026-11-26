# hilbert_space — complex normed spaces and Hilbert spaces on module carriers

Complex vector spaces use the existing module record over `complex_ring`. Norms and inner products are explicit components; the inner product is linear in its first argument and conjugate linear in its second. All identities are guarded by the module carrier. Completeness uses the metric induced by subtraction, so a closed subspace retains the ambient distance.

The orthogonal complement and projection are defined on the carrier. A projection is zero outside it; its uniqueness is therefore an equality of total functions. Finite dimensionality is the algebraic finite-basis predicate, and does not silently assign a dimension to an infinite space.

## Members

| Member | Statement or role |
|---|---|
| `NormedSpace` | Definition of `complex_normed_space` |
| `NormDistanceDef` | Definition of `norm_distance` |
| `NormTopologyDef` | Definition of `norm_topology` |
| `BanachSpace` | Definition of `complex_banach_space` |
| `InnerProductSpace` | Definition of `complex_inner_space` |
| `HilbertNormDef` | Definition of `hilbert_norm` |
| `HilbertSpace` | Definition of `complex_hilbert_space` |
| `OrthogonalComplementDef` | Definition of `hilbert_complement` |
| `OrthogonalProjectionDef` | Definition of `hilbert_projection` |
| `ProductInnerDef` | Definition of `direct_sum_inner` |
| `NormMetric` | The norm-induced distance is a metric on the module carrier |
| `CauchySchwarz` | Cauchy–Schwarz for carrier vectors of a positive semidefinite Hermitian form — card |
| `InnerProductNorm` | The inner-product norm makes the module a complex normed space — card |
| `ClosedSubspace` | A closed linear subspace of a Hilbert space is Hilbert — card |
| `OrthogonalDecomposition` | Every vector splits into its projection onto a closed subspace and a perpendicular remainder — card |
| `ProjectionLinearContraction` | Orthogonal projection onto a closed subspace is linear and contractive — card |
| `OrthogonalComplementClosed` | The orthogonal complement of a carrier subset is a closed submodule — card |
| `FiniteDimensionalHeineBorel` | A closed bounded set inside a finite dimensional submodule of a normed space is compact — card |
| `FiniteDimensionalClosed` | A finite dimensional submodule of a normed space is closed — card |
| `FiniteDimensionalComplete` | A finite dimensional normed space is Banach — card |
| `ProductHilbert` | The product module with the sum inner product is Hilbert — card |
| `SeminormDef` | complex_seminorm |
| `SeminormKernelDef` | seminorm_kernel |
| `QuotientNormDef` | quotient_norm |
| `SemiInnerDef` | complex_semi_inner |
| `QuotientInnerDef` | quotient_inner |
| `SeminormQuotientNormed` | submodule(complex_ring, M, seminorm_kernel(M, v)) ∧ complex_normed_space(quotient_module(M, seminorm_kernel(M, v)), quotient_norm(v)) ∧ (∀x:A. x ∈ M.carrier ⇒ quotient_norm(v, left_coset(M.add, x, seminorm_kernel(M, v))) = v(x)) — card |
| `SeminormQuotientComplete` | complex_banach_space(quotient_module(M, seminorm_kernel(M, v)), quotient_norm(v)) — card |
| `SemiInnerQuotient` | complex_seminorm(M, hilbert_norm(p)) ∧ complex_inner_space(quotient_module(M, seminorm_kernel(M, hilbert_norm(p))), quotient_inner(p)) ∧ (∀Q:set(A). Q ∈ quotient_module(M, seminorm_kernel(M, hilbert_norm(p))).carrier ⇒ hilbert_norm(quotient_inner(p), Q) = quotient_norm(hilbert_norm(p), Q)) — card |
