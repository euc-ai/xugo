# fredholm — Fredholm operators, parametrices and the integer index

A Fredholm operator is bounded between Hilbert spaces, has closed image, and has finite dimensional kernel and orthogonal cokernel. The index is the integer difference of those dimensions. It is read only under the Fredholm hypothesis; algebraic dimension is unspecified for infinite dimensional modules.

Atkinson's criterion uses a bounded inverse modulo compact errors on both carriers. The stability cards use operator-norm neighbourhoods and give compact-perturbation invariance, direct-sum additivity and composition additivity. Finite dimensional stabilization makes a nearby family surjective and fixes the dimension of its augmented kernel; the original kernels need not have constant dimension.

## Members

| Member | Statement or role |
|---|---|
| `KernelDef` | Definition of `hilbert_kernel` |
| `CokernelDef` | Definition of `hilbert_cokernel` |
| `FredholmDef` | Definition of `fredholm_operator` |
| `IndexDef` | Definition of `fredholm_index` |
| `ParametrixDef` | Definition of `fredholm_parametrix` |
| `Atkinson` | A bounded Hilbert-space operator is Fredholm exactly when it has a two-sided parametrix modulo compact operators — card |
| `FredholmOpenIndexLocallyConstant` | A small operator-norm neighbourhood of a Fredholm operator consists of Fredholm operators with the same index — card |
| `CompactPerturbation` | Adding a compact operator preserves Fredholmness and index — card |
| `IndexComposition` | Composition preserves Fredholmness and adds indices — card |
| `IndexDirectSum` | Direct sum preserves Fredholmness and adds indices — card |
| `IndexAdjoint` | The adjoint is Fredholm with the negative index — card |
| `IndexHomotopy` | The endpoints of an operator-norm continuous Fredholm path have equal indices — card |
| `FiniteDimensionalStabilization` | A fixed finite dimensional target supplement makes every nearby operator surjective with constant augmented-kernel dimension — card |
