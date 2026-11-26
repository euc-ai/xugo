# bounded_operator — bounded linear operators, adjoints and compact operators

Operators act between explicit complex normed module carriers. Boundedness is a property of total maps restricted to those carriers; values outside the source do not affect the operator norm. Compactness means relative compactness of the image of the closed unit ball in the target topology.

The adjoint is normalized to zero outside the target carrier. Operator identities that compare arbitrary maps are asserted only on their carriers. The operator module itself consists of normalized bounded maps, so completeness and norm limits do not identify distinct irrelevant off-carrier values.

## Members

| Member | Statement or role |
|---|---|
| `BoundedOperatorDef` | Definition of `bounded_operator` |
| `OperatorNormDef` | Definition of `bounded_op_norm` |
| `OperatorModuleDef` | Definition of `operator_module` |
| `FiniteRankDef` | Definition of `finite_rank_operator` |
| `CompactOperatorDef` | Definition of `compact_operator` |
| `AdjointDef` | Definition of `hilbert_adjoint` |
| `OperatorNormBound` | The operator norm is nonnegative and bounds every carrier vector — card |
| `BoundedIffContinuous` | A linear map between normed spaces is bounded exactly when continuous — card |
| `OperatorSpaceBanach` | Normalized bounded maps into a Banach space form a Banach space — card |
| `BoundedExtension` | A bounded linear map on a dense submodule extends to a bounded operator into a Banach space with the same bound — card |
| `BoundedAgreeDense` | Bounded operators that agree on a dense set agree on the source carrier — card |
| `NeumannInverse` | The identity plus an operator of norm below one is a bijection with bounded inverse on a Banach space — card |
| `BoundedInverse` | A bounded linear bijection between Banach spaces has bounded inverse — card |
| `RieszRepresentation` | A bounded complex-linear functional has a unique representing vector — card |
| `Adjoint` | A bounded Hilbert-space operator has an adjoint with the same operator norm — card |
| `FiniteRankCompact` | A bounded finite-rank map between normed spaces is compact — card |
| `CompactNormLimit` | An operator-norm limit of compact maps into a Banach space is compact — card |
| `CompactAdd` | The sum of two compact operators is compact — card |
| `CompactIdeal` | A composite of bounded operators is compact if either factor is compact — card |
| `CompactAdjoint` | The adjoint of a compact Hilbert-space operator is compact — card |
| `CompactApproximation` | A compact Hilbert-space operator admits finite-rank approximations in operator norm — card |
