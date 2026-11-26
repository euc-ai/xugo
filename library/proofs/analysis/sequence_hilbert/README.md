# sequence_hilbert — enumeration-independent weighted square-summable sequences

A sequence is a function on a fixed index type, zero outside a specified index set. Weighted square summability bounds all finite subsums of the nonnegative squared modulus. Strict positivity of the weight on the index set is a hypothesis of the Hilbert-space instance, including at arbitrarily small weights.

Complex sums are limits of the directed finite subsets: no enumeration enters the definition. The summation layer comes first: a family whose finite modulus sums are bounded has a sum, a nonnegative family sums to the supremum of its finite subsums, the relation is linear and commutes with conjugation, and an absolutely summable family on a product sums row by row. Finite-support truncations are dense, and reindexing bijections transport both the sum and the inner product. The empty index set is the zero Hilbert space.

## Members

| Member | Statement or role |
|---|---|
| `UnorderedSumRelationDef` | Definition of `unordered_complex_sums` |
| `UnorderedSumDef` | Definition of `unordered_complex_sum` |
| `WeightedSquareSummableDef` | Definition of `weighted_square_summable` |
| `SequenceModuleDef` | Definition of `weighted_sequence_module` |
| `SequenceInnerDef` | Definition of `weighted_sequence_inner` |
| `SequenceTruncateDef` | Definition of `sequence_truncate` |
| `SumAbsolute` | A family with bounded finite modulus sums has an unordered sum, of modulus at most the bound — card |
| `SumNonneg` | A nonnegative family with bounded finite subsums sums to their supremum — card |
| `SumLinear` | The unordered sum relation is additive, homogeneous and commutes with conjugation — card |
| `SumIterated` | An absolutely summable family on a product sums row by row to its sum over the product — card |
| `WeightedHilbert` | Strictly positive weights give a Hilbert space of normalized square-summable sequences — card |
| `InnerProductSum` | The weighted polarized finite-subset sums converge to the inner product — card |
| `NormSquaredFiniteSup` | The squared norm is the supremum of the finite weighted squared-modulus sums — card |
| `FiniteSupportDense` | Finite-support truncations approximate every weighted square-summable sequence — card |
| `SumReindex` | A bijection of index carriers preserves the unordered sum relation — card |
| `SumUnique` | An unordered complex sum has a unique value — card |
| `FiniteSum` | A family supported on a finite subset sums to its finite module sum there — card |
