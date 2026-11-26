# valuation_order — integer orders of powers and of finite sums

The valuation laws range over pairs of nonzero elements; a product of two of them can be zero in a ring with zero divisors, and then the product law speaks of the order of zero. The finite-sum theorems hold over any commutative ring and keep zero apart from the elements of greater order, so the order of zero does not enter their conclusions. A power lives in a field, where a nonzero element has nonzero powers.

## Members

| Member | Statement |
|---|---|
| `ValuationOrderDef` | `valuation_order`: ring_ops(A) → (A → int) → bool |
| `UniqueExtremeOrderNonzero` | A unique term of least order determines the order and nonvanishing of a finite sum |
| `PowerOrder` | A nonzero element of a field has nonzero powers, each of order the exponent times its own |
| `DistinctOrdersSumNonzero` | A finite sum with a nonzero term, whose nonzero terms have pairwise different orders, is nonzero |
