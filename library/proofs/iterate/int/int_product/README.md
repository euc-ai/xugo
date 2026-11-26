# int_product — products of integers

Products over ℤ are `iterated_op` at integer multiplication. The general
fold laws come from `iterate/monoidal`; this chapter supplies their
reading at ℤ and the consequences that use arithmetic. Integer
multiplication inherits its monoidal facts from `int_real_lift`. Sums
over ℤ are the sibling chapter `int_sum`.

## Definition and recursion

| Member | Statement |
|---|---|
| `IntProductDef` | Integer products are folds at integer multiplication |
| `IntProductClauses` | Empty-set and insertion clauses over ℤ |

## Integer products

| Member | Statement |
|---|---|
| `IntProductSuperset` | Adding indices whose factors are 1 leaves the product unchanged |
| `IntProductConst` | A finite product of c is c to the number of factors |
| `IntProductSigns` | A product of signs is −1 to the number of negative signs |
| `IntOfNatProduct` | A finite product of naturals cast into ℤ is the product of the casts |
