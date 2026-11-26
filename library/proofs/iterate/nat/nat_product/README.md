# nat_product — products of naturals

Products over ℕ are `iterated_op` at natural multiplication. The general
fold laws come from `iterate/monoidal`; this chapter supplies their
reading at ℕ and the consequences that use arithmetic. Sums over ℕ are
the sibling chapter `nat_sum`.

## Definition and recursion

Natural multiplication's neutral is 1 (`NeutralNatMul`), and its
commutativity, associativity and unit laws give `MonoidalNatMul`.

| Member | Statement |
|---|---|
| `NatProductDef` | Natural products are folds at natural multiplication |
| `NatProductClauses` | Empty-set and insertion clauses over ℕ |

## Natural products

| Member | Statement |
|---|---|
| `NatProductConst` | A finite product of c is c to the number of factors |
| `NatProductMonotone` | A product grows with its factors |
| `NatProductUpperBound` | Factors at most c give a product at most c to the number of factors |
| `NatProductLowerBound` | Factors at least c give a product at least c to the number of factors |
| `FactorialProduct` | n! is the product of 1, …, n |

## Counting choices from varying factors

`HasSizeIndexedFunctions` counts maps on a finite index set whose
active coordinates lie in their own finite factors and whose other
coordinates have prescribed values. Adjoining a new index gives one
independent choice from its factor. The empty index set has the unique
prescribed map, so its count and its empty product are both one.

| Member | Statement |
|---|---|
| `HasSizeIndexedFunctions` | The maps on a finite index set J with each active coordinate in its own finite factor X(i) number the product of the card(X(i)) |
