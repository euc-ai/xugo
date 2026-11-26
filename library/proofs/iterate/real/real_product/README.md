# real_product — products of reals

Products over ℝ are `iterated_op` at real multiplication. The general
fold laws come from `iterate/monoidal`; this chapter supplies their
reading at ℝ and the consequences that use arithmetic. Real
multiplication inherits its monoidal facts from `real_ring`. Sums over ℝ
are the sibling chapter `real_sum`.

## Definition and recursion

| Member | Statement |
|---|---|
| `RealProductDef` | Real products are folds at real multiplication |
| `ProductClauses` | Empty-set and insertion clauses over ℝ |

## Real products

| Member | Statement |
|---|---|
| `ProductZero` | A finite product with a zero factor is zero |
| `RealOfNatProduct` | A finite product of naturals cast into ℝ is the product of the casts |
| `Congruence` | two functions equal on the index set have the same product |
| `Pointwise` | a finite product of pointwise products is the product of the two products |
| `Diff` | a finite product splits at a subset of its index set, the product off it times the product over it |
| `EqOne` | a product whose factor is 1 at every index is 1 |
| `Superset` | enlarging the index set leaves a product unchanged when the factor is 1 at every added index |
| `Restrict` | a product over the indices of s where P holds is the product over s with the factor silenced to 1 where P fails |
| `Sing` | a product over one index is its factor there |
| `Delete` | a finite product is the factor at one of its indices times the product over the others |
| `Union` | a product over two disjoint finite index sets is the product of the two products |
| `Swap` | two finite products exchange |
| `ProductOfHalves` | the product of the f(v)/2 over a finite set is the product of the f(v) over 2 to the number of factors |
| `ProductSquareOne` | a product of reals that each square to one squares to one |
| `Nonneg` | a product of nonnegative reals is nonnegative |
| `ProductConst` | the product of one real c over a finite set is c to the set's size |
| `SubsetProductsSum` | the sum over the subsets of a finite set of the products of b over them is the product of the 1 + b(u) |
| `ProductOfBinomials` | a finite product of binomials a(v) + b(v) is the sum, over the subsets S that take b, of the product of a off S and of b on S — card |
