# real_sqrt — the square root

`real_sqrt(x)` is the y whose sign is the sign of x and whose square is |x|. On
the nonnegative reals that is the usual nonnegative root; asking the sign to
match totalizes it as an odd function, which is a reading of the definition
rather than anything the chapter proves. The choice is justified once, by the
chapter's existence theorem: for every x such a y exists, which for positive x
is the completeness of ℝ at work — the nonnegative reals whose square is at
most x have a least upper bound, and that bound squares to x.

Every other law reads off the existence theorem and the uniqueness of the
nonnegative root, but for the product law, which holds at every sign: a
real is fixed by its sign and its square. Uniqueness is the chapter's
working tool: it identifies a root from a nonnegative value and its square,
and it is what carries the root's monotonicity, so no member here states
monotonicity itself.

## The definitional layer (definitions.go)

| constant | reading |
|---|---|
| `real_sqrt(x)` | `εy. real_sgn(y) = real_sgn(x) ∧ y² = \|x\|` |

## The members (sqrt.go, definitions.go)

| member | statement | stands on |
|---|---|---|
| `Works` | `real_sgn(real_sqrt(x)) = real_sgn(x) ∧ real_pow(real_sqrt(x), 2) = real_abs(x)` — the definition's choice is not vacuous | `SquareRootExists` |
| `SquareRootExists` | `&0 < y ⇒ ∃r. real_pow(r, 2) = y` — the chapter's existence theorem: the least upper bound of the nonnegative reals whose square is at most y (completeness) squares to y, its square being neither below y nor above it | `ApproachFromBelow`, `ApproachFromAbove` — the two approximation lemmas (a real whose square is under y is not the largest such; a positive real whose square is over y is not the smallest such) |
| `SqrtUnique` | `x = real_pow(y, 2) ⇒ &0 ≤ y ⇒ y = real_sqrt(x)` — the other side of `Works`: on the nonnegative half the root is not merely *a* choice but the only one, so a value known to be nonnegative and to square to x IS the root. Every later law that identifies a root reads off this | `SqrtPowTwo` and `SqrtNonneg` — the two halves of `Works` it needs — together with the fact that squares compare exactly as the sizes of their bases do (`real_pow.AbsLessEqIffPowTwoLessEq`), read in both directions |
| `SqrtPowTwo` | `&0 ≤ x ⇒ real_pow(real_sqrt(x), 2) = x` — reads off `Works` (`real_sqrt(x)² = \|x\|`) and the abs law for a nonnegative real | `Works` |
| `SqrtNonneg` | `&0 ≤ x ⇒ &0 ≤ real_sqrt(x)` — the root has the sign of x (`Works`), and a nonnegative x has sign &1 or &0, either of which leaves the root nonnegative | `Works` |
| `SqrtPos` | `&0 < x ⇒ &0 < real_sqrt(x)` — the root is nonnegative and squares back to x | `SqrtNonneg`, `SqrtPowTwo` |
| `SqrtOfPow` | `&0 ≤ x ⇒ real_pow(real_sqrt(x), m) = real_sqrt(real_pow(x, m))` — the power of the root is nonnegative and squares back to the power of x | `SqrtUnique`, `SqrtPowTwo`, `SqrtNonneg` |
| `SqrtMul` | `real_sqrt(x) * real_sqrt(y) = real_sqrt(x * y)` — for every x and y, the root being odd: the product has the sign and the square of `real_sqrt(x * y)`, and two reals with one sign and one square are equal | `Works`, `real_sgn_abs.SgnMul` and `real_sgn_abs.AbsMul` |
| `SqrtLowerBound` | `real_pow(x, 2) ≤ y ⇒ x ≤ real_sqrt(y)` — the order law: x is a lower bound for the root exactly when x² is one for the radicand. x is not assumed nonnegative and need not be, since the hypothesis already puts y above a square, so the root is nonnegative and settles a negative x outright | `SqrtPowTwo`, `SqrtNonneg`, and `real_pow.AbsLessEqIffPowTwoLessEq` |
| `SqrtZero` | `&0 = real_sqrt(&0)` — one application of `SqrtUnique` at zero; a uniqueness fact, not a definitional one, since the choice alone does not say which root it named |

## The approximation lemmas (approach.go)

The existence theorem needs completeness at one point only: that the set of
reals whose square is below a positive y has a least upper bound whose
square is y itself. What makes that supremum's square land exactly on y is
that the set has no greatest element and its complement no least — a value
squaring below y can always be nudged up and one squaring above y nudged
down without crossing y. These lemmas are those nudges, stated as
approximations and proved by exhibiting the nudged witness explicitly.

| law | statement |
|---|---|
| `ApproachFromBelow` | `x² < y ⇒ ∃z. x < z ∧ z² < y` — a value under y is not the largest such |
| `ApproachFromAbove` | `&0 < x ∧ &0 < y ∧ y < x² ⇒ ∃z. z < x ∧ &0 < z ∧ y < z²` — a positive value over y is not the smallest such: step down from x by the smaller of x/2 and $\frac{x^2 - y}{2x}$ |
