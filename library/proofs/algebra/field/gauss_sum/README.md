# gauss_sum — the quadratic Gauss sum over a field holding a p-th root of unity, its square and its Frobenius image

Let ζ ≠ 1 be a p-th root of unity, p an odd prime, in a field (its
characteristic is then not p). The quadratic Gauss sum $g = \sum_{a<p} \left(\frac{a}{p}\right) \zeta^a$
reads each Legendre symbol through the integers' map into the field. Its
square is $\left(\frac{-1}{p}\right) \cdot p$, and in characteristic q the q-th power map is a ring
homomorphism carrying g to $\left(\frac{q}{p}\right) \cdot g$; comparing the two with Euler's
criterion mod q gives the law of quadratic reciprocity, in
int_num/quadratic_reciprocity, which computes in an algebraically closed
field of characteristic q holding such a ζ
(`roots_of_unity.ClosedFieldOfCharacteristic`,
`roots_of_unity.RootOfUnityInClosedField`).

## Members

| Member | Statement |
|---|---|
| `GaussSumDef` | `gauss_sum`: field_ops(A) → A → num → A |

## The twisted sum and the Frobenius image

When p does not divide k, $\left(\frac{ak}{p}\right) = \left(\frac{a}{p}\right)\left(\frac{k}{p}\right)$ and $\left(\frac{k}{p}\right)^2 = 1$ give
$\left(\frac{a}{p}\right) = \left(\frac{k}{p}\right) \cdot \left(\frac{ak \bmod p}{p}\right)$. Since a ↦ ak mod p permutes the residues
below p, the twisted sum $\sum_{a<p} \left(\frac{a}{p}\right) \zeta^{ak}$ is $\left(\frac{k}{p}\right)$ times the Gauss sum.
When p divides k both sides are zero, because the symbols sum to zero. In
characteristic q the q-th power map is additive and fixes the image of
every integer, so it carries g to the twisted sum at q.

| Member | Statement |
|---|---|
| `TwistedGaussSum` | For a p-th root of unity ζ, p an odd prime, the twisted sum $\sum_{a<p} \left(\frac{a}{p}\right) \zeta^{ak}$ is $\left(\frac{k}{p}\right)$ times the Gauss sum |
| `GaussSumFrobenius` | In characteristic q, the q-th power of the Gauss sum is $\left(\frac{q}{p}\right)$ times the Gauss sum |

## The square of the Gauss sum

Multiply g by itself term by term and read each $\left(\frac{a}{p}\right) \cdot g$ as a twisted
sum: g² becomes the double sum $\sum_b \left(\frac{b}{p}\right) \sum_a \zeta^{a(b+1)}$. The inner power
sum is p when p divides b + 1 and zero otherwise. Below p only b = p − 1
has p dividing b + 1, and $\left(\frac{p-1}{p}\right) = \left(\frac{-1}{p}\right)$.

| Member | Statement |
|---|---|
| `GaussSumSquareDoubleSum` | For a p-th root of unity ζ, p an odd prime, the square of the Gauss sum is $\sum_{b<p} \left(\frac{b}{p}\right) \cdot \sum_{a<p} \zeta^{a(b+1)}$ |
| `GaussSumSquare` | For a p-th root of unity ζ ≠ 1, p an odd prime, the square of the Gauss sum is $\left(\frac{-1}{p}\right) \cdot p$ |
