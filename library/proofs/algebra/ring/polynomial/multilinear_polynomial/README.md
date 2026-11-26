# multilinear_polynomial — multilinear representation on a finite Boolean cube

A subset $X$ of a finite variable set $U$ specifies the Boolean point with ones
on $X$ and zeros elsewhere. At that point the squarefree monomial indexed by
$T$ evaluates to one if $T\subseteq X$ and zero otherwise. A coefficient
family $c$ therefore evaluates to the sum of $c(T)$ over all subsets of $X$.

Every function $f$ on the cube has a unique multilinear representative over
any commutative unital ring. Its coefficient at $S\subseteq U$ is

$$
c(S)=\sum_{T\subseteq S}(-1)^{|S\setminus T|}f(T).
$$

The ring may have a proper carrier. The hypotheses ask for $f(T)$ to lie in
`R.carrier` on subsets of $U$. A normalized coefficient family takes values
in the carrier there and vanishes outside the subsets of $U$.
`MultilinearRepresentation` characterizes that family by equality with the
alternating formula extended by zero.

## Inversion and uniqueness

| Member | Mathematical role |
|---|---|
| `MultilinearEvalDef` | Defines `multilinear_eval(R, c, X)` as the ring sum over subsets of $X$. |
| `MultilinearCoeffDef` | Defines `multilinear_coeff(R, f, S)` by the alternating subset sum. |
| `MultilinearCoeffIn` | Shows that the coefficient belongs to the ring when the values below $S$ do. |
| `MultilinearEvalEmpty`, `MultilinearCoeffEmpty` | Identify the constant coefficient and the value at the all-zero point. |
| `MultilinearEvalInsert` | Splits an evaluation according to whether the index subset contains the fresh variable. |
| `MultilinearCoeffInsert` | Adjoining a fresh variable $x$ to a monomial takes the coefficient of the finite difference $f(T\cup\lbrace x\rbrace)-f(T)$. |
| `MultilinearReconstruction` | Evaluating the alternating coefficients gives back $f$. |
| `MultilinearEvalInjective` | Proves that equal evaluations imply equal coefficients on the cube. |
| `MultilinearRepresentation` | Gives existence and uniqueness with the coefficients normalized outside the cube. |

## Evaluation in the polynomial algebra

`squarefree_exponent(T)` is the exponent vector with ones on $T$.
`cube_ring_point(R, X)` assigns ring elements zero and one to the variables.
`squarefree_polynomial(R, U, c)` is the ordinary coefficient function on
exponent vectors. It selects the specified coefficient at each squarefree
exponent supported in $U$ and assigns zero to all other exponents.

| Member | Mathematical role |
|---|---|
| `squarefreeExponentDef`, `cubeRingPointDef`, `SquarefreePolynomialDef` | Define the exponent vector, evaluation point, and polynomial. |
| `SquarefreeExponentSupport`, `SquarefreeMonomials` | Recover $T$ as the support of its exponent and embed subsets of finite $U$ in its monomials. |
| `SquarefreeMonomialEval` | Computes the ordinary monomial evaluation by testing $T\subseteq X$. |
| `SquarefreePolynomialCoefficient`, `SquarefreePolynomialSupport` | Identify the coefficient at each indexed monomial and bound the support. |
| `SquarefreePolynomialIn` | Places the resulting polynomial in `polynomial_algebra(R, U)`. |
| `SquarefreePolynomialEval` | Identifies `polynomial_algebra_eval` at the Boolean point with `multilinear_eval`. |
