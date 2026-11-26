# polynomial_evaluation — the value of a polynomial at a point, a ring homomorphism, and its transport along ring maps

The value of a polynomial `p` at a point `x` is the sum of
`p(i) * x ^ i` over its support, `polynomial_eval(p, x)`; it may be read
over any segment past the support, so it is the sum of the terms through
the degree. At a point of `c` evaluation is additive and multiplicative,
takes `a • p` to `a * polynomial_eval(p, x)`, the `k`-th power of the
variable to `x ^ k` and a constant to itself, and keeps values in `c`:
it is a ring homomorphism from the polynomials over `c` to `c`. At zero a
polynomial takes its constant coefficient, at one the sum of its
coefficients. Evaluation turns a division `f = g q + r` into an identity
between values, and at a root of `g` the value of `f` is that of `r`.

A ring homomorphism carries the value of a polynomial at a point to the
value of the mapped polynomial at the image of the point, and moving
coefficients along it is a homomorphism of polynomial rings, which
evaluation at a point of the target turns into a homomorphism out of the
polynomials over the source. Moving coefficients takes `c • p` to `f(c)`
times the moved `p`, commutes with the derivative, and takes a division
`c • p = g q + r` to the division of the moved polynomials. Every polynomial is its own value at the
variable, its coefficients read as constant polynomials; translating or
rescaling the argument gives another polynomial; and the coefficients of
a polynomial in two variables give one value in either order of
evaluation.

The operations take the ring's components implicitly, as in the
polynomial chapter: under a law over a ring `R` the text writes
`polynomial_eval(p, x)`, completed from the record by field name.

## The definitions

| member | statement |
|---|---|
| `PolynomialEvalDef` | `polynomial_eval(p, x)` = the sum of `p(i) * x ^ i` over the indices where `p` is not zero |
| `OddDegreeRootsDef` | `odd_degree_roots(F)`: every polynomial of odd degree over the field has a root in it |

## Evaluation

| member | statement |
|---|---|
| `EvalHomomorphism` | evaluation at `x ∈ c` is a ring homomorphism to `c` |
| `EvalAlongHomomorphism` | a ring homomorphism `f` sends the value of `p` at `x` to the value at `f(x)` of the polynomial of the images of `p`'s coefficients |
| `EvalTranslate` | translating the argument gives another polynomial: for `a ∈ c` some `q` over `c` has `polynomial_eval(q, w) = polynomial_eval(p, a + w)` at every `w ∈ c` |
| `EvalAtVar` | every polynomial over `c` is its own value at the variable, its coefficients read as constants: `λi. f(i) • basis_vector(0)` evaluated in `polynomial_ring(R)` at `basis_vector(1)` is `f` |
| `EvalBelow` | an `n`-vector's value at `x` is the sum of `p(i) * x ^ i` over the indices below `n` |
| `EvalBelowDegree` | a polynomial's value at `x` is the sum of `p(i) * x ^ i` over the indices below the successor of its degree |
| `EvalAtZero` | a polynomial over `c` takes its constant coefficient at zero: `polynomial_eval(p, R.zero) = p(0)` |
| `EvalFirstTermExpansion` | when `p(k)` is nonzero and the coefficients strictly between `0` and `k` vanish, the value at `z ∈ c` is `p(0)` plus the term at `k` plus the sum of the terms past `k` |
| `EvalOneBelow` | an `n`-vector's value at one is the sum of its coefficients below `n` |
| `EvalOneSupport` | a sequence with every term in `c` takes at one the sum of its terms over its support: `polynomial_eval(p, R.one) = module_sum(R.add, R.zero, {i \| p(i) ≠ R.zero}, p)` |
| `EvalVecTwo` | a polynomial vanishing from index two on takes the value `p(0) + p(1) * x` at every point `x` of `c` |
| `EvalVecThree` | a polynomial vanishing from index three on takes the value `p(0) + p(1) * x + p(2) * (x * x)` at every point `x` of `c` |
| `EvalAdd`, `EvalMul`, `EvalScalar`, `EvalBasisVector` | at `x ∈ c`, evaluation of polynomials over `c` is additive and multiplicative, takes `a • p` to `a * polynomial_eval(p, x)` for `a ∈ c`, and takes `basis_vector(k)` to `x ^ k` |
| `EvalSub` | at `x ∈ c`, evaluation of polynomials over `c` takes `p - q` to `polynomial_eval(p, x) - polynomial_eval(q, x)` |
| `BinomialValue` | at `x ∈ c`, the binomial `basis_vector(0) - c • basis_vector(d)` takes the value `R.one - c * x ^ d` |
| `EvalPow` | at `x ∈ c`, the value of a power of a polynomial over `c` is the power of its value: `polynomial_eval(polynomial_pow(p, n), x) = monoid_pow(R.mul, R.one, polynomial_eval(p, x), n)` |
| `EvalConstant` | the constant `k • basis_vector(0)` takes the value `k` at every point of `c` |
| `DegreeZeroEval` | a polynomial of degree zero takes its constant coefficient as its value at every point of `c` |
| `EvalVecZero` | the zero polynomial takes the value zero at every point of `c` |
| `EvalMulRoot` | a root of `p` is a root of `polynomial_mul(p, q)` and of `polynomial_mul(q, p)` |
| `DivisionValue` | at `x ∈ c`, `f = polynomial_mul(g, q) + r` gives `polynomial_eval(f, x) = polynomial_eval(g, x) * polynomial_eval(q, x) + polynomial_eval(r, x)` |
| `DivisionValueAtRoot` | at a root `x ∈ c` of `g`, `f = polynomial_mul(g, q) + r` gives `polynomial_eval(f, x) = polynomial_eval(r, x)` |
| `EvalIn` | a polynomial over `c` takes its values at points of `c` in `c` |
| `CoefficientMapHomomorphism` | applying a ring homomorphism to every coefficient is a homomorphism of the polynomial rings |
| `CoefficientMapScalar` | applying a ring homomorphism `f` to every coefficient takes `c • p` to `f(c) • (λi. f(p(i)))` |
| `CoefficientMapDerivative` | applying a ring homomorphism `f` to every coefficient commutes with the derivative: `λi. f(polynomial_derivative(p, i))` is `polynomial_derivative(λi. f(p(i)))` |
| `CoefficientMapDivision` | applying a ring homomorphism `f` to every coefficient takes a division `c • p = polynomial_mul(g, q) + r` to `f(c) • fp = polynomial_mul(fg, fq) + fr`, `fp` the polynomial of the images of `p`'s coefficients |
| `TransportedEvaluationHomomorphism` | Moving a polynomial along a ring map and evaluating at w is a homomorphism |
| `MappedEvaluationHomomorphism` | Moving coefficients along f and evaluating at y is a ring map out of R[X] extending f and sending the variable to y |
| `EvalRescaled` | for `p` over `c` of degree at most `n` and `s, x ∈ c`, the polynomial with coefficients `s ^ (e(n − i)) * p(i)` up to `n` takes at `s ^ e * x` the value `s ^ (en) * polynomial_eval(p, x)` |
| `EvalAtScaledPoint` | at `s, x ∈ c`, the value of `p` at `s * x` is the value at `x` of `p` with its `i`-th coefficient weighted by `s ^ i` |
| `EvalTwoVariables` | a polynomial in two variables, its coefficients zero from row `m` and from column `n` on, takes one value at `(x, y)` whichever variable is evaluated first |
| `GeometricFactorization` | for d > 0, `basis_vector(0) - basis_vector(1)` and the geometric sum `λn. COND(n < d, R.one, R.zero)` are polynomials over `c`, their product is `basis_vector(0) - basis_vector(d)`, and the geometric sum takes at one the numeral d |
| `PolynomialProductData` | over a subfield `k` of a field, a product of polynomials over `k` is over `k`, nonzero when both factors are, and evaluates to the product of the values |
