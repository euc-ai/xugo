# polynomial — polynomials over a ring on a set, as sequences of coefficients

A polynomial is a sequence `p : num → A` of coefficients, the coefficient
of `x ^ i` at `i`, that is zero from some index on: an `n`-vector of the
vector chapter for some `n`. `polynomial_over(c, p)` says it is one with
every coefficient in `c`, under a ring `R` its carrier `R.carrier`
(called `c` below). The polynomials over a
subring `K ⊆ c` are polynomials over `c` as they stand — the same
sequences, a stronger predicate — so there is one kind of polynomial per
type and never a ring of polynomials per subring, nor a map carrying the
polynomials over `K` into those over `c`.

The vector chapter's pointwise operations are the polynomials' sum,
negation, difference and scaling, and they keep their notation: `p + q`,
`-p`, `p - q`, `a • p`. The product is new: `polynomial_mul(p, q)` is the
convolution, its `n`-th coefficient the sum of `p(i) * q(n - i)` over
`i ≤ n`, folded by the module chapter's finite sum so that a ring on a
set suffices. It is spelled by name: a `*` declared on it would be read
first at every `*` whose operands are of a type variable, and break the
statements of a structure that binds `mul` but not `add`. The vector chapter's standard basis vector
`basis_vector(k)` is the `k`-th power of the variable — `basis_vector(0)`
the one polynomial, `basis_vector(1)` the variable `x`, and
`polynomial_mul(basis_vector(j), basis_vector(k)) = basis_vector(j + k)` — so a constant
is `a • basis_vector(0)` and `x - a` is `basis_vector(1) - a • basis_vector(0)`.
The polynomials of degree below `n` are the `n`-vectors with coefficients
in `c`, an `n`-dimensional vector space over a field
(`PolynomialsBelowDim`).

The degree is the index of the last nonzero coefficient, zero for the
zero polynomial (`polynomial_degree`); over an integral domain degrees
add, a nonzero scalar keeps the degree, and the polynomials form an
integral domain. The formal derivative (`polynomial_derivative`) is
additive, obeys the product rule and the power rule, and keeps
polynomials over a subring.

Four chapters build on this one. `polynomial_evaluation` evaluates a
polynomial at a point, a ring homomorphism from the polynomials over `c`
to `c`; `polynomial_division` divides over a field and by a monic
polynomial over any ring, with Bézout's identity, Euclid's lemma and
coprimality; `polynomial_roots` splits off the roots, at most the degree
many over a domain; and `separable_polynomial` holds splitting,
separability and the Mason–Stothers theorem.

The ring of polynomials is the record `polynomial_ring(R)`, the vector
operations, the convolution and `basis_vector(0)` on the polynomials
over `R.carrier`; the module is the record value
`mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul, …)` over `R`.
The predicates of the chapters above — divisibility, irreducibility,
coprimality, splitting and separability — take the ring record,
`polynomial_divides(R, p, q)`;
the operations take components, and the components are implicit: under
a law over a ring `R` the text writes `polynomial_over(R.carrier, p)`,
`polynomial_degree(p)`, `polynomial_eval(p, x)`, completed from the
record by field name; a statement with no ring spells the zero.

## The definitions

| member | statement |
|---|---|
| `PolynomialOverDef` | `polynomial_over(c, p)` ⇔ `p` is an `n`-vector for some `n` with every coefficient in `c` |
| `PolynomialMulDef` | `polynomial_mul(p, q)(n)` = the sum of `p(i) * q(n - i)` over `i ≤ n` |
| `PolynomialDegreeDef` | `polynomial_degree(p)` = the least `d` with `p` zero past `d` |
| `PolynomialMonicDef` | `polynomial_monic(p)` ⇔ the coefficient at the degree is `one` |
| `PolynomialDerivativeDef` | `polynomial_derivative(p)(n) = (n + 1) · p(n + 1)` |
| `PolynomialPowDef` | `polynomial_pow(p, n)` = the `n`-th power of `p` under `polynomial_mul`, `basis_vector(0)` at `n = 0` |
| `PolynomialRingDef` | `polynomial_ring(R) = mk_ring(vec_add(R.add), vec_zero(R.zero), vec_neg(R.neg), polynomial_mul(R.add, R.zero, R.mul), basis_vector(R.zero, R.one, 0), vec_sub(R.sub), {p \| polynomial_over(R.zero, R.carrier, p)})` |

## The ring and the module

| member | statement |
|---|---|
| `PolynomialRingOn` | `comm_ring_on(R) ⇒ comm_ring_on(polynomial_ring(R))` |
| `SeriesMulIn` | the convolution of two sequences with every term in `c` has every term in `c` |
| `PolynomialMulOver` | the product of polynomials over `c` is a polynomial over `c` |
| `PolynomialMulComm`, `PolynomialMulAssoc`, `PolynomialOneMul`, `PolynomialMulDistrib`, `PolynomialMulSub` | the convolution product of sequences with every term in `c`, polynomials or not, is commutative and associative, distributes over `+` and `-`, and has `basis_vector(0)` as its identity |
| `PolynomialMulLeftComm`, `PolynomialMulDistribLeft`, `PolynomialMulSubLeft` | so its first two factors interchange, `polynomial_mul(p, polynomial_mul(q, r)) = polynomial_mul(q, polynomial_mul(p, r))`, and it distributes over `+` and `-` in the left factor |
| `PolynomialModuleOn` | `comm_ring_on(R) ⇒ module_on(R, mk_module(vec_add, vec_zero, vec_neg, vec_scalar_mul, {p \| polynomial_over(R.carrier, p)}))` |
| `CoefficientIn` | `polynomial_over(c, p) ⇒ p(i) ∈ c` |
| `PolynomialOverMono` | `K ⊆ c ∧ polynomial_over(K, p) ⇒ polynomial_over(c, p)` |
| `PolynomialOverMap` | mapping the coefficients of a polynomial over `c` along `f`, with `f(z) = w` and `f` sending `c` into `d`, gives a polynomial over `d`: `polynomial_over(z, c, p) ⇒ polynomial_over(w, d, λi. f(p(i)))` |
| `PolynomialPullBack` | A polynomial over the image of a set under a map one-to-one on it is the image of a polynomial over the set. |
| `VecMap` | a map with `f(z) = w` keeps a vector's length: `vec⟨n⟩(z, p) ⇒ vec⟨n⟩(w, λi. f(p(i)))` |
| `PolynomialMapNonzero` | a map injective on `c` keeps a polynomial over `c` nonzero: `polynomial_over(z, c, p) ∧ z ∈ c ∧ injective_on(c, f) ∧ f(z) = w ∧ p ≠ vec_zero(z) ⇒ (λi. f(p(i))) ≠ vec_zero(w)` |
| `PolynomialFiniteSupport` | a sequence is a polynomial over k exactly when finitely many terms are nonzero, all in k |
| `BasisVectorOver`, `VecZeroOver` | the powers of the variable and the zero polynomial are polynomials over `c` |
| `BasisVectorMul` | the powers of the variable multiply by adding exponents |
| `PolynomialPowZero` | the zeroth power is the one polynomial: `polynomial_pow(p, 0) = basis_vector(0)` |
| `PolynomialPowSuc` | the next power multiplies by p once more: `polynomial_pow(p, suc(n)) = polynomial_mul(p, polynomial_pow(p, n))` |
| `VarPow` | the powers of the variable are the basis polynomials: `polynomial_pow(basis_vector(1), n) = basis_vector(n)` |
| `PolynomialPowOver` | a power of a polynomial over `c` is over `c` |
| `PolynomialMulAtZero` | the constant coefficient of a convolution product of sequences with every term in `c` is the product of their constant coefficients: `polynomial_mul(p, q, 0) = p(0) * q(0)` |
| `ConvolutionRingMap` | a ring homomorphism carries the convolution of two sequences with every term in its source's carrier to the convolution of their images |
| `PolynomialMulBasisVector` | multiplying a sequence with every term in `c` by `basis_vector(s)` shifts its terms up by `s`: `polynomial_mul(p, basis_vector(s), j) = COND(s ≤ j, p(j - s), R.zero)` |
| `BinomialConvolution` | multiplying a sequence f with every term in `c` by the binomial `basis_vector(0) - c • basis_vector(d)` gives at n the term `f(n) - c * f(n - d)`, the subtracted term present from n = d on |
| `PolynomialExpansion` | an `n`-vector over `c` is the sum of `p(i) • basis_vector(i)` over the indices below `n` |
| `PolynomialsBelowDim` | over a field, the polynomials of degree below `n` have dimension `n` — card |
| `PolynomialMulScalar` | a scalar `a` in `c` comes out of a convolution product of sequences with every term in `c`: `polynomial_mul(p, a • q) = a • polynomial_mul(p, q)` |
| `PolynomialMulConstant` | multiplying by a constant is scaling: `polynomial_mul(p, a • basis_vector(0)) = a • p` |
| `ConstantPolynomialHomomorphism` | taking each element to its constant polynomial is a ring homomorphism: `ring_homomorphism(R, polynomial_ring(R), λa. a • basis_vector(0))` |

## Convolution of sequences of naturals

`polynomial_mul(λi j. i + j, 0, λi j. i * j)` multiplies sequences of naturals as power series (the chapter's «natConv», written ⋆ below). ℕ is no ring, so the laws above do not apply to it, and its left-commutativity is proved in ℕ's finite sums: at n both sides sum the products p(i)·q(j)·r(n − i − j) over the triangle i + j ≤ n, padded with zero to the square i, j ≤ n, and they sum that square in its two orders.

| member | statement |
|---|---|
| `NatPolynomialMulSum` | the n-th coefficient of the convolution of two sequences of naturals is $\sum_{i \le n} p(i) \cdot q(n-i)$ |
| `NatPolynomialMulLeftComm` | the convolution of sequences of naturals is left-commutative: p ⋆ (q ⋆ r) = q ⋆ (p ⋆ r) |

## The degree

| member | statement |
|---|---|
| `DegreeVec`, `DegreeLeast` | `p` vanishes past its degree, and the degree is the least such bound |
| `DegreeVecZero` | `polynomial_degree(vec_zero) = 0` |
| `DegreeBelow` | a nonzero sequence that vanishes from `n` on has degree below `n` |
| `VecOfDegreeBelow` | a polynomial that is zero or of degree below `n` vanishes from `n` on |
| `TruncateBelow` | truncating a polynomial below a positive `n` leaves a polynomial of degree below `n` |
| `TruncationImage` | a map that keeps zero and kills the leading coefficient of `q` sends `q` and its truncation below its degree to the same sequence |
| `DegreeExact` | a polynomial vanishing past `n` with `p(n) ≠ zero` has degree `n` |
| `DegreeLeading` | a nonzero polynomial's coefficient at its degree is nonzero |
| `LeadingCoefficientNonzero` | the leading coefficient `p(polynomial_degree(p))` of a nonzero polynomial over `c` lies in `c` and is nonzero |
| `FirstNonconstantTerm` | a polynomial of positive degree has a first nonzero coefficient at a positive index |
| `DegreeZeroIff` | degree zero is constant |
| `DegreeZeroConstant`, `MonicDegreeZero` | a polynomial of degree zero is the constant `p(0) • basis_vector(0)`, and a monic one is `basis_vector(0)` |
| `MonicNonzero` | over an integral domain a monic polynomial is not `vec_zero` |
| `DegreeBasisVector` | `R.one ≠ R.zero ⇒ polynomial_degree(basis_vector(k)) = k` |
| `LeadingCoefficientMul` | the coefficient of `polynomial_mul(p, q)` at the sum of the degrees is the product of the leading coefficients |
| `PolynomialMulVec` | the degree bound of a product, stated by vanishing: `p` vanishing past `m` and `q` past `n`, `polynomial_mul(p, q)` vanishes past `m + n` |
| `DegreeMulLe` | the degree of a product is at most the sum of the degrees |
| `LeadingCoefficientMulNonzero` | over an integral domain, for nonzero `p` and `q` the coefficient of `polynomial_mul(p, q)` at the sum of the degrees is not zero |
| `DegreeMul` | over an integral domain degrees add |
| `PolynomialDomain` | over an integral domain the polynomials form a domain |
| `DegreeScalar` | over an integral domain a nonzero scalar keeps the degree |
| `MonicMultiple` | over a field, `F.inv(p(polynomial_degree(p))) • p` is a monic polynomial over `c` of `p`'s degree, for nonzero `p` over `c` |
| `DegreePow` | over an integral domain, `polynomial_degree(polynomial_pow(p, n)) = n * polynomial_degree(p)` |

## The derivative

The derivative's coefficient at `n` is the ring's numeral `suc(n)`, the
sum of `suc(n)` ones, spelled `«numeral»(suc(n))` from the chapter's
abbreviation table, times `p(suc(n))`.

| member | statement |
|---|---|
| `DerivativeAdd` | additivity of the derivative, for any two sequences with every term in `c` |
| `DerivativeVecZero` | the derivative of the zero polynomial is zero |
| `DerivativeSub` | the derivative of a difference is the difference of the derivatives, for any two sequences with every term in `c` |
| `DerivativeConstant` | the derivative of a constant `a • basis_vector(0)`, `a` in `c`, is zero |
| `DerivativeMul` | the product rule, for any two sequences with every term in `c` |
| `DerivativeOver` | the derivative of a polynomial over a subring is over it |
| `DerivativeOverCarrier` | the derivative of a polynomial over `c` is over `c` |
| `DerivativeVec` | the derivative vanishes from the degree on, in every characteristic |
| `DerivativeScalar` | a scalar comes out of the derivative of a sequence with every term in `c` |
| `DerivativePow` | the derivative of `polynomial_pow(p, suc(n))` is `n + 1` times `polynomial_mul(polynomial_pow(p, n), polynomial_derivative(p))` |
| `PowDerivativeZero` | over an integral domain, a power of zero derivative whose exponent is not zero in the ring has a base of zero derivative — card |
