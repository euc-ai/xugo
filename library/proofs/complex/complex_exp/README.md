# complex_exp — the exponential, the cosine and the sine of a complex number, and Euler's formula

The three functions are defined by their power series, as ℝ's are:
`exp(z)` is the sum of $\sum \frac{z^n}{n!}$, `cos(z)` of $\sum \frac{(-1)^n \cdot z^{2n}}{(2n)!}$ and
`sin(z)` of $\sum \frac{(-1)^n \cdot z^{2n+1}}{(2n+1)!}$, each chosen through `complex_sums`
(`complex/complex_series`). The words `exp`, `cos` and `sin` name ℂ's
function at a complex argument and ℝ's at a real one. `z ^ n` is ℂ's power,
the monoid power of its product (`comm_monoid.MonoidPowDef`), which the
chapter binds; the signs and the factorials are reals carried into ℂ by
`complex_of_real`.

The chapter's subject is Euler's formula `exp(i·z) = cos z + i·sin z`,
and the route is the series itself: split the exponential series at
`i·z` by the parity of its index, and the even terms are the cosine's,
the odd ones `i` times the sine's. Neither the Cauchy product nor the
binomial theorem enters.

## The definitions, and the three series converge (definitions.go, series.go)

The size of a quotient is the quotient of the sizes
(`complex_abs.AbsDiv`), and of a power the power of the size
(`complex_abs.AbsPow`), so the size of the exponential's `n`-th term is
`|z|ⁿ/n!`. That is the `n`-th term of ℝ's exponential series at
`|z|`, so the sizes have a sum, and a series whose sizes have a sum has
one (`AbsoluteConvergence`). The cosine's and the sine's terms are, in
size, the even and the odd terms of the same real series. Each is at
most that series' `n`-th pair, and the series of pairs sums to `exp|z|`
(`real_series.SumsPair`). One real series thus bounds both, where ℝ's
own chapter compared each with the exponential series at `x·x`.

| member | statement |
|---|---|
| `ComplexExpDef` | `exp(z) = εs. complex_sums(λn. z ^ n / complex_of_real(&factorial(n)), s)` |
| `ComplexCosDef` | `cos(z) = εs. complex_sums(λn. complex_of_real(real_pow(-&1, n)) * z ^ (2 * n) / complex_of_real(&factorial(2 * n)), s)` |
| `ComplexSinDef` | `sin(z) = εs. complex_sums(λn. complex_of_real(real_pow(-&1, n)) * z ^ (2 * n + 1) / complex_of_real(&factorial(2 * n + 1)), s)` |
| `ExpSums` | the exponential series sums to `exp(z)` |
| `CosSums` | the cosine series sums to `cos(z)` |
| `SinSums` | the sine series sums to `sin(z)` |

## On the real line (real_line.go)

At an embedded real `x`, each of ℂ's series is ℝ's series carried into
ℂ term by term, since the embedding carries quotients, products and
powers (`complex_field.OfRealDiv`, `OfRealMul`, `OfRealPow`). A real
series and its image converge together (`complex_series.SumsOfReal`),
and a series has one sum, so the three functions are ℝ's there. Their
values at 0 follow.

| member | statement |
|---|---|
| `ExpOfReal` | `exp(complex_of_real(x)) = complex_of_real(exp(x))` |
| `CosOfReal` | `cos(complex_of_real(x)) = complex_of_real(cos(x))` |
| `SinOfReal` | `sin(complex_of_real(x)) = complex_of_real(sin(x))` |
| `ExpZero` | `exp(complex_of_real(&0)) = complex_of_real(&1)` |
| `CosZero` | `cos(complex_of_real(&0)) = complex_of_real(&1)` |
| `SinZero` | `sin(complex_of_real(&0)) = complex_of_real(&0)` |

## Euler's formula (euler.go)

`i²ⁿ = (i²)ⁿ = (−1)ⁿ`, so `(i·z)²ⁿ = (−1)ⁿ·z²ⁿ` and `(i·z)²ⁿ⁺¹` is one
more factor `i·z`. The `n`-th pair of the exponential series at `i·z` is
therefore the cosine's `n`-th term plus `i` times the sine's
(`EulerTerm`). The pairs still sum to `exp(i·z)`, while the cosine series
plus `i` times the sine series sums to `cos z + i·sin z`, and a series
has one sum. On the real line the cosine and the sine are ℝ's, so
`exp(i·x)` is the point `(cos x, sin x)` of the unit circle. At `π`,
where the cosine is −1 and the sine 0, it is −1.

| member | statement |
|---|---|
| `IPowEven` | `complex_i ^ (2 * n) = complex_of_real(real_pow(-&1, n))` |
| `EulerTerm` | the `n`-th pair of the exponential series at `i·z` is the cosine's `n`-th term plus `i` times the sine's |
| `Euler` | `exp(complex_i * z) = cos(z) + complex_i * sin(z)` |
| `EulerOfReal` | `exp(complex_i * complex_of_real(x)) = complex_of_real(cos(x)) + complex_i * complex_of_real(sin(x))` |
| `AbsExpIOfReal` | `complex_abs(exp(complex_i * complex_of_real(x))) = &1` |
| `EulerIdentity` | `exp(complex_i * complex_of_real(pi)) + complex_of_real(&1) = complex_of_real(&0)` |

A law of ℂ's ring is read at its instance where a proof needs it
(`comm_ring.MulNegNegOn.Read(complex_field.CommRing)`, `MulLeftNeg`,
`MulRightNeg`, `NegOneMul`), as `complex_field` does. An identity that
is no single law — `EulerTerm`'s product of six factors regrouped,
`SinNeg`'s negated factor in a quotient, the mean and the difference
of `c ± i·s` in `CosExp` and `SinExp` — is stated over variables inside
its member and proved by comparing parts (`complex_field.Parts`). It is
never proved at the site, where computing the parts would also unfold
the operation inside ℂ's power.

## Parity, and the cosine and the sine through the exponential (parity.go)

An even power forgets the sign and an odd power keeps it — the ring's
laws `comm_ring.NegPowEven` and `NegPowOdd`, read at ℂ — so the cosine's
series at `−z` is its series at `z`, and the sine's is −1 times it. With Euler's formula at `z` and at `−z`, `exp(±i·z) = cos z ± i·sin z`.
Their mean is the cosine, and their difference over `2i` is the sine.

| member | statement |
|---|---|
| `CosNeg` | `cos(-z) = cos(z)` |
| `SinNeg` | `sin(-z) = -sin(z)` |
| `CosExp` | `cos(z) = (exp(complex_i * z) + exp(-(complex_i * z))) / complex_of_real(&2)` |
| `SinExp` | `sin(z) = (exp(complex_i * z) - exp(-(complex_i * z))) / (complex_of_real(&2) * complex_i)` |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
