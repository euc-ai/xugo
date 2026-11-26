# separable_polynomial — splitting, separability and the Mason–Stothers theorem

A polynomial splits over `R`, `polynomial_splits(R, p)`, when each of its
irreducible factors is linear, and it is separable,
`polynomial_separable(R, p)`, when it is coprime over `R` to its
derivative. A divisor of a polynomial that splits splits, a product of
polynomials that split splits, and a polynomial of positive degree that
splits has a root. A divisor of a separable polynomial is separable, a
product of coprime separable polynomials is separable, a ring
homomorphism applied to the coefficients keeps a polynomial separable, and
an irreducible polynomial is separable exactly when its derivative is not
zero. In characteristic zero its leading derivative coefficient cannot
vanish, so every irreducible polynomial is separable. The roots of a separable
polynomial are simple, so a separable polynomial that splits has as many roots as its degree, and the product
of the linear factors at a finite set of points is separable and splits,
with exactly those points as its roots. At two distinct roots a and b of
a nonzero polynomial over a domain, the value of its derivative at a is
a multiple of a − b.

On coprimality and the derivative stands the Mason–Stothers theorem,
over a field and in every characteristic, read off the Wronskian
`polynomial_wronskian(p, q)` of two polynomials, with Fermat's equation
for polynomials and Davenport's bound as its corollaries.

## The derivative at two roots

| member | statement |
|---|---|
| `DerivativeAtRootFactors` | For roots a ≠ b of a nonzero polynomial over a domain, a − b divides the derivative at a |

## Splitting and separability

A polynomial splits over `c` when each of its irreducible factors over
`c` is linear, `polynomial_splits(R, p)`, and it is separable over `c`
when some combination of it and its derivative over `c` is the one
polynomial, `polynomial_separable(R, p)`. The first asks for no product
over a list of roots, the second for no field in which to look for
repeated roots: both are said by divisibility over `c` alone. Every
irreducible polynomial divides the zero polynomial, so the zero
polynomial splits only over a field whose irreducible polynomials are
all linear; the laws ask for nonzero polynomials where it matters.

| member | statement |
|---|---|
| `PolynomialSplitsDef` | `polynomial_splits(R, p)` ⇔ every irreducible `q` over `c` dividing `p` has degree one |
| `PolynomialSeparableDef` | `polynomial_separable(R, p)` ⇔ `polynomial_mul(u, p) + polynomial_mul(v, polynomial_derivative(p)) = basis_vector(0)` for some `u`, `v` over `c` |
| `SplitsDivisor` | a divisor of a polynomial that splits splits |
| `SplitsRoot` | over a field, a polynomial of positive degree that splits has a root in `c` |
| `SplitsMul` | over a field, a product of two polynomials that split splits |
| `SplitsMono` | a nonzero polynomial over a subfield `K` that splits over `K` splits over `c` — card |
| `SeparableDivisor` | a divisor of a separable polynomial is separable |
| `SeparableMul` | over a commutative ring, a product of coprime separable polynomials is separable |
| `DistinctLinearProduct` | over a field, the product of the linear factors `x - a` over a finite `S` is over the field, separable and split, has root set exactly `S`, and is coprime to `x - a` at each point of the field off `S` |
| `SeparableMono` | separable over `K ⊆ c` is separable over `c` |
| `SeparableCoefficientMap` | a ring homomorphism `f` applied to every coefficient keeps a polynomial over `c` separable: `polynomial_separable(S, λi. f(p(i)))` |
| `SeparableIffDerivative` | over a field, an irreducible polynomial is separable ⇔ its derivative is not zero |
| `CharZeroIrreducibleSeparable` | An irreducible polynomial over a characteristic-zero subfield is separable |
| `SeparableRootSimple` | over a field, a root of a separable polynomial is simple: the derivative does not vanish there |
| `SeparableNonzero` | over a field, a separable polynomial is nonzero |
| `SeparableFactorsShareNoRoot` | over a field, the two factors of a separable product share no root in `c` |
| `SeparableSplitsRoots` | over a field, a separable polynomial that splits has exactly `polynomial_degree(p)` roots in `c` |
| `SeparableCoprime` | a polynomial is separable exactly when it is coprime to its derivative |

## The Mason–Stothers theorem

The Wronskian of two polynomials is `p q' − p' q`, written
`polynomial_wronskian(p, q)`. Three of its properties give the theorem by
Snyder's argument. It does not change when one argument is added to the
other, so `p`, `q` and `p + q` have one Wronskian between any two of them.
A common divisor of `p` and `p'` divides the Wronskian of `p` with any
polynomial. And it vanishes from `deg p + deg q` on, while for coprime `p`
and `q` not both of zero derivative it is not zero. So for coprime `p`
and `q`, divisors `d` of `p` and `p'`, `e` of `q` and `q'`, and `f` of
`p + q` and its derivative are pairwise coprime and have their product
dividing a nonzero polynomial whose degree is below the degree sum of any
two of `p`, `q` and `p + q`.

The theorem is stated for such divisors rather than for the radical.
`p` divided by its radical is one such `d`, in every characteristic, and
taking it and its like for `e` and `f` gives the classical form: the
largest of the three degrees is below the degree of the radical of
`p q (p + q)`. The divisor form needs no factorization into irreducibles,
and it is the form the corollaries use. Fermat's equation takes the
`(n − 1)`-th powers of `x`, `y` and `z` as the divisors: for `n ≥ 3` not
zero in the field, `x^n + y^n = z^n` with `x` and `y` coprime forces `x`,
`y` and `z` to have zero derivative. The hypothesis on `n` is not idle:
in a field of characteristic `n`, `t^n + 1 = (t + 1)^n`. Davenport's bound
takes the divisors `g`, `1` and `f²` of `g²`, `f³ − g²` and `f³`.

| member | statement |
|---|---|
| `PolynomialWronskianDef` | `polynomial_wronskian(p, q)` = `polynomial_mul(p, q') - polynomial_mul(p', q)`, the prime the derivative |
| `WronskianOver`, `WronskianSum` | the Wronskian of polynomials over `c` is over `c`, and `W(p, p + q) = W(p + q, q) = W(p, q)` — card |
| `WronskianDivisor`, `WronskianVec` | a common divisor of `p` and `p'` divides `W(p, q)` and `W(q, p)`; `W(p, q)` vanishes from `deg p + deg q` on — card |
| `WronskianNonzero` | over a field, coprime `p` and `q` not both of zero derivative have a nonzero Wronskian — card |
| `WronskianDivisorProduct` | for coprime `p`, `q`, divisors `d` of `p`, `p'`, `e` of `q`, `q'`, `f` of `p + q` and its derivative have `polynomial_mul(polynomial_mul(d, e), f)` dividing `W(p, q)` — card |
| `MasonStothers` | over a field, with `p`, `q`, `d`, `e`, `f` as above and `p`, `q` not both of zero derivative, `deg d + deg e + deg f` is below `deg p + deg q`, `deg p + deg(p + q)` and `deg q + deg(p + q)` — card |
| `FermatPolynomial` | for `n ≥ 3` not zero in the field, `polynomial_pow(x, n) + polynomial_pow(y, n) = polynomial_pow(z, n)` with `x`, `y` coprime gives `x`, `y`, `z` of zero derivative — card |
| `DavenportCoprime` | for coprime `f`, `g` with `f' ≠ 0`, in a field where `3` is not zero, `deg f + 2 ≤ 2 · deg(f³ − g²)` — card |
