# polynomial_roots — the factor theorem, the roots of a polynomial and their number, root multiplicity and derivatives of linear-factor powers, and the monic polynomial vanishing on a finite set

The roots of a polynomial, the linear factor that splits each off and
their number over a domain are below. A finite set of points of a domain
is the zero set of exactly one monic polynomial of degree its size, the
product of its linear factors, which every endomorphism of the domain
permuting the set fixes. Coprime polynomials over a field share no root,
and finitely many nonzero polynomials over a subfield have a nonzero
common multiple at a point. A pseudo-remainder vanishes with the dividend
at the roots of the divisor's image under a homomorphism into a field that
keeps the divisor's leading coefficient (`PseudoRemainderRoots`).
Multiplying by `x − c` takes differences of shifted
coefficients, and weighting the coefficients by the powers of `b` turns
the factor `x − c` into `x − c · b`.

## The definitions

| member | statement |
|---|---|
| `PolynomialRootsDef` | `polynomial_roots(c, p)` = the points `x ∈ c` with `polynomial_eval(p, x)` zero |

## Roots

The roots of `p` in a set `c` are `polynomial_roots(c, p)`, the points
of `c` at which `polynomial_eval(p, x)` is zero; `c` is any set of
points, so the roots in a subfield `M` of a field `L` are
`polynomial_roots(M, p)` under `L`. `x - a` is `«linear»(a)`, an entry of
the chapter's abbreviation table. Over any commutative ring, `a ∈ c` is a root
of `p` exactly when `x - a` divides `p`: `x - a` is monic, so monic
division by it leaves a constant remainder, the value of `p` at `a`.
Over an integral domain the quotient of a nonzero `p` by `x - a` is
nonzero and one lower in degree, and the roots of `p` are `a` with the
roots of the quotient; so a nonzero polynomial has at most its degree
many roots.

| member | statement |
|---|---|
| `LinearFactor` | `x - a` is a monic polynomial over `c` of degree at most one, whose value at `y` is `y - a` and so zero at `a`, and of degree one when one is not zero |
| `LinearFactorMap` | a ring map `ι`, applied to the coefficients, carries `x − a` to `x − ι(a)` |
| `FactorTheorem` | over any commutative ring, `polynomial_eval(p, a) = R.zero ⇔ x - a divides p` |
| `DegreeZeroNoRoots` | a nonzero polynomial of degree zero has no roots: `polynomial_roots(c, p) = ∅` |
| `RootFactorization` | over a domain, a root `a` of a nonzero `p` gives `p = polynomial_mul(x - a, q)` with `q` nonzero, `polynomial_degree(p) = suc(polynomial_degree(q))` and `polynomial_roots(c, p) = insert(a, polynomial_roots(c, q))` |
| `IrreducibleRootLinear` | an irreducible polynomial over an integral domain with a root in that domain has degree one |
| `RootBound` | over a domain, a nonzero `p` has at most `polynomial_degree(p)` roots in `c` |
| `PolynomialCommonMultiple` | over a subfield `k`, finitely many nonzero polynomials `p(s)`, `s ∈ E`, with a nonzero `a`, have a nonzero common multiple `c` at `t`: `c(t) = p(s)(t) · q(t)`, `q` over `k` |
| `CoprimeNoCommonRoot` | over a field, coprime polynomials share no root |

## Pseudo-division at a root

| member | statement |
|---|---|
| `PseudoDivisionValueAtRoot` | a pseudo-division `cᵉ f = g·s + r` over the source `R` of a ring homomorphism `σ` into a field keeping `c`, the leading coefficient of `g`, read at a root `x` of `σg`: `σcᵉ` is a nonzero element of the field and `σcᵉ·σf(x) = σr(x)`; `R` is a commutative ring as the source of `σ` |
| `PseudoRemainderRoots` | over a commutative ring, the pseudo-remainder of `f` by `g`, with no coefficient from `deg g` on, vanishes with `f` at the roots of `g`, under every homomorphism into a field that keeps `g`'s leading coefficient |

## The monic polynomial vanishing on a finite set

| member | statement |
|---|---|
| `MonicVanishingPolynomial` | A finite part of a domain has a monic polynomial of its size vanishing on it |
| `MonicVanishingUnique` | That polynomial is unique |
| `MonicVanishingFixed` | An endomorphism moving S onto S fixes the monic polynomial vanishing on S |

## Linear factors and rescaling

| member | statement |
|---|---|
| `LinearConvolution` | the coefficient of `(x − c)·p` at `n` is `p(n − 1) − c·p(n)` |
| `RescaledLinearFactor` | weighting the coefficients of `(x − c)·p` by $b^{m+1-i}$ gives `(x − c·b)` times `p` weighted by $b^{m-i}$ |

## Multiplicity and derivatives

A root of a nonzero polynomial over a domain splits off its linear factor to its full multiplicity, and the derivative of a product of linear-factor powers keeps one power less of each factor.

| member | statement |
|---|---|
| `RootMultiplicity` | over a domain, a root `a` of a nonzero `p` splits off `x − a` to its full multiplicity: $p = (x-a)^{m+1} \cdot s$ with `s(a) ≠ 0`, and the roots of `p` are `a` and the roots of `s` |
| `LinearFactorDerivative` | the derivative of `x − a` is the one polynomial |
| `LinearPowerDerivative` | the derivative of $(x-a)^{m+1} \cdot g$ is $(x-a)^m \cdot \bigl((m+1) \cdot g + (x-a) \cdot g'\bigr)$ |
| `LinearPowersDerivative` | the derivative of $(x-a)^{m+1} \cdot (x-b)^{n+1} \cdot s$ is $(x-a)^m \cdot (x-b)^n$ times $(m+1) \cdot (x-b) \cdot s + (x-a) \cdot \bigl((n+1) \cdot s + (x-b) \cdot s'\bigr)$ |
