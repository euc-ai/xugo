# polynomial_division — division with remainder, divisibility, Bézout's identity, irreducible polynomials and coprimality

Over a field on `c` a polynomial divides by a nonzero one with a unique
quotient and a remainder of lower degree; over any commutative ring the
same holds for a monic divisor, and any divisor divides the dividend once
it is scaled by a power of the divisor's leading coefficient
(pseudo-division), whose remainder decides divisibility over a field.
Divisibility `polynomial_divides(R, p, q)` is reflexive and transitive and
passes to a larger carrier, and over a field a divisor of a nonzero
polynomial has at most its degree.

Over a field two polynomials not both zero have a monic common divisor
that is a combination of them, Bézout's identity; an irreducible
polynomial `polynomial_irreducible(R, p)` that does not divide another
is coprime to it, which gives Euclid's lemma, and every polynomial of
positive degree has an irreducible factor. Two polynomials are coprime
over `c` when a combination of them by polynomials over `c` is the one
polynomial, `polynomial_coprime(R, p, q)`: Bézout's identity taken as
the definition, as for the integers, so that coprimality asks for no
greatest common divisor and its laws hold over any ring.

The predicates take the ring record, `polynomial_divides(R, p, q)`; the
operations take components, as in the polynomial chapter.

Every division here is written one way: the dividend `f` bound before
the divisor `g`, the divisor as the product's first factor,
`f = polynomial_mul(g, q) + r` as in `polynomial_divides`, and the
remainder `r` with `vec⟨polynomial_degree(g)⟩(r)`, vanishing from the
divisor's degree on, which for a polynomial is `r` zero or of degree
below `g` (`polynomial.VecOfDegreeBelow`, `polynomial.DegreeBelow`).
The chapter's table names the four conditions `«division»(c, f, g, q, r)`:
`q` and `r` over `c`, `r` vanishing from the degree of `g` on, and
`f = polynomial_mul(g, q) + r`; the chapters that read this table spell
a division the same way, except where a proof has named the divisor's
degree and bounds the remainder at that name.

## The definitions

| member | statement |
|---|---|
| `PolynomialDividesDef` | `polynomial_divides(R, p, q)` ⇔ `q = polynomial_mul(p, r)` for some `r` over `R.carrier` |
| `PolynomialIrreducibleDef` | `polynomial_irreducible(R, p)` ⇔ `p` over `R.carrier` of positive degree with a factor of degree zero in every factorization over `R.carrier` |

## Pseudo-division over rings

Any divisor admits division over a commutative ring once the dividend is
scaled by a power of the divisor's leading coefficient: each step cancels
the dividend's top coefficient for one more factor of that coefficient, so
no inverse is needed and the ring may have zero divisors.

| member | statement |
|---|---|
| `LeadingTermCancel` | over a commutative ring, subtracting the right monomial multiple of g from the dividend scaled by g's leading coefficient removes the dividend's coefficient at a support bound |
| `PseudoDivision` | over a commutative ring, the leading coefficient of g to the power suc(deg f) − deg g, times f, is g times a quotient plus a remainder vanishing from the degree of g on |

## Monic division over rings

A monic polynomial admits division with a unique remainder over any
commutative ring: its leading coefficient is one, so no inverse of a
coefficient is needed. The division is pseudo-division's, above, at
leading coefficient one, which scales the dividend to itself.
`MonicLeadingTermCancel` is pseudo-division's cancellation step at a
monic divisor, a member for lookup: the division reads `PseudoDivision`,
not it.

| member | statement |
|---|---|
| `MonicLeadingTermCancel` | subtracting the right monomial multiple of a monic divisor removes the dividend's coefficient at a support bound |
| `MonicDivisionExists` | division by a monic polynomial leaves a remainder vanishing from its degree on |
| `MonicDivisionUnique` | two such decompositions by a monic divisor have the same quotient and remainder |
| `MonicDivisionAlgorithm` | over a commutative ring, a monic divisor gives a unique quotient and a remainder vanishing from its degree on |

## Division over a field

Over a field, a nonzero `g` is a unit times a monic polynomial of its
degree: scaled by the inverse `a` of its leading coefficient it is monic
(`MonicAssociate`). Dividing by `g` is then dividing by the monic `a • g`:
division with remainder and the uniqueness of its quotient and remainder
are monic division's, above, read through that scaling.

| member | statement |
|---|---|
| `MonicAssociate` | over a field, a nonzero `g` has a nonzero `a` in `c` with `a • g` monic of `g`'s degree |
| `DivisionExists` | over a field, `f = polynomial_mul(g, q) + r` with `r` vanishing from the degree of `g` on |
| `DivisionUnique` | the quotient and remainder are unique |

## Divisibility over any ring

| member | statement |
|---|---|
| `DividesTrans` | divisibility is transitive |
| `DividesRefl` | every polynomial over `c` divides itself |
| `DividesMono` | a divisor over `K ⊆ c` is a divisor over `c` |

## Divisibility over a field

| member | statement |
|---|---|
| `DividesDegree` | a divisor of a nonzero polynomial has at most its degree |
| `PolynomialBezout` | a monic common divisor `d = polynomial_mul(u, f) + polynomial_mul(v, g)` |
| `IrreducibleCoprime` | an irreducible `p` that does not divide `f`: some combination of `p` and `f` over `c` is the one polynomial |
| `IrreducibleDividesProduct` | Euclid's lemma |
| `IrreducibleFactorExists` | over a field, a polynomial of positive degree has an irreducible factor |

## Coprime polynomials

Coprimality is Bézout's identity taken as the definition: `p` and `q`
are coprime over `c` when `polynomial_mul(u, p) + polynomial_mul(v, q)`
is the one polynomial for some `u` and `v` over `c`. Each law below is
then ring algebra on such combinations, and holds over any commutative
ring on `c`.

| member | statement |
|---|---|
| `PolynomialCoprimeDef` | `polynomial_coprime(R, p, q)` ⇔ `polynomial_mul(u, p) + polynomial_mul(v, q) = basis_vector(0)` for some `u`, `v` over `c` |
| `CoprimeSymm` | coprimality is symmetric |
| `CoprimeDividesProduct`, `CoprimeProductDivides` | a divisor of `polynomial_mul(q, r)` coprime to `q` divides `r`; coprime divisors of `w` have their product dividing `w` |
| `CoprimeDivisor` | divisors of coprime polynomials are coprime — card |
| `CoprimeSum` | `p` is coprime to `q` exactly when it is coprime to `p + q` |
| `CoprimeAddMultiple` | adding a multiple of `p` keeps a polynomial coprime to `p` |
| `CoprimeMono` | coprime over `K ⊆ c` is coprime over `c` |
| `CoprimeMul` | a product of two polynomials coprime to `r` is coprime to `r` |
| `CoprimePow` | powers of coprime polynomials are coprime — card |

## The pseudo-remainder over a field

Over a field the remainder of a pseudo-division decides divisibility: the
power of the leading coefficient that scales the dividend is invertible.

| member | statement |
|---|---|
| `PseudoRemainderDivides` | over a field, when `cᵏ f = g·s + r` with `c` nonzero and `r` vanishing from the degree of `g` on, `g` divides `f` exactly when `r` is zero |
