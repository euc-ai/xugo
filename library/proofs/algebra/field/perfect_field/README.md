# perfect_field — perfect fields, read through the p-th power map

A field is perfect when every irreducible polynomial over it is separable
(`PerfectFieldDef`). In characteristic p this is read through the p-th power
map: a surjective p-th power map makes a field perfect, by the p-th root of a
polynomial with zero derivative; the degree of a p-th root over a subfield
gives the converse; the map keeps the degree of a finite extension, so a
finite extension of a perfect field is perfect, and a finite field is. The
characteristic and the p-th power map are finite_field's, and so are the facts
about them that ask nothing of perfectness: a power of the characteristic is a
ring endomorphism (`finite_field.FrobeniusRingHomomorphism`, read here at the
power p¹) and a subfield holds the p-th powers of its points
(`finite_field.PowersInsideSubfield`).

## Definitions

| Member | Statement |
|---|---|
| `PerfectFieldDef` | `perfect_field`: field_ops(A) → bool |

## Members

| Member | Statement |
|---|---|
| `ZeroDerivativeCoefficients` | Over a field of characteristic p, a polynomial with zero derivative has its coefficients on the multiples of p |
| `PolynomialFrobenius` | In characteristic p the p-th power of a polynomial is the polynomial in x ^ p of the p-th powers of its coefficients |
| `PolynomialPthRoot` | Over a field of characteristic p whose elements are all p-th powers, a polynomial with its coefficients on the multiples of p is the p-th power of a polynomial |
| `FrobeniusSurjectivePerfect` | A field of prime characteristic p in which every element is a p-th power is perfect |
| `FiniteExtensionPerfect` | A finite extension of a perfect field is perfect |
| `PrimeRootDegree` | In characteristic p, an element outside a subfield P whose p-th power lies in P has degree exactly p over P |
| `PerfectFrobeniusSurjective` | In a perfect field of characteristic p every element is a p-th power |
| `FrobeniusImageDegree` | In characteristic p the p-th power map carries a finite extension of subfields to a finite extension of the same degree |
| `PerfectSubfieldPowers` | In characteristic p a perfect subfield is its own p-th powers |
| `FiniteFieldIsPerfect` | A finite field is perfect: every irreducible polynomial over it is separable |
