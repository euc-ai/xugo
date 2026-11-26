# rational_function_field — the rational function field k(t), Gauss's lemma and plane equations over it

For t transcendental over k, k is algebraically closed in k(t), and in the
fractions of the polynomials over a field the variable is transcendental, so
every field K embeds in an algebraically closed field holding a point
transcendental over its image: the algebraic closure of K(x). A polynomial in T and Z is read at
a point t row by row (`gauss.go`): Gauss's lemma makes a monic polynomial
irreducible over k[T], read at a transcendental t, the minimal polynomial over
k(t) of each of its roots, and an absolutely irreducible equation over a
perfect k gives a regular function field k(t)(z) (`absolutely_irreducible.go`).
Transcendentals exchange (`transcendence.go`): a regular function field is
algebraic over k(t) for every t in it transcendental over k.

## The rational function field and its closure

| Member | Statement |
|---|---|
| `FractionVariableTranscendental` | In the fractions of the polynomials over a field, the variable is transcendental over the constants |
| `FunctionFieldClosure` | Every field K embeds, by a ring homomorphism, in an algebraically closed field holding a point transcendental over the image of K: the algebraic closure of K(x) |

## Plane equations over the rational function field

| Member | Statement |
|---|---|
| `MonicRowsAtPoint` | A monic polynomial over k[T], its rows read at a point t, is a monic polynomial over k[t] of the same degree |
| `RowsLift` | A polynomial over k[t] is the reading at t of a polynomial over k[T] of the same degree |
| `GaussMinimalPolynomial` | Gauss's lemma: a monic polynomial irreducible over k[T], read at a transcendental t, is the minimal polynomial over k(t) of each of its roots |
| `RowsDerivativeNonzero` | A polynomial over k[T] with nonzero derivative in Z keeps a nonzero derivative read at a transcendental t |
| `RationalFunctionConstants` | k is algebraically closed in k(t) for t transcendental over k |
| `AbsolutelyIrreducibleRegular` | For k perfect, F monic over k[T] and irreducible over k̄[T], k̄ the elements of M algebraic over k, t transcendental and z a root of F(t, Z): F(t, Z) is the minimal polynomial of z over k(t), and k(t)(z) is a regular function field over k |

## The exchange of transcendentals

| Member | Statement |
|---|---|
| `AlgebraicExchange` | If t is transcendental over k and algebraic over k(s), then s is algebraic over k(t) |
| `AlgebraicOverAnyTranscendental` | A regular function field is algebraic over k(t) for every t in it transcendental over k |
