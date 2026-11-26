# polynomial_quotient — the polynomials over a field modulo an ideal, the class of a polynomial as its value at the class of the variable, and modulo an irreducible polynomial a field that holds a root

Kronecker's construction, in the polynomials' own type. Modulo an ideal
`I` of the polynomials over a commutative ring, the class of a
polynomial is its value at the class of the variable, each coefficient
read as the class of its constant (`QuotientClassIsEvaluation`). Over a
field, modulo a proper ideal, the classes of the constants are an
injective copy of the field (`QuotientConstantsEmbed`). An irreducible
`p` generates a maximal ideal (`IrreduciblePrincipalMaximal`), so the
quotient is a field (`quotient_ring.QuotientFieldOn`) whose points are
sets of polynomials; the class of the variable is a root of `p` read
over the copy, and every class is algebraic over the copy
(`QuotientAlgebraicExtension`). algebra/field/algebraic_closure carries
the quotient back into the field's own type to adjoin a root there.

## Modulo an ideal

| member | statement |
|---|---|
| `PolynomialPrincipalIdealDivides` | for `p` over a field `F` and any sequence `r`, `r` lies in the ideal of `p` exactly when `polynomial_divides(field_ring(F), p, r)` |
| `PolynomialQuotientRemainder` | for a nonzero `p` over a field `F` and a polynomial `r`, the class of `r` modulo the ideal of `p` has exactly one representative `u` with `polynomial_over(F.zero, F.carrier, u)` and `vec⟨polynomial_degree(F.zero, p)⟩(F.zero, u)` |
| `IrreduciblePrincipalMaximal` | `polynomial_irreducible(field_ring(F), p) ⇒` the ideal of `p` is maximal in the polynomials over `F` |
| `QuotientClassIsEvaluation` | modulo an ideal `I` of the polynomials over a commutative ring, the class of `f` is `f` evaluated at the class of the variable, each coefficient `a` replaced by the class of the constant `a • basis_vector(0)` |
| `QuotientConstantsEmbed` | modulo a proper ideal of the polynomials over a field, `a ↦` the class of the constant `a • basis_vector(0)` is an injective ring homomorphism |
| `QuotientAlgebraicExtension` | modulo an irreducible `p` over a field `F`, the quotient is a field into which the classes of the constants embed `F` as a ring; the class of the variable lies in it and is a root of `p` with its coefficients read as their constants' classes; and the classes of the constants form a subfield over which every class is algebraic |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
