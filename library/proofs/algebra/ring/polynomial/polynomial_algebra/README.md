# polynomial_algebra — the polynomials in a set of variables over a ring record, finitely supported functions of monomials, the commutative ring they form, an integral domain over a domain, and the descent of ideals along a subfield

A monomial in variables of type `D` is an exponent function `m : D → num`,
zero at all but finitely many variables; `monomials(S)` are those nonzero
only at members of `S`, and the monomial of the constants is the exponent
zero everywhere. A polynomial over a ring record `R : ring_ops(A)` is a
member of the free module on the monomials, `polynomial_algebra(R, S) =
finite_supp(R.zero, R.carrier, monomials(S))`: finitely many nonzero
coefficients, all at monomials of `S`, every coefficient in the carrier
(`PolynomialAlgebraMember`). Polynomials add pointwise
and multiply by the convolution `polynomial_algebra_mul`, whose coefficient
at `m` is the sum of `f(m₁) * g(m − m₁)` over the monomials `m₁` below `m`,
or equally the sum of `f(m₁) * g(m₂)` over the pairs of support monomials
adding up to `m`. Multiplying by a term `c·xⁿ` shifts the coefficients by
`n` and scales them by `c`, so the generators multiply by adding their
monomials. `polynomial_algebra_ring(R, S)` packs these operations with the
polynomials of `S` as a ring record, and its operations do not read `S`.
Over a commutative ring it is a commutative ring, the constants a ring
homomorphism into it and each variable of `S` a polynomial of `S`; a set
holding the constants and closed under sums and under multiplication by
the variables of `S` holds every polynomial of `S`. Over an integral
domain it is an integral domain: two nonzero polynomials involve finitely
many variables; ordered lexicographically along a listing of those, their
monomials have greatest members, and the coefficient of the product at
the sum of the two greatest monomials is the product of the two leading
coefficients, nonzero.

The evaluation of these polynomials in a second ring, and their generation
by the constants and the variables, are `polynomial_algebra_evaluation`'s; their
hosting in a type of one's choosing is `free_algebra`'s.

## Definitions

| member | statement |
|---|---|
| `MonomialsDef` | `monomials(S)` = the finitely supported `m : D → num` nonzero only at members of `S` |
| `MonomialVarDef` | `monomial_var(x) = delta_at(0, 1, x)` |
| `PolynomialAlgebraDef` | `polynomial_algebra(R, S) = finite_supp(R.zero, R.carrier, monomials(S))` |
| `PolynomialAlgebraMulDef` | `polynomial_algebra_mul(R, f, g, m)` = the sum over `m₁ ≤ m` of `f(m₁) * g(m − m₁)` at a finitely supported `m`, `R.zero` elsewhere |
| `PolynomialAlgebraOneDef` | `polynomial_algebra_one(R) = delta_at(R.zero, R.one, λx. 0)` |
| `PolynomialAlgebraConstDef` | `polynomial_algebra_const(R, a) = delta_at(R.zero, a, λx. 0)` |
| `PolynomialAlgebraVarDef` | `polynomial_algebra_var(R, x) = delta_at(R.zero, R.one, monomial_var(x))` |
| `PolynomialAlgebraRingDef` | `polynomial_algebra_ring(R, S)` = the pointwise sum, zero, negation and difference, the product, the one, and the carrier `polynomial_algebra(R, S)` |

## Monomials

| member | statement |
|---|---|
| `MonomialsMember` | an exponent function is a monomial of `S` exactly when it is nonzero at finitely many variables, all of them in `S` |
| `MonomialSupport` | a monomial of `S` is nonzero at finitely many variables, all of them in `S` |
| `MonomialsSubset` | `S ⊆ T` ⇒ the monomials of `S` are monomials of `T` |
| `MonomialVarValues` | `monomial_var(x)` is 1 at `x` and 0 at every other variable |
| `MonomialVarIn` | the monomial of a variable `x` of `S` is a monomial of `S` |
| `MonomialLowerRaise` | `c ≤ m(x)` ⇒ lowering the exponent of `m` at `x` by `c` and raising it again gives `m` back |
| `MonomialAddIn` | the sum of two monomials of `S` is a monomial of `S` |
| `MonomialsBelowFinite` | a finitely supported monomial m has finitely many monomials below it, exponent by exponent |
| `MonomialTriangleSwap` | a finite sum over the monomials `i ≤ k ≤ m` below a finitely supported `m`, grouped by `k`, is the same sum grouped by `i` with `k = i + j` over the `j ≤ m − i`, exponent by exponent |
| `MonomialsOfDegreeCount` | the monomials of degree `d` in the variables `0, …, n` number `binomial(d + n, n)` |
| `MonomialLexOrder` | ordering exponent functions lexicographically along a sequence ι of variables is a strict order that adding a monomial keeps |
| `MonomialLexTrichotomy` | two monomials whose variables ι lists are equal, or one comes before the other in the lexicographic order along ι |
| `MonomialLexGreatest` | a finite nonempty set of monomials whose variables ι lists has a greatest one in the lexicographic order along ι |

## The ring of polynomials

| member | statement |
|---|---|
| `PolynomialAlgebraMember` | a coefficient function is a polynomial of `S` exactly when it is nonzero at finitely many monomials, all of them monomials of `S`, with every coefficient in the carrier |
| `PolynomialAlgebraMulSupport` | a nonzero coefficient of a product at `m` comes from a split `m₁ + (m − m₁)` where both factors are nonzero |
| `PolynomialAlgebraMulSupportInSums` | a product of two coefficient functions valued in the carrier is nonzero only at the sums of a monomial where `f` is nonzero and one where `g` is |
| `PolynomialAlgebraMulPairs` | the coefficient of a product at a finitely supported `m` is the sum of `f(m₁) * g(m₂)` over the pairs of a monomial where `f` is nonzero and one where `g` is with `m₁ + m₂ = m` |
| `PolynomialAlgebraMulIn` | the product of two polynomials of `S` is a polynomial of `S` |
| `PolynomialAlgebraMulComm`, `PolynomialAlgebraMulAssoc`, `PolynomialAlgebraMulDistrib` | on coefficient functions with values in the carrier, polynomials among them, the product is commutative, associative, and distributes over the sum |
| `PolynomialAlgebraTermMul` | multiplying by the term `c·xⁿ` (the coefficient `c` at the monomial `n`) shifts the coefficients by `n` and scales them by `c`: the coefficient at a finitely supported `m` above `n` is `c * f(m − n)`, every other is `R.zero` |
| `PolynomialAlgebraMulOne` | on the polynomials of `S` the one polynomial is a unit for the product |
| `PolynomialAlgebraConstMul` | multiplying a polynomial by the constant polynomial `a` multiplies each coefficient by `a` |
| `PolynomialAlgebraGeneratorMul` | the product of the generators at two finitely supported monomials `m₁`, `m₂` is the generator at `m₁ + m₂` |
| `PolynomialAlgebraCommRingOn` | `polynomial_algebra_ring(R, S)` is a commutative ring on the polynomials of `S` |
| `PolynomialAlgebraLeadingCoefficientMul` | for a strict order on the monomials that adding a monomial keeps, the coefficient of a product at `μ + ν`, μ the greatest monomial where `f` is nonzero and ν the greatest where `g` is, is `f(μ) * g(ν)` |
| `PolynomialAlgebraMulLeadingTerms` | two nonzero polynomials of `S` have monomials μ, ν where they are nonzero, the coefficient of their product at `μ + ν` being `f(μ) * g(ν)` |
| `PolynomialAlgebraDomain` | the polynomials over an integral domain, in any set of variables, are an integral domain |
| `PolynomialAlgebraRingRestrictVariables` | `polynomial_algebra_ring(R, S)` is `polynomial_algebra_ring(R, 𝕌)` restricted to the polynomials of `S`: the operations do not read `S` |
| `PolynomialAlgebraConstHom` | the constants are a ring homomorphism from `R` into the polynomials of `S` |
| `PolynomialAlgebraVarIn` | `x ∈ S` ⇒ the variable `x` is a polynomial of `S` |
| `PolynomialAlgebraSubset` | `S ⊆ T` ⇒ the polynomials of `S` are polynomials of `T` |
| `PolynomialAlgebraOverMono` | `k ⊆ R.carrier` ⇒ the polynomials of `S` over `restrict_ring(R, k)` are polynomials of `S` over `R` |
| `PolynomialAlgebraMulRestrict`, `PolynomialAlgebraOneRestrict`, `PolynomialAlgebraConstRestrict` | the product, the one and the constants over `restrict_ring(R, k)` are those over `R` |
| `PolynomialAlgebraInclusionHom` | `k ⊆ R.carrier`, `R` and `restrict_ring(R, k)` commutative rings ⇒ the polynomials of `S` over `restrict_ring(R, k)` include into those over `R` as a ring homomorphism |
| `PolynomialAlgebraMapHomomorphism` | carrying the coefficients along a ring homomorphism `f` is a ring homomorphism of the polynomial rings; `PolynomialAlgebraInclusionHom` is the case of the inclusion |
| `PolynomialAlgebraMapIsomorphism` | carrying the coefficients along a ring isomorphism is an isomorphism of the polynomial rings |

## The polynomials generated by the constants and the variables

| member | statement |
|---|---|
| `PolynomialInduction` | a set holding the constants, closed under sums and under multiplication by the variables of `S`, holds every polynomial of `S` |

## Descent along a subfield

For a subfield k of L, a polynomial over k that lies in the ideal the
polynomials E over k generate over L already lies in the ideal they
generate over k. The argument runs through the coefficients. A k-linear
map π of L into k, applied coefficient by coefficient, commutes with
multiplication by a polynomial over k (`LinearCoefficientsMul`), so it
carries each ideal combination b·x + w over L, with x in E, to π(b)·x +
π(w) over k, and by induction on a finite part of E it carries the whole
ideal over L into the ideal over k (`IdealLinearDescent`). Any k-linear π
will do: the coordinate functionals of a k-basis of L are the case a
curve's constants need. Taking for π a retraction of L onto k, which
exists because 1 extends to a k-basis of L
(`field_extension.SubfieldRetraction`), π fixes every polynomial over k,
and that is `IdealDescent`.

| member | statement |
|---|---|
| `LinearCoefficientsMul` | a k-linear map of L into k, applied to the coefficients, commutes with multiplication by a polynomial over k: π(f · g) = π(f) · g |
| `LinearCoefficientsConst` | a k-linear map π of L into k, applied to the coefficients, carries the constant β to the constant π(β) |
| `RetractionLinearFactor` | a k-linear map π of L onto k fixing k, applied to the coefficients, carries F − β·G to F − π(β)·G for F and G over k and β in L |
| `IdealLinearDescent` | a k-linear map π of L into a subfield k, applied to the coefficients, carries the ideal that polynomials E over k generate over L into the ideal E generates over k |
| `IdealDescent` | a polynomial over a subfield k in the ideal that polynomials over k generate over L lies in the ideal they generate over k |
| `IdealExtension` | for a subfield `k` of `L`, the ideal polynomials `E` over `k` generate over `k` lies in the ideal they generate over `L` |
