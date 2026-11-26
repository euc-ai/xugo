# algebraic_element — elements algebraic over a subfield, their minimal polynomials, and K(a) = K[a]

An element `a` of the field `L` is algebraic over a subfield `K` when a
nonzero polynomial over `K` vanishes at it, `algebraic_over(L, K, a)`. Its
minimal polynomial `minimal_polynomial(L, K, a)` is chosen among the monic
polynomials over `K` vanishing at `a` of least degree among the nonzero
ones; it meets that specification (`MinimalPolynomialSpec`), has positive degree, divides
over `K` every polynomial over `K` vanishing at `a`, is irreducible over
`K`, and is the one monic irreducible polynomial over `K` vanishing at
`a`. It is a polynomial in the one sense the corpus has, a sequence of
the field's type, whose coefficients happen to lie in `K`. Where a ring of
polynomials over `K` is wanted it is `polynomial_ring` of the ring on `K`:
evaluation at `a` maps it into `K(a)` as a ring homomorphism
(`AdjoinEvaluationHomomorphism`).

The subfield a set generates, `field_adjoin(L, K, S)` — `K(S)` on paper —
is the meet of the subfields of `L` holding `K` and `S`; the field it is
taken in is an argument, as the subfield predicate's carrier is. The values at `a` of the
polynomials over `K`, `polynomial_image(field_ring(L), K, a)` — `K[a]` — form a ring
inside `K(a)`, and for an algebraic `a` already a field, so
`K(a) = K[a]` (`AdjoinEqImage`): the inverse of a nonzero value `p(a)` is
`v(a)` from `u * μ + v * p = 1`, which exists because the minimal
polynomial `μ` is irreducible and does not divide `p`. The powers of `a`
below the degree of `μ` are then a basis of `K(a)` over `K`, so
`[K(a):K] = deg μ`; and an element is algebraic over `K` exactly when
`K(a)` is a finite extension of `K`. Adjoining two algebraic elements one
after the other gives a finite extension by the tower law, so sums,
products and inverses of algebraic elements are algebraic: the elements
algebraic over `K` form a subfield (`AlgebraicElementsSubfield`). A point
algebraic over algebraic points is algebraic: the coefficients of one
polynomial generate a finite extension of `K`, and the point a finite
extension of that (`AlgebraicOverTrans`).

The field record is explicit: under `∀L:field_on(A).` (two such records,
on two types, for a field embedding) the text writes
`algebraic_over(L, K, a)`, `minimal_polynomial(L, K, a)`, `field_adjoin(L, K, S)`
and `polynomial_image(field_ring(L), K, a)`. A point a law reads at is a member of `L.carrier`,
`a ∈ L.carrier`: off the carrier the operations say nothing.

## The definitions

| member | statement |
|---|---|
| `AlgebraicOverDef` | `algebraic_over(L, K, a)` ⇔ some nonzero polynomial over `K` vanishes at `a` |
| `AlgebraicElementsDef` | `algebraic_elements(L, K) = {x \| x ∈ L.carrier ∧ algebraic_over(L, K, x)}`, the algebraic closure of `K` in `L` |
| `MinimalPolynomialDef` | `minimal_polynomial(L, K, a)` = a monic polynomial over `K` vanishing at `a`, of least degree among the nonzero ones, chosen |
| `FieldAdjoinDef` | `field_adjoin(L, K, S) = ⋂{M \| subfield(L, M) ∧ K ⊆ M ∧ S ⊆ M}` |
| `GeneratedSubringDef` | `generated_subring(R, S, E) = ⋂{B \| subring(R, B) ∧ S ∪ E ⊆ B}` |
| `PolynomialImageDef` | `polynomial_image(field_ring(L), K, a) = {polynomial_eval(p, a) \| polynomial_over(K, p)}` |

## The minimal polynomial

| member | statement |
|---|---|
| `MinimalPolynomialSpec` | monic, over `K`, vanishing at `a`, and of least degree among the nonzero polynomials over `K` vanishing at `a` |
| `MinimalPolynomialLeast` | of least degree among the nonzero polynomials over `K` vanishing at `a`, with no `algebraic_over` hypothesis: the `q` it is read at is the witness |
| `MinimalPolynomialPositive` | of positive degree |
| `LeastMonicRelationDivides` | any monic polynomial `g` over a subring `S` of a commutative ring `R`, vanishing at `z` with the least degree among the nonzero polynomials over `S` vanishing there, divides over `S` every polynomial over `S` vanishing at `z` |
| `MinimalPolynomialDivides` | divides over `K` every polynomial over `K` vanishing at `a` |
| `MinimalPolynomialDividesOver` | over a subring `S` of `K` holding its coefficients, divides over `S` every polynomial over `S` vanishing at `a` |
| `MinimalPolynomialIrreducible` | irreducible over `K` |
| `MinimalPolynomialUnique` | the one monic irreducible polynomial over `K` vanishing at `a` |
| `MinimalPolynomialOfDegree` | A monic polynomial over K of degree [K(a) : K] vanishing at a is the minimal polynomial of a |
| `ShortPolynomialsAgree` | Two polynomials over K whose difference vanishes from the degree of the minimal polynomial of a on, with one value at a, are equal |

## K(S), K[a], and K(a) = K[a]

| member | statement |
|---|---|
| `AdjoinSubfield`, `AdjoinLeast` | for `K, S ⊆ L.carrier`, `field_adjoin(L, K, S)` is the least subfield holding `K` and `S` |
| `AdjoinElementSubfield` | for `a ∈ L.carrier`, `field_adjoin(L, K, {a})` is a subfield of `L` holding `K` and `a` |
| `AdjoinElementBetween` | `subfield(L, K) ∧ subfield(L, E) ∧ K ⊆ E ∧ a ∈ E ⇒` `K(a)` is a subfield holding `K` and `a`, and `K(a) ⊆ E` |
| `GeneratedSubringStructure` | for a subring `S` of `L` and `E ⊆ L.carrier`, `generated_subring(field_ring(L), S, E)` is a subring of `L` holding `S` and `E`, and lies in every such subring: the least one |
| `PolynomialImageSubring` | For a coefficient subring `S` of `L` and `x ∈ L`, `S[x]` is a ring holding `S` and `x` inside `L` |
| `PolynomialImageRing` | `K[a]` is a ring holding `K` and `a`, inside `K(a)` and so inside `L` |
| `PolynomialImageLeast` | `polynomial_image(field_ring(L), K, a) ⊆ Q` for every ring `Q` under the field's operations holding `K` and `a`: `K[a]` is the least such ring |
| `AdjoinEvaluationHomomorphism` | `subfield(L, K) ∧ a ∈ L.carrier ⇒` evaluation at `a` is a ring homomorphism from the polynomials over `K` into `K(a)` |
| `CombinationOfPowers` | a combination of finitely many powers `a ^ i` with `i ∈ E`, coefficients in `K` and `i ↦ a ^ i` one-to-one on `E`, is the value at `a` of the polynomial over `K` carrying those coefficients at those exponents (zero elsewhere) |
| `PolynomialValueInSpan` | a polynomial over `K` vanishing from `n` on has its value at `a` in the span over `K` of `{a ^ i \| i < n}`, taken in any ring `M ⊇ K` holding `a` |
| `AdjoinEqImage` | `algebraic_over(L, K, a) ⇒ field_adjoin(L, K, {a}) = polynomial_image(field_ring(L), K, a)` |
| `AdjoinPowerBasis` | the powers of `a` below `deg μ` are a basis of `K(a)` over `K`, and there are `deg μ` of them |
| `AdjoinDegree` | `K(a)` is a finite extension of `K` and `[K(a):K] = polynomial_degree(minimal_polynomial(L, K, a))` |
| `MinimalPolynomialLinearIff` | an algebraic `a` lies in `K` exactly when `polynomial_degree(minimal_polynomial(L, K, a)) = 1` |
| `MinimalPolynomialDegreeDivides` | the minimal polynomial of a point of a finite extension `E/K` has degree dividing `[E : K]` |
| `BoundedPowersDegree` | an element whose powers 1, a, …, a^D lie in a subspace of L of dimension at most D over K is algebraic over K, of degree [K(a) : K] ≤ D |
| `ScaledValueInInverseImage` | For a subring S of L, a nonzero a ∈ L and p over S of degree at most m, a⁻ᵐ · p(a) lies in S[a⁻¹] |

## A transcendental element

| member | statement |
|---|---|
| `EvalInjectiveTranscendental` | `¬algebraic_over(L, K, a)` ⇒ two polynomials over `K` with one value at `a` are equal |
| `TranscendentalPowersIndependent` | `¬algebraic_over(L, K, a)` ⇒ the powers of `a` are distinct and independent over `K` in `L` |
| `TranscendentalSubfieldInfinite` | a subfield `E` holding an element transcendental over `K` is infinite |
| `EvalImageFreeOverK` | `¬algebraic_over(L, K, a)` ⇒ the powers of `a` are distinct and `monoid_powers(L.mul, L.one, a)` is a basis of `K[a]` over `K` |
| `TranscendentalInverse` | a transcendental element is nonzero and its inverse is transcendental |
| `ConstantTranscendental` | an element transcendental over k stays transcendental over a finite extension |

## Finite extensions and the algebraic elements

| member | statement |
|---|---|
| `FiniteExtensionAlgebraic` | every element of a finite extension is algebraic |
| `SquareClosedNoQuadraticExtension` | in characteristic different from two, a subfield in which every element is a square has no finite extension of degree two |
| `AlgebraicIffFinite` | `algebraic_over(L, K, a) ⇔ finite_extension(L, K, field_adjoin(L, K, {a}))` |
| `MemberAlgebraic` | every member `k` of `K` is algebraic over `K`, a root of `x - k` |
| `AlgebraicOverMono` | algebraic over `K`, then over any larger set |
| `AdjoinOfSubset` | `subfield(L, K) ∧ S ⊆ K ⇒ field_adjoin(L, K, S) = K`: adjoining points `K` already holds changes nothing |
| `AdjoinInsert` | for `K, S ⊆ L.carrier` and `a ∈ L.carrier`, `K(insert(a, S)) = K(S)(a)` |
| `FiniteAdjoinStep` | `C` a finite extension of `K` and `x ∈ L.carrier` algebraic over `C` ⇒ `C(x)` is a subfield holding `C` and a finite extension of `K` |
| `AdjoinTwoFinite` | `K(a)(b)` is finite over `K` for algebraic `a`, `b` |
| `FiniteAlgebraicAdjoin` | finitely many elements algebraic over `K` generate a finite extension `K(S)/K` |
| `AdjoinAlgebraicOver` | `subfield(L, B)`, `K ⊆ B`, `S` finite with every point algebraic over `B` ⇒ every point of `K(S)` is algebraic over `B` |
| `AlgebraicElementsSubfield` | `subfield(L, algebraic_elements(L, K))`, holding `K` |
| `AlgebraicOverTrans` | `subfield(L, K)`, `E ⊆ L.carrier` with every point of `E` algebraic over `K`, and `x` algebraic over `E` ⇒ `x` algebraic over `K` |

## Field embeddings

A field embedding is a ring homomorphism `ι` from `field_ring(F)` into
`field_ring(G)`, two fields on carriers of their own types. It is one-to-one
— only zero maps to zero, a nonzero point having an inverse and one mapping
to one — and its image `image(ι, F.carrier)` is a subfield of `G`
(`ring_homomorphism.ImageSubfield`), a copy of `F`. What `F` holds is carried
to that copy: a subfield `S` to the subfield `image(ι, S)`, the field
`field_adjoin(F, K, E)` to the field `image(ι, K)` and `image(ι, E)` generate
in `G`, a finite extension to a finite extension of the same degree, and a
polynomial over a subfield `k`, its coefficients mapped one by one, to a
polynomial over `image(ι, k)` with the same degree, products, values,
derivative and irreducibility. The two fields are never identified: each
statement compares them through images.

A ring map out of a subring `S` extends to `S[z]`, sending `z` to `y`,
when `y` is a root of every relation of `z` over `S` moved along it
(`PolynomialImageLift`): to any point when `z` is transcendental
(`TranscendentalLift`), one-to-one at a point transcendental over the image
of a one-to-one map (`TranscendentalLiftInjective`), and to any root of the
moved `g` when `z` has a monic relation `g` of least degree over `S`
(`HomomorphismExtendsAtRoot`). An embedding of a subfield `K` so extends to
`K(a)`, for an algebraic `a`, at any root of the transported minimal
polynomial (`AdjoinEmbeddingAtRoot`), and that polynomial keeps its degree
and divides every polynomial fixed by the embedding that vanishes at `a`
(`TransportedMinimalPolynomial`).

| member | statement |
|---|---|
| `FieldEmbeddingPreimageSubfield` | `ring_homomorphism(field_ring(F), field_ring(G), ι)` and `subfield(G, H)` ⇒ `subfield(F, preimage_on(F.carrier, ι, H))`: the preimage of a subfield of the target is a subfield of the source |
| `FieldEmbeddingSubfieldsAdjoin` | `ring_homomorphism(field_ring(F), field_ring(G), ι)` ⇒ `ι` is one-to-one on `F.carrier`, carries each subfield `S` of `F` to a subfield `image(ι, S)` of `G`, and `image(ι, field_adjoin(F, K, E)) = field_adjoin(G, image(ι, K), image(ι, E))` for `K, E ⊆ F.carrier` |
| `FieldEmbeddingFiniteDegree` | for a field embedding `ι` and subfields `k ⊆ K` of `F` with `K` finite over `k`, `image(ι, K)` is finite over `image(ι, k)` and `extension_degree(G, image(ι, k), image(ι, K)) = extension_degree(F, k, K)` |
| `PolynomialImageLift` | a ring map `ε` out of a subring `S` extends to `S[z]`, sending `z` to `y`, when `y` is a root of every polynomial over `S` vanishing at `z`, its coefficients moved along `ε` |
| `TranscendentalLift` | a ring map out of a subring `k` extends to `k[t]`, sending `t` to any `x`, for `t` transcendental over `k` |
| `TranscendentalLiftInjective` | a ring map `φ` on `k[t]` that agrees on `k` with a one-to-one ring map `ε` into a field `T` and sends `t` to `x` transcendental over `image(ε, k)` is one-to-one on `k[t]` |
| `HomomorphismExtendsAtRoot` | a ring map `e` out of a subring `S` of a commutative ring extends to `S[z]` at a root of the image of a monic relation `g` of `z` over `S` of least degree |
| `AdjoinEmbeddingAtRoot` | an embedding `f` of `K` into a field `T` extends to `K(a)` sending an algebraic generator `a` to a root `b` in `T` of its transported minimal polynomial |
| `TransportedMinimalPolynomial` | an embedding of `M` into `L` fixing `K` carries the minimal polynomial of `a` over `M` to a polynomial over `L` of the same degree dividing, in `L`'s polynomial ring, every polynomial over `K` vanishing at `a` |
| `FieldEmbeddingPolynomials` | for a field embedding `ι` and `p` over a subfield `k` of `F`, the coefficients mapped, `λi. ι(p(i))`, are a polynomial over `image(ι, k)` of the same degree, zero exactly when `p` is, taking products to products, the value at `x` to the value at `ι(x)` and the derivative to the derivative |
| `TransportOddDegreeRootsIsomorphism` | odd-degree roots are carried along a ring isomorphism onto any field |
| `FieldEmbeddingIrreducible` | an irreducible polynomial over a subfield `k` remains irreducible over `image(ι, k)` when its coefficients are carried along a field embedding |
| `FieldEmbeddingMonic` | for a field embedding `ι` and `S ⊆ F.carrier`, a monic polynomial `p` over `S` maps to a monic polynomial `λi. ι(p(i))` over `image(ι, S)` |
| `FieldEmbeddingDivides` | for a field embedding `ι` and `h` over `F.carrier`, `h` dividing `g` over `F` gives `λi. ι(h(i))` dividing `λi. ι(g(i))` over `G` |
| `PolynomialsOverRestriction` | Polynomials evaluate by the operations alone, so the polynomial image is the same in a restricted field |
| `AdjoinInverse` | k(1/t) is k(t) |
| `AdjoinInSubfield` | Adjoining to k inside a subfield K of M or inside M gives one field |
| `RestrictFieldReadings` | A restricted field reads polynomial images and algebraicity as the field does |
