# algebraic_closure — the algebraic closure of a field, built once in a host type fixed by the field's type, and the splitting fields inside an algebraically closed field

A field `M` is algebraically closed, `algebraically_closed_field(M)`, when
every polynomial of positive degree over its carrier has a root there.
The rest of algebra/field works inside one field, or compares two through
the images of a field embedding (algebraic_element), and builds an
extension only where a field already holds it. This chapter builds an
algebraically closed algebraic extension once, and reads it as the
ambient field of the other constructions: a statement over a closed
field is a statement about sets of its carrier, a splitting field among
them.

Over a field `K` on a type `A`, the closure is a field on the host
`set(prod(num, num → A))`. The choice of host is the whole cardinal
argument. Write `B = num → A`. The host is `set(prod(num, B))`, so the
cardinal chapter's encodings hold in it at the inner type `B`: a
sequence of its points is one point (`cardinal.SequencesIntoPowerSet`),
so is a pair of them (`cardinal.PairsIntoPowerSet`), and so a set of
its points smaller than all of them leaves room for all of them outside
it (`cardinal.ComplementRoom`). A field algebraic
over a copy of `K` is no larger than the pairs of a sequence of `A` and
an index (`AlgebraicExtensionBound`): a point is a root of a polynomial
over `K`, and one of finitely many. Those pairs are `prod(num, B)` up to
the swap, strictly below the host by Cantor. So every field of the host
that is algebraic over the copy of `K` has room off its carrier for all
its polynomials (`AlgebraicExtensionRoom`). `K` itself enters by
`a ↦ {(0, λn. a)}`, transported (`ring_transport.TransportFieldOn`).

`field_extends(F, G)` says that `G`'s carrier holds `F`'s and that the
eight operations of the two records agree on `F`'s carrier. A record is
a set of total maps, so off `F`'s carrier nothing is compared, and the
relation is a preorder, not an order (`FieldExtendsPreorder`); Zorn's
lemma asks no more. An extension holds the smaller carrier as a subfield
(`FieldExtendsSubfield`), and evaluates every polynomial over it as the
smaller field does, so algebraicity over a fixed set passes both ways
(`FieldExtendsEval`). A chain of fields under it unites to a record,
`chain_union_field(c)`, whose carrier is the union and whose operation
at given points is that of a member holding them, chosen
(`ChainUnionExtends`); a nonempty chain of fields algebraic over one set
unites to such a field (`ChainUnionFieldOn`). Zorn's lemma then gives
every field an extension on its own type that is maximal among its
algebraic extensions (`MaximalAlgebraicExtension`).

A root is adjoined in the field's own type. The polynomials over a field
`F` modulo an irreducible `p` are a field whose points are sets of
polynomials, holding a copy of `F` and a root of `p`, every point
algebraic over the copy (algebra/field/polynomial_quotient). With room
off `F`'s carrier for the polynomials, an injection that sends each
constant's class to the constant and the other classes off the carrier
carries the quotient back into the type (`RootAdjunctionInHost`). The composite of the
constants' embedding and the injection fixes `F`'s carrier, so the new
record extends `F` (`FixedFieldEmbeddingExtends`); the root travels
with the injection as a ring homomorphism does
(`polynomial_evaluation.EvalAlongHomomorphism`), and algebraicity with it
(`AlgebraicOverTransport`).

The maximal algebraic extension of the copy of `K` in the host is
closed (`AlgebraicClosureInHost`). A polynomial of positive degree over
it has an irreducible factor; there is room off the carrier to adjoin
that factor's root, in an extension algebraic over the maximal field and
so over the copy of `K`; maximality brings the root back into the
maximal field, and a root of the factor is a root of the polynomial.
Read as a field with `K` inside it, this is the algebraic closure
(`AlgebraicClosureFieldOn`). Over a closed field every polynomial
splits (`ClosedFieldSplits`), and a nonzero polynomial over a subfield
`K` has its splitting field inside: the field `K` generates
with the polynomial's roots, finite over `K` and below every subfield
holding `K` over which the polynomial splits (`SplittingFieldInClosed`).
Inside the closure a finite separable extension of an infinite field is simple
(`PrimitiveElement`).

## Definitions

| member | statement |
|---|---|
| `AlgebraicallyClosedDef` | `algebraically_closed_field(F)` ⇔ every polynomial of positive degree over `F.carrier` has a root in `F.carrier`; no field axiom is part of it |
| `fieldExtendsDef` | `field_extends(F, G)` ⇔ `F.carrier ⊆ G.carrier` and the zero, the one and the six other operations of `F` and `G` agree on `F.carrier` |
| `chainUnionFieldDef` | `chain_union_field(c)`: the carrier `⋃{F.carrier \| F ∈ c}`, each operation at given points that of a member of `c` holding them, chosen |

## An algebraically closed field as a structure

A statement about one closed field holds it as the structure's
hypothesis and reads the field and the roots off it;
`algebraically_closed_field(F)` is the root axiom alone, for a statement
that states the field beside it.

| member | statement |
|---|---|
| `AlgebraicallyClosedFieldOn` | `algebraically_closed_field_on(F)` ⇔ `field_on(F)` and every polynomial of positive degree over `F.carrier` has a root in `F.carrier`: a structure over `field_on` |
| `FieldOn` | an algebraically closed field is a field |
| `PositiveDegreeRoot` | a polynomial of positive degree over `F.carrier` has a root in `F.carrier` |
| `AlgebraicallyClosedFieldOnIff` | `algebraically_closed_field_on(F) ⇔ field_on(F) ∧ algebraically_closed_field(F)` |
| `AlgebraicElementsClosed` | `M` a closed field, `k` a subfield ⇒ a polynomial of positive degree over the elements of `M` algebraic over `k` has a root among them: the algebraic elements are closed in their turn |

## One variable over a closed field

A nonzero polynomial whose roots are all roots of `q` divides a power of
`q`: by induction on the degree, a root splits off a linear factor, which
divides `q`. So a root of `p` avoiding `q` exists exactly when `p` does not
divide `q` to the degree of `p`, and a polynomial `p` takes a nonzero value
exactly when it is not zero, at a root of `p·x − 1`. Over a commutative ring,
the pseudo-remainder `r` of $h^{\deg g}$ by `g` decides, at once for every
homomorphism `σ` into a closed field keeping `g`'s leading coefficient,
whether `σg` has a root where `σh` is nonzero: `σ` carries the
pseudo-division coefficientwise, so such a root exists exactly when `σr` is
not zero.

| member | statement |
|---|---|
| `RootsDivideDegreePower` | the Nullstellensatz in one variable: a nonzero `p` whose roots are all roots of `q` divides `q` to the power of its degree |
| `RootAvoidance` | `p` of positive degree: a root of `p` where `q` does not vanish exists exactly when `p` does not divide `q` to the degree of `p` |
| `NonzeroValue` | a polynomial over `F.carrier` takes a nonzero value there exactly when it is not the zero polynomial |
| `PseudoRemainderDecision` | over a commutative ring, the pseudo-remainder of $h^{\deg g}$ by `g` decides, under every homomorphism `σ` into an algebraically closed field keeping `g`'s leading coefficient, whether `σg` has a root where `σh` is nonzero |

## Extensions and chains

| member | statement |
|---|---|
| `FieldExtendsPreorder` | `preorder(field_extends)` |
| `FieldExtendsEval` | `field_on(F) ∧ field_extends(F, G) ∧ K ⊆ F.carrier ∧ x ∈ F.carrier ⇒` a polynomial over `K` has one value at `x` under `F` and `G`, and `algebraic_over(F, K, x) ⇔ algebraic_over(G, K, x)` |
| `AlgebraicOverTransport` | `ι` injective on `F.carrier`, `K ⊆ F.carrier`, `x ∈ F.carrier` ⇒ `ι(x)` is algebraic over `image(ι, K)` in `transport_field(ι, F)` exactly when `x` is over `K` in `F` |
| `FieldExtendsSubfield` | `field_on(F) ∧ field_extends(F, G) ⇒ subfield(G, F.carrier)`; `G` need not be a field |
| `FieldExtendsHomomorphism` | `field_extends(F, G)` for fields `F` and `G` ⇒ the inclusion `λy. y` is a ring homomorphism from `field_ring(F)` to `field_ring(G)` |
| `FixedFieldEmbeddingExtends` | a ring homomorphism of fields fixing the source field's carrier makes the target an extension, `field_extends(F, G)` |
| `ChainUnionExtends` | `chain(field_extends, c) ∧ F ∈ c ⇒ field_extends(F, chain_union_field(c))` |
| `ChainUnionFieldOn` | a nonempty chain of fields, each holding `K` and algebraic over it, unites to a field algebraic over `K` |
| `MaximalAlgebraicExtension` | every field has an extension maximal under `field_extends` among its algebraic extensions on the same type |

## Adjoining a root

| member | statement |
|---|---|
| `RootAdjunctionInHost` | `p` irreducible over `F`, and room off `F.carrier` for the polynomials over `F` ⇒ some field `G` on the same type extends `F`, holds a root of `p`, and is algebraic over `F.carrier` |

## The algebraic closure

| member | statement |
|---|---|
| `AlgebraicExtensionBound` | a field on `B` holding `image(ι, k)`, `k : set(A)`, and algebraic over it injects into `prod(num → A, num)` |
| `AlgebraicExtensionRoom` | a field of the closure host holding `image(ι, k)` and algebraic over it has room off its carrier for all its polynomials |
| `ClosureEmbeddingInjective` | `a ↦ {(0, λn. a)}` is one-to-one on every set |
| `AlgebraicClosureInHost` | every field `K` on `A` has an algebraically closed field `M` on `set(prod(num, num → A))` extending the transported copy of `K` along `a ↦ {(0, λn. a)}`, every point algebraic over the copy |
| `AlgebraicClosureFieldOn` | every field `K` on `A` has an algebraically closed field `M` on `set(prod(num, num → A))`, algebraic over the copy of `K`, that holds the copy as a subfield, `a ↦ {(0, λn. a)}` an isomorphism onto it: the algebraic closure of `K` |

## Extending embeddings into a closed field

A map of fields from K into a closed field carries the minimal polynomial of an element z algebraic over K to one of the same positive degree, and the closed field holds its root, so the map extends to K(z); adjoining finitely many algebraic elements one at a time extends it to K(S).

| member | statement |
|---|---|
| `AdjoinEmbeddingClosed` | a map of fields from K into a closed field extends to K(z) for z algebraic over K |
| `FiniteAdjoinEmbedding` | a map of fields from K into a closed field extends to K(S) for a finite set S of elements algebraic over K, one adjunction at a time |

## Splitting inside a closed field

| member | statement |
|---|---|
| `ClosedFieldSplits` | `field_on(M) ∧ algebraically_closed_field(M) ⇒` every polynomial splits over `M` |
| `SplittingFieldInClosed` | `M` closed, `K` a subfield, `p` a nonzero polynomial over `K` ⇒ the field `K` generates with the roots of `p` is finite over `K`, `p` splits over it, and it lies in every subfield holding `K` over which `p` splits |

## Factors over a closure

Over a closed field a monic polynomial splits off the linear factor at a root, so by induction on the degree it lies over every subring that holds its roots (`MonicCoefficientsFromRoots`). A monic factor of a nonzero polynomial over `k` has its roots among the polynomial's, so its coefficients are algebraic over `k`, and any field is carried into its closure and read back through the transported copy. A monic factor of a monic polynomial over a subring `S` has its coefficients integral over `S` (Kronecker) the same way, the elements integral over `S` being a subring; a field embedding carries integrality to the image and reflects it, so any field is read back from its closure through the embedding. An element integral over a ring integrally closed in a field `F` holding it therefore has its minimal polynomial over `F` with coefficients in the ring. Read through a ring map ι from M, a binary form $\sum \iota(f(i)) \cdot a^i \cdot b^{m-i}$ of a nonzero f is a product of linear factors a − ι(β)·b, so a prime ideal holding it holds one of them (`PrimeHoldsLinearFactor`).

| member | statement |
|---|---|
| `MonicCoefficientsFromRoots` | over a closed field `M`, a monic polynomial over `M.carrier` whose roots lie in a subring `Ω` is a polynomial over `Ω` |
| `MonicFactorCoefficientsInClosed` | over a closed field, a monic factor of a nonzero polynomial over a subfield `k` has every coefficient algebraic over `k` |
| `MonicFactorCoefficientsAlgebraic` | over any field `M`, a monic factor over `M` of a nonzero polynomial over a subfield `k` has every coefficient algebraic over `k` |
| `FieldEmbeddingIntegral` | a field embedding `ι`, `S ⊆ F.carrier`, `x ∈ F.carrier`: `x` integral over `S` ⇒ `ι(x)` integral over `image(ι, S)` |
| `FieldEmbeddingReflectsIntegral` | the converse: `ι(x)` integral over `image(ι, S)` in `G` ⇒ `x` integral over `S` in `F` |
| `MonicFactorCoefficientsIntegralInClosed` | over a closed field, a monic factor of a monic polynomial over a subring `S` has every coefficient integral over `S` |
| `MonicFactorCoefficientsIntegral` | over any field `M`, a monic factor over `M` of a monic polynomial over a subring `S` has every coefficient integral over `S` (Kronecker) |
| `MinimalPolynomialOverClosed` | an element integral over a subring `R` integrally closed in a subfield `F ⊇ R` has its minimal polynomial over `F` with coefficients in `R`; `F` need not be the fraction field of `R` |
| `PrimeHoldsLinearFactor` | over an algebraically closed `M`, a prime ideal reached by a ring map `ι` from `M` that holds the binary form $\sum \iota(f(i)) \cdot a^i \cdot b^{m-i}$ of a nonzero `f` holds a linear factor `a − ι(β)·b` with `β ∈ M` |

## Separability of a simple extension

A simple extension by a separable element is separable. Inside a closed field the element's minimal polynomial has a root field that is Galois (`galois_correspondence.SeparableRootFieldGalois`), and `F(z)` lies in it. A general field embeds in its closure, and an embedding carries separability both ways, its inverse on the image being an embedding too.

| member | statement |
|---|---|
| `FieldEmbeddingReflectsSeparable` | a field embedding `ι`, `k` a subfield, `x` in the source field, `ι(x)` separable over `image(ι, k)` ⇒ `x` is separable over `k`; `x` is not assumed algebraic |
| `SeparableAdjoinSeparable` | `z` in `L` separable over a subfield `F` ⇒ every element of `F(z)` is separable over `F`, in any ambient field `L` |

## The primitive element theorem

Inside the closure, two elements of a finite separable extension `K` of an
infinite field `B` lie in the root field of their minimal polynomials. That
field is finite Galois over `B` (`galois_correspondence.SeparableRootFieldGalois`), and all but
finitely many `r ∈ B` make `a + r·b` generate both. Pulled back, any two
elements of `K` share a primitive element in `K`, and an element of largest
degree over `B` generates `K`. The theorem lives here because its proof runs
in the algebraic closure.

| member | statement |
|---|---|
| `PrimitiveElement` | `B` infinite, `K` finite over `B` with every element separable over `B` ⇒ `K = B(z)` for some `z ∈ K` |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
