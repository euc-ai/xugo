# galois_correspondence — Galois extensions of a subfield and the correspondence between their intermediate fields and automorphism groups

A subfield `M` above a subfield `K` is normal over `K` when every
irreducible polynomial over `K` with a root in `M` splits over `M`,
`normal_over(L, K, M)`. An element `a` is separable over `K` when it is
algebraic over `K` and its minimal polynomial is coprime over `K` to its
derivative, `separable_over(L, K, a)`. And `M` is Galois over `K`,
`galois_over(L, K, M)`, when it is a finite extension of `K`, normal over
`K`, and each of its members is separable over `K`.

All three are said of subsets of one field `L` on a set and of
polynomials over `L`'s type: a root in `M` is a member of `M`, splitting over `M` is a
statement about divisibility by polynomials over `M`, and none of the
three builds a splitting field. The minimal polynomial over `K` of a member of a normal
extension splits over `M` (`NormalIffMinimalPolynomial`), and when the
member is separable its roots in `M`, its conjugates, are exactly as
many as the degree (`ConjugatesCount`). When `M` is finite over `K`,
normality passes to every intermediate `E`. Separability of an element
passes from `K` to a larger subfield `E`, and a Galois extension `M/K`
remains Galois over `E`. A root of a
polynomial over `K` that is separable over `K` is itself separable over `K`,
its minimal polynomial dividing that polynomial (`SeparableAnnihilator`); so
a field embedding `ι` of `F` into a field `G` on another type — a ring
homomorphism of their rings, one-to-one by
`algebraic_element.FieldEmbeddingSubfieldsAdjoin` — carries an element
separable over a subfield `k` to one separable over `image(ι, k)`
(`FieldEmbeddingSeparable`): the transported minimal polynomial is separable over
`image(ι, k)` and has `ι(x)` as a root.

For a Galois extension the subfields between `K` and `M` and the
subgroups of the Galois group `galois_group(L, K, M)` determine each other: `E` goes
to the automorphisms fixing it, `field_automorphisms(L, E, M)`, and a
subgroup `H` to the field it fixes, `fixed_field(M, H)`; the two maps are
inverse and reverse inclusion, and `[E : K]` is the index of
`field_automorphisms(L, E, M)`. Every field of the correspondence is a set
of the one type, so it states no map between two field types; the
embedding of `FieldEmbeddingSeparable` is the one place
two fields on different types meet, and it compares them through images. An intermediate field is normal over `K` exactly
when its group is a normal subgroup; then each automorphism of `M`
restricts to one of `E`, `permutation_restrict(E, p)` — the permutation
that is `p` on `E` and the identity elsewhere — and the quotient of
`galois_group(L, K, M)` by `field_automorphisms(L, E, M)` is isomorphic
to `galois_group(L, K, E)`.

The field record is explicit: under a law over the field the text writes
`normal_over(L, K, M)`, `separable_over(L, K, a)` and `galois_over(L, K, M)`.

## The definitions

| member | statement |
|---|---|
| `NormalOverDef` | `normal_over(L, K, M)` ⇔ every irreducible `p` over `K` with a root `a ∈ M` has `polynomial_splits(restrict_ring(field_ring(L), M), p)` |
| `SeparableOverDef` | `separable_over(L, K, a)` ⇔ `algebraic_over(L, K, a) ∧ polynomial_separable(restrict_ring(field_ring(L), K), minimal_polynomial(L, K, a))` |
| `GaloisOverDef` | `galois_over(L, K, M)` ⇔ `finite_extension(L, K, M) ∧ normal_over(L, K, M) ∧ (∀a. a ∈ M ⇒ separable_over(L, K, a))` |

## Normality and separability

| member | statement |
|---|---|
| `NormalIffMinimalPolynomial` | `normal_over(L, K, M)` ⇔ the minimal polynomial over `K` of each member of `M` algebraic over `K` splits over `M` |
| `NormalTower` | a finite normal extension `M` of `K` is normal over every intermediate `E` |
| `SeparableTower` | separable over `K` is separable over every larger subfield `E` |
| `GaloisTower` | `galois_over(L, K, M) ⇒ galois_over(L, E, M)` for every intermediate `E` |
| `ConjugatesCount` | in a normal extension, a separable `a` has `deg μ` conjugates in `M` |
| `SeparableAnnihilator` | a root `x ∈ L.carrier` of a polynomial over `B` that is separable over `B` is separable over `B`: being separable, the polynomial is nonzero, and the minimal polynomial divides it |
| `FieldEmbeddingSeparable` | a field embedding `ι`, `ring_homomorphism(field_ring(F), field_ring(G), ι)`, carries an `x` separable over a subfield `k` of `F` to `ι(x)` separable over `image(ι, k)` |

## Galois extensions and their groups

The conjugate-automorphism construction extends an embedding across a
finite basis and uses dimension to make it onto. The fixed-field criterion
combines singleton conjugate sets with separable polynomials on finite
orbits. The numerical criterion then uses Artin's degree formula and the
tower law.

On a Galois extension the sum of the conjugates is a `K`-linear form into
`K` (`GaloisTraceLinear`): the sum is fixed by every automorphism
(`field_automorphism.GaloisTraceFixed`), and `GaloisIffFixed` reads the
fixed field as `K`.

A root field is Galois (`SeparableRootFieldGalois`): adjoining to a subfield
`K` of `L` every root of finitely many separable polynomials over `K` that
split in `L` gives a Galois extension of `K`. `L` need not be closed; inside
a closed field the splitting comes from `algebraic_closure.ClosedFieldSplits`.
The proof counts the embeddings of the root field over `K` by adjoining roots
one at a time: the transported minimal polynomial of a root divides a
separable polynomial that splits (`algebraic_element.TransportedMinimalPolynomial`),
so it has as many distinct roots as its degree, and each embedding of the
field before extends in that many ways (`algebraic_element.AdjoinEmbeddingAtRoot`).
The embeddings are then as many as the degree, each maps the roots to roots,
so maps the root field onto itself (`field_extension.FiniteEmbeddingOnto`), and
extends to a permutation (`field_automorphism.EmbeddingPermutation`), an
automorphism; `GaloisIffCard` concludes.

| member | statement |
|---|---|
| `ConjugateAutomorphism` | in a finite normal extension, some automorphism fixing `K` sends `a` to any conjugate `b` in `M` |
| `GaloisIffFixed` | a finite extension is Galois ⇔ `fixed_field(M, field_automorphisms(L, K, M)) = K` |
| `GaloisTraceLinear` | on a Galois extension `C` of `K` inside `M` the group `field_automorphisms(M, K, C)` is finite and the sum of the conjugates, `b ↦ Σ_g g(b)`, is a `K`-linear form on `C` into `K` |
| `GaloisIffCard` | a finite extension is Galois ⇔ `card(field_automorphisms(L, K, M)) = extension_degree(L, K, M)` |
| `FixedFieldGalois` | `M` is Galois over the field a finite group of its automorphisms fixes |
| `SeparableRootFieldGalois` | `P` a finite set of polynomials over a subfield `K` of `L`, each separable over `K` and splitting in `L` ⇒ the field `K` generates with the roots in `L` of the members of `P` is Galois over `K` |

## The correspondence

| member | statement |
|---|---|
| `CorrespondenceFixed` | `fixed_field(M, field_automorphisms(L, E, M)) = E` for every intermediate `E` |
| `CorrespondenceAutomorphisms` | for a finite extension `M/K`, a subgroup `H` of `galois_group(L, K, M)` fixes an intermediate field, and `field_automorphisms(L, fixed_field(M, H), M) = H`; this half of the correspondence needs no Galois hypothesis |
| `CorrespondenceAntitone` | `E ⊆ F ⇔ field_automorphisms(L, F, M) ⊆ field_automorphisms(L, E, M)` for any `E ⊆ M` and an intermediate field `F` |
| `CorrespondenceDegree` | `field_automorphisms(L, E, M)` has `[M : E]` members and index `[E : K]` |

## Normal intermediate fields and the quotient

| member | statement |
|---|---|
| `permutationRestrictDef` | `permutation_restrict(E, p)` = a permutation moving no point outside `E` that agrees with `p` on `E`, chosen |
| `RestrictionInto` | an automorphism fixing `K` carries a normal intermediate `E` into `E` — card |
| `RestrictionAutomorphism` | `permutation_restrict(E, p) ∈ field_automorphisms(L, K, E)`, agreeing with `p` on `E` — card |
| `RestrictionHomomorphism`, `RestrictionKernel`, `RestrictionOnto` | restriction is a homomorphism `galois_group(L, K, M) → galois_group(L, K, E)` with kernel `field_automorphisms(L, E, M)`, onto — card |
| `NormalIffNormalSubgroup` | `E` is normal over `K` exactly when its fixing automorphisms are normal in those fixing `K` — card |
| `QuotientGalois` | `E` is Galois over `K`, and `galois_group(L, K, M)` modulo `field_automorphisms(L, E, M)` is isomorphic to `galois_group(L, K, E)` |
