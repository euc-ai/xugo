# field_automorphism — the automorphisms of a subfield fixing a smaller one, fixed fields, Dedekind and Artin

The automorphisms of a subfield `M` fixing a subfield `K ⊆ M`,
`field_automorphisms(L, K, M)` — Aut_K(M) on paper — are permutations of the
type the field `L` lives in: those that move no point outside `M`, keep the sum
and the product of members of `M`, and fix every member of `K`. Such a
permutation carries `M` onto itself, so it is an automorphism of `M`
fixing `K`, made a permutation of the type by the identity outside `M`;
and every automorphism of `M` fixing `K` arises so, once. The
automorphisms then form a subgroup of the permutations, a group on
their set under composition, `galois_group(L, K, M)` (for any `K ⊆ M`,
Galois or not), with no group of automorphisms built as a type. At `M = L.carrier` they are the automorphisms of the field `L` itself.

The members of `M` that every permutation of a set `H` fixes form the
fixed field `fixed_field(M, H)`, a subfield when `H` is made of
automorphisms of `M`. Distinct automorphisms are linearly independent
over `L` (Dedekind), so a finite extension has at most its degree many
automorphisms fixing `K`; and a finite group `H` of automorphisms of `M`
makes `M` an extension of its fixed field of degree exactly `|H|`, whose
automorphisms are exactly `H` (Artin).

The field record is explicit: under `∀L:field_on(A).` the text writes
`field_automorphisms(L, K, M)`.

## The definitions

| member | statement |
|---|---|
| `FieldAutomorphismsDef` | `field_automorphisms(L, K, M)` = the `p ∈ symmetric_group(M)` keeping `+` and `*` on `M` and fixing each member of `K` |
| `GaloisGroupDef` | `galois_group(L, K, M)` = `restrict_group(permutation_group, field_automorphisms(L, K, M))`: the automorphisms of `M` over `K` as a group of permutations under composition; it is Aut_K(M) for any K ⊆ M, whether or not M is Galois over K |
| `FixedFieldDef` | `fixed_field(M, H) = {x \| x ∈ M ∧ ∀p. p ∈ H ⇒ permutation_map(p, x) = x}` |

## The group, and fixed fields

| member | statement |
|---|---|
| `AutomorphismsSubgroup` | Aut_K(M) is a subgroup of the permutations inside `symmetric_group(M)` |
| `GaloisGroupCarrier` | the carrier of `galois_group(L, K, M)` is `field_automorphisms(L, K, M)` |
| `GaloisGroupOn` | `galois_group(L, K, M)` is a group on its set |
| `GaloisGroupSubgroup` | a subgroup of `galois_group(L, K, M)` is exactly a subgroup of the permutations inside `field_automorphisms(L, K, M)` |
| `AutomorphismsTowerSubgroup` | for `K ⊆ E`, `field_automorphisms(L, E, M)` is a subgroup of `galois_group(L, K, M)` |
| `EmbeddingPermutation` | an onto embedding of `M` fixing `K` is represented by an automorphism of `M` over `K`, extended by the identity off `M` |
| `FiniteSubfieldAutomorphism` | a map of a finite extension `l` of `k` that keeps sums, products and one, fixes `k` and keeps `l` is an automorphism of `l` over `k` |
| `AutomorphismRingHomomorphism` | an automorphism of `M` is a ring homomorphism of the restricted field |
| `AutomorphismFixesUnits` | an automorphism of a subfield `M` fixes `zero` and `one` |
| `AutomorphismPermutesRoots` | an automorphism fixing `K` sends a root in `M` of a polynomial over `K` to a root |
| `FiniteOrbitPolynomial` | a finite subgroup orbit in `M` is the root set of a polynomial over its fixed field, separable and split over `M` |
| `FixedFieldSubfield` | the field fixed by automorphisms of `M` is a subfield |
| `AutomorphismsAgreeOnGenerators` | two automorphisms of `K(S)` that agree on `K` and on `S` are equal |
| `FixedFieldAntitone` | more automorphisms fix fewer points |
| `SubfieldFixed` | `K ⊆ fixed_field(M, Aut_K(M))` |
| `AutomorphismsAntitone` | fixing a larger set leaves fewer automorphisms |
| `FixedFieldAutomorphisms` | a set `H` of automorphisms of `M` lies in `field_automorphisms(L, fixed_field(M, H), M)` |

Multiplying the distinct linear factors indexed by a finite orbit gives
a polynomial whose roots are that orbit (`FiniteOrbitPolynomial`).
The group permutes the factors, so every coefficient lies in its fixed
field.

## Dedekind and Artin

The two dimension arguments share the coordinate relation
(`free_module.CoordinateRelation`) and the independence criterion
(`linear_independence.IndependentImageCriterion`), and differ in the scalars
and in how the coefficients are cleared: `L` for the bound, `M` for Artin's
lemma, where the automorphisms act only on `M`. The automorphism bound evaluates the automorphisms
on a finite basis: a relation among the columns extends K-linearly from the
basis to all of `M`, where Dedekind independence clears it. Artin's lemma
evaluates members of `M` along a finite group `H`: minimality makes the
normalized relation of least support unique, applying an automorphism gives
another such relation, so its coefficients lie in the fixed field, where
independence clears them. The two inequalities meet in Artin's theorem.

| member | statement |
|---|---|
| `Dedekind` | a combination of finitely many automorphisms of `M` with coefficients in `L` that vanishes on `M` has every coefficient zero |
| `AutomorphismsBound` | a finite extension has finitely many automorphisms fixing `K`, at most `[M : K]` |
| `AutomorphismOrderFacts` | an automorphism `s` of a finite extension has an order: `0 < permutation_order(s)`, `s^permutation_order(s)` is the identity and no smaller positive power is, and `permutation_order(s) ∣ card(field_automorphisms(M, K, L))` |
| `ArtinIndependentBound` | Artin's lemma: a subset of `M` independent over `fixed_field(M, H)` has at most `card(H)` members |
| `ArtinFixedField` | a finite group `H` of automorphisms: `[M : fixed_field(M, H)] = card(H)` |
| `ArtinAutomorphisms` | `field_automorphisms(L, fixed_field(M, H), M) = H` |
| `AutomorphismsOrderPositive` | Above a finite extension of K, the automorphisms fixing a set holding K have a positive count |

## The sum of the conjugates

Under a finite group of automorphisms of a subfield `C` fixing `K` —
`field_automorphisms(M, K, C)`, the four members below naming the
ambient field `M` and the extension `C` — each automorphism is a
`K`-linear map of `C` (`AutomorphismLinear`), and the sum of the
conjugates of `b`, `Σ_g g(b)` over the group, is fixed by every
automorphism `h`: `h` carries the sum to the sum over the translates
`h ∘ g`, a one-to-one self-map of the finite group (`GaloisTraceFixed`).
The sum is not the zero map, the automorphisms being independent with
the identity among them (`GaloisTraceNonzero`, by `Dedekind`); and an
element integral over a subring `S ⊆ K` has its
conjugates roots of the same monic relation, whose finite sum is
integral (`GaloisTraceIntegral`, by
`integral_element.IntegralModuleSum`). On a Galois extension the
sum lands in `K` and is `K`-linear there:
`galois_correspondence.GaloisTraceLinear`.

| member | statement |
|---|---|
| `AutomorphismLinear` | an automorphism of `C` fixing `K` is a `K`-linear map of `C` |
| `GaloisTraceFixed` | under finitely many automorphisms of `C` fixing `K`, the sum of the conjugates of `b ∈ C` is fixed by each of them |
| `GaloisTraceNonzero` | the sum of finitely many automorphisms of `C` fixing `K` is not the zero map on `C` |
| `GaloisTraceIntegral` | under finitely many automorphisms of `C` fixing `K`, the sum of the conjugates of an element integral over a subring `S ⊆ K` is integral over `S` |
