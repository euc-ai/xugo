# field_extension — a subfield above another as a vector space over it, its degree, and the tower law

Everything lives in one field on a set: every law opens with
`∀L:field_on(A).`, a record `L:field_ops(A)` whose carrier is a set of the type `A`,
and the fields it contains are its subfields, sets `subfield(L, K)`. The
field may be a whole type, a field of fractions, a quotient of a ring by
a maximal ideal or a residue field: each is a field on a set, so each is
an `L` the laws read at. An extension is a pair of subfields `K ⊆ M`,
and `M` is a vector space over
`K` with the field's own operations: the vectors' sum, zero and negation
are the field's, and `K` acts by the field's product
(`ExtensionModuleOn`, the module chapter's `module_on` at the ring
record `restrict_ring(field_ring(L), K)` and the module record
`restrict_module(regular_module(field_ring(L)), M)`). Nothing is a new type and nothing is
coerced: `K`, `M` and the scalars acting on `M` are subsets of `L.carrier` with
`L`'s operations.

`finite_extension(L, K, M)` says `M` is finite-dimensional over `K`, and
`extension_degree(L, K, M)`, the degree `[M:K]`, is its dimension. The
degree is a number nothing is said about when the extension is not
finite. The tower law is bases multiplied: a basis of `M` over `K` and
one of `N` over `M` give their products as a basis of `N` over `K`, all
distinct (`TowerBasis`), so degrees multiply (`TowerLaw`); and each step
of a finite tower is finite (`TowerFinite`). A finite extension of
degree one is no extension at all (`DegreeOneIff`). A field between `B` and `K` has degree at most `[K : B]`, and is `K` at equality (`IntermediateDegree`).

The field record is explicit in `finite_extension(L, K, M)` and
`extension_degree(L, K, M)`. Its ring on a subfield is
`restrict_ring(field_ring(L), K)`; its vector operations are
`restrict_module(regular_module(field_ring(L)), M)`, the field's ring as
a module over itself, on `M`.

## The definitions

| member | statement |
|---|---|
| `FiniteExtensionDef` | `finite_extension(L, K, M) ⇔ finite_dimensional(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), M))` |
| `ExtensionDegreeDef` | `extension_degree(L, K, M) = module_dim(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), M))` |

## Extensions and the tower law

| member | statement |
|---|---|
| `RingExtensionModuleOn` | `subfield(L, K) ∧ comm_ring_on(restrict_ring(field_ring(L), M)) ∧ K ⊆ M ⇒ module_on(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), M))` |
| `ExtensionModuleOn` | `subfield(L, K) ∧ subfield(L, M) ∧ K ⊆ M ⇒ module_on(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), M))` |
| `SubfieldScalars` | `subfield(L, K) ⇒ subring(field_ring(L), K) ∧ module_on(restrict_ring(field_ring(L), K), regular_module(field_ring(L)))` |
| `SubfieldSubmodule` | `subfield(L, K) ∧ subfield(L, M) ∧ K ⊆ M ∧ M ⊆ N ⇒ submodule(restrict_ring(field_ring(L), K), restrict_module(regular_module(field_ring(L)), N), M)` |
| `ScaleLinear` | `subring(field_ring(L), S) ∧ a ∈ L.carrier ⇒` `L.mul(a)` is a module endomorphism of `regular_module(field_ring(L))` over `restrict_ring(field_ring(L), S)` |
| `MultiplicationLinear` | `subfield(L, K) ∧ z ∈ L.carrier ⇒` `L.mul(z)` is a module endomorphism of `regular_module(field_ring(L))` over `restrict_ring(field_ring(L), K)` |
| `ProductFormLinear` | subfields `F ⊆ C` of `M`, a linear form `T` on `C` over `F` into `F` and `b ∈ C` give the linear form `y ↦ T(b * y)` |
| `SubfieldRetraction` | `subfield(L, K) ⇒` some `K`-linear map of `L` onto `K` fixes every member of `K` — a `K`-linear retraction |
| `TowerSpan` | `B` spanning `M` over `K` and `C` spanning `N` over `M` give `{b * c}` spanning `N` over `K` |
| `TowerIndependent` | finite `B` independent over `K` and `C` independent over `M` give `{b * c}` independent over `K`, with `card(B) * card(C)` members |
| `TowerBasis` | finite bases `B` of `M` over `K` and `C` of `N` over `M` give `{b * c}` as a basis of `N` over `K` of `card(B) * card(C)` members |
| `BasisDegree` | a finite basis `B` of `M` over `K` gives `finite_extension(L, K, M) ∧ extension_degree(L, K, M) = card(B)` |
| `ExtensionOverItself` | `subfield(L, K) ⇒ finite_extension(L, K, K) ∧ extension_degree(L, K, K) = 1` |
| `TowerLaw` | `finite_extension(L, K, M) ∧ finite_extension(L, M, N) ⇒ finite_extension(L, K, N) ∧ extension_degree(L, K, N) = extension_degree(L, K, M) * extension_degree(L, M, N)` |
| `TowerFinite` | `finite_extension(L, K, N) ⇒ finite_extension(L, K, M) ∧ finite_extension(L, M, N)` |
| `DegreeOneIff` | `finite_extension(L, K, M) ⇒ (extension_degree(L, K, M) = 1 ⇔ M = K)` |
| `IntermediateDegree` | subfields `B ⊆ E ⊆ K` with `finite_extension(L, B, K)` ⇒ `finite_extension(L, B, E)`, `extension_degree(L, B, E) ≤ extension_degree(L, B, K)`, and `E = K` when the degrees agree |
| `FiniteEmbeddingOnto` | a homomorphism of a finite extension `M/K` into the ambient field, fixing `K` and mapping `M` into itself, has image `M` |
| `ExtensionDegreePositive` | A finite extension has positive degree |
