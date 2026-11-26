# singular_set — the singular simplicial set of a space, a Kan complex whose homotopy groups are the space's

A singular n-simplex of a space is a continuous map of the standard
n-simplex Δⁿ (vector/euclidean_simplex), read as a subspace of ℝⁿ⁺¹,
into the space, normalized to `junk` off the simplex as continuous's
hom sets are, so that it is determined by its values on Δⁿ:
`singular_simplices(T, n)`, the hom set
`continuous_hom_set(subtopology(euclidean_topology(n + 1), euclidean_simplex(n)), T)`.
The singular simplicial set `singular_set(T)` is the record
`mk_simplicial` of these sets with faces and degeneracies by
precomposition — the i-th face of an n-simplex σ is σ after the i-th
coface of Δⁿ⁻¹, the i-th degeneracy σ after the i-th codegeneracy of
Δⁿ⁺¹, each normalized again — so its simplicial identities are the
cosimplicial identities of the standard simplices. A continuous map acts
by postcomposition, `singular_map(f)`, a simplicial map, functorially.

The singular simplices of a subspace are those of the space whose image
lies in it, and the 0-simplices are the constant maps at the points. A
horn of singular simplices pastes, over the finitely many closed faces of
the horn of Δⁿ⁺¹, into one continuous map, and the retraction of Δⁿ⁺¹
onto its horn extends it: every singular simplicial set is a Kan complex.
So its homotopy groups are simplicial/homotopy_group's, read at the
vertex of a point — groups for n ≥ 1 and abelian for n ≥ 2 by `GroupOn`
and `AbelianGroupOn`, with no further statement — and the first of them
is the fundamental group of the space at the point.

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `singular_simplices(T, n)` | `continuous_hom_set(subtopology(euclidean_topology(n + 1), euclidean_simplex(n)), T)` |
| `singular_set(T)` | `mk_simplicial(λn. singular_simplices(T, n), λn i σ. normalize_on(euclidean_simplex(n - 1), junk, σ ∘ euclidean_coface(i)), λn i σ. normalize_on(euclidean_simplex(n + 1), junk, σ ∘ euclidean_codegeneracy(i)))` |
| `singular_map(f)` | `λn σ. normalize_on(euclidean_simplex(n), junk, f ∘ σ)` |

## The singular simplicial set (singular_set.go)

| member | statement |
|---|---|
| `SingularSimplicialSet` | `simplicial_set(singular_set(T))` — card |
| `SingularMapSimplicial` | `continuous_map(T, S, f) ⇒ simplicial_map(singular_set(T), singular_set(S), singular_map(f))` — card |
| `SingularMapIdentity` | `σ ∈ singular_simplices(T, n) ⇒ singular_map(λx. x, n, σ) = σ` — card |
| `SingularMapCompose` | `singular_map(g ∘ f, n, σ) = singular_map(g, n, singular_map(f, n, σ))` — card |
| `SubspaceSingularSimplices` | `u ⊆ ⋃T ⇒ singular_simplices(subtopology(T, u), n) = {σ \| σ ∈ singular_simplices(T, n) ∧ image(σ, euclidean_simplex(n)) ⊆ u}` — card |
| `SingularVertex` | `σ ∈ singular_simplices(T, 0) ⇔ ∃x. x ∈ ⋃T ∧ σ = normalize_on(euclidean_simplex(0), junk, λt. x)` — card |
| `SingularKan` | `kan_complex(singular_set(T))` — card |
| `FundamentalGroupSingular` | `x ∈ ⋃T ⇒ ∃φ. group_isomorphism(fundamental_group(T, x), mk_group(…, simplicial_homotopy_group(singular_set(T), «vertex», 1)), φ)`, «vertex» the 0-simplex at x — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
