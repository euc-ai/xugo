# singular_homology — the singular chains of a space with coefficients in a ring, homotopy invariance, small simplices and the Mayer–Vietoris sequence

The singular chains of a space with coefficients in a commutative ring R
are simplicial_chain's chains on its singular simplicial set: the free
modules on the singular simplices, `free_complex`, with the alternating
sum of the faces for boundary. `singular_complex(R, T)` names that
complex; its homology is `homology_module(singular_complex(R, T), n)`,
and a continuous map acts on it through the pushforward of the simplicial
map it induces, `λn. free_pushforward(R, singular_map(f, n))`, a chain
map. Nothing in the chain algebra is new: the chapter reads the free
chains, chain homotopies and the long exact sequence of a short exact
sequence of complexes from algebra/module and simplicial/, at the
singular simplicial set.

Three theorems carry the geometry. Homotopic maps induce chain homotopic
chain maps, by the prism that cuts Δⁿ × ⟦0, 1⟧ into n + 1 simplices; so a
homotopy equivalence induces isomorphisms in homology, and a contractible
space, homotopy equivalent to a point whose chains are those of a
constant simplicial set, has no homology above degree 0. A nonempty
path-connected space has R for its homology in degree 0, the coefficient
sum of a 0-chain. And the chains of simplices each inside a member of an
open cover compute the same homology as all chains: barycentric
subdivision shrinks every simplex below a Lebesgue number of the cover,
and is chain homotopic to the identity.

For a space covered by two open sets the small chains are the sums of
chains in the one and in the other, which makes a short exact sequence
with the chains of the two sets and of their intersection; its long
exact sequence is the Mayer–Vietoris sequence. Where the two sets have
no homology in two consecutive degrees, the connecting map identifies the
homology of the union one degree up with that of the intersection —
the step the spheres are computed by (vector/sphere).

## The definitions (definitions.go)

| constant | reading |
|---|---|
| `singular_complex(R, T)` | `free_complex(R, singular_set(T).simplices, simplicial_boundary(R.add, R.zero, R.one, R.neg, R.mul, singular_set(T).d))` |

## Singular homology (singular_homology.go)

| member | statement |
|---|---|
| `SingularChainComplex` | `comm_ring_on(R) ⇒ chain_complex(R, singular_complex(R, T))` — card |
| `SingularChainMap` | `comm_ring_on(R) ∧ continuous_map(T, S, f) ⇒ chain_map(R, singular_complex(R, T), singular_complex(R, S), λn. free_pushforward(R, singular_map(f, n)))` — card |
| `SingularHomotopyChainHomotopy` | `comm_ring_on(R) ∧ homotopic_rel(T, S, ∅, f, g) ⇒ ∃h. chain_homotopy(R, singular_complex(R, T), singular_complex(R, S), λn. free_pushforward(R, singular_map(f, n)), λn. free_pushforward(R, singular_map(g, n)), h)` — card |
| `HomotopyEquivalenceHomology` | `comm_ring_on(R) ∧ homotopy_equivalence(T, S, f, g) ⇒ module_isomorphism(R, homology_module(singular_complex(R, T), n), homology_module(singular_complex(R, S), n), homology_map(singular_complex(R, S), λk. free_pushforward(R, singular_map(f, k)), n))` — card |
| `ContractibleAcyclic` | `comm_ring_on(R) ∧ contractible_space(T) ⇒ cycles(singular_complex(R, T), n + 1) = boundaries(singular_complex(R, T), n + 1)` — card |
| `PathConnectedZerothHomology` | `comm_ring_on(R) ∧ path_connected_in(T, ⋃T) ∧ x ∈ ⋃T ⇒ module_isomorphic(R, homology_module(singular_complex(R, T), 0), regular_module(R))` — card |
| `SmallChainsQuasiIsomorphism` | `comm_ring_on(R) ∧ c ⊆ T ∧ ⋃T ⊆ ⋃c ⇒` the inclusion of the free complex on the simplices each with image inside a member of c into `singular_complex(R, T)` is a `quasi_isomorphism` — card |
| `MayerVietorisDiagonal` | `comm_ring_on(R)`, u and v open with `⋃T ⊆ u ∪ v`, cycles = boundaries for u and for v in degrees n + 1 and n + 2 ⇒ `module_isomorphic(R, homology_module(singular_complex(R, T), n + 2), homology_module(singular_complex(R, subtopology(T, u ∩ v)), n + 1))` — card |

Framework mechanics (family manifest, shared CNF cache, replay) are
family.go's header and the constitution's.
