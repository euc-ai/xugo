# simplicial_group — the homotopy groups of a simplicial module, read off its Moore complex

A simplicial module `simplicial_module(R, V, M)` is in particular a
simplicial abelian group, and two classical facts tie its homotopy to its
Moore complex `moore_complex(V, M)`. It is a Kan complex, by Moore's
construction of fillers, which simplicial_module states as
`HornFillerExists`; so its homotopy groups
`simplicial_homotopy_group(M, x₀, n)` are taken at every vertex
under homotopy_group's definitions. And at the vertex `V.zero` they are
the homology of the Moore complex — not only in bijection with it, but
the same set of sets.

The comparison rests on three observations. Every 0-th degeneracy
keeps `V.zero` (simplicial_module's `DegeneracyZero`), so the base
simplex at `V.zero` is `V.zero` in every dimension (simplicial_set's
`BaseSimplexFixedPoint`), and a sphere at `V.zero` is a simplex all of whose faces vanish: a Moore
cycle. A homotopy between two spheres reads faces `n` and `n + 1` of an
(n+1)-simplex, with the faces below `n` at the base, while a Moore
boundary reads face 0, with the faces above it zero. Subtracting a
degeneracy moves the one nonzero face of a simplex to the next place and
negates it, so the Moore boundaries can be read through any face, and two
spheres are homotopic exactly when their difference is a Moore boundary.
The class of a sphere is then its coset modulo the Moore boundaries, and
πₙ at `V.zero` is the Moore homology `homology(moore_complex(V, M), n)`.

At another vertex `x₀`, adding the base simplex at `x₀` in every
dimension is an automorphism of the underlying simplicial set — not of
the module, since it is not additive — carrying `V.zero` to `x₀`; its
direct image carries the classes at `V.zero` one-to-one onto the classes
at `x₀`. So πₙ is the one class of its unit at a vertex exactly when the
Moore complex is exact in degree `n`, and a simplicial module acyclic
over a set, `acyclic_augmentation(R, V, M, N, ε)`, has every
homotopy group of positive dimension trivial at every vertex. This is how
a resolution's acyclicity, stated on its Moore complex, is said with
`kan_complex` and `simplicial_homotopy_group`. The group structure of πₙ
plays no part: every comparison here is one of sets.

## Spheres at zero and Moore cycles

| member | statement |
|---|---|
| `HomotopyGroupMooreCycles` | the spheres at `V.zero` are the Moore cycles: `simplicial_sphere(M, V.zero, n) = cycles(moore_complex(V, M), n)` — card |
| `MooreBoundaryAtFace` | for each face `k ≤ n + 1`, `c` is a Moore boundary of degree `n` exactly when some (n+1)-simplex has `c` as its k-th face and `V.zero` as every other — card |

## Homotopy at zero is the Moore homology

| member | statement |
|---|---|
| `HomotopicIffMooreBoundary` | two spheres at `V.zero` are homotopic exactly when their difference is a Moore boundary — card |
| `HomotopyClassMooreCoset` | the homotopy class of a sphere `x` at `V.zero` is `left_coset(V.add, x, boundaries(moore_complex(V, M), n))` — card |
| `HomotopyGroupMooreHomology` | `simplicial_homotopy_group(M, V.zero, n) = homology(moore_complex(V, M), n)` — card |

## Other base points

| member | statement |
|---|---|
| `BasepointTranslationIsomorphism` | for a vertex `x₀`, `u ↦ u + base_simplex(M.s, x₀, n)` is a `simplicial_isomorphism` of `M` onto itself, `simplicial_isomorphism(M, M, …)` — card |
| `BasepointTranslation` | πₙ at `x₀` is the direct image of πₙ at `V.zero` under that translation, and the direct image is injective on the classes — card |
| `HomotopyGroupTrivialIffMooreExact` | at a vertex `x₀`, πₙ is `{simplicial_homotopy_unit(M, x₀, n)}` exactly when the Moore cycles of degree `n` are the Moore boundaries — card |
| `AcyclicHomotopyGroupsTrivial` | under `acyclic_augmentation`, πₙ at every vertex is `{simplicial_homotopy_unit(M, x₀, n)}` for every `0 < n` — card |
