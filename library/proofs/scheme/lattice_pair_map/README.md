# lattice_pair_map — maps and isomorphisms of lattice pairs, the module of maps, and what an isomorphism keeps

A map of lattice pairs M → N (scheme/lattice_pair) is an R-linear map of
the ambient of M into the container of N that carries each chart of M
into the same chart of N. It is linear over any subring of R and carries
the ambient and the chart sum of M into those of N; maps compose, and the
maps of M into N are a module over any subring of both charts. An
isomorphism is a map one-to-one and onto each chart: it carries the
ambient onto the ambient, H⁰ and H¹ isomorphically, and keeps their
dimensions and χ; isomorphisms compose and invert, and an isomorphism of
the target pairs acts on the maps by postcomposition. No statement about
an isomorphism assumes its target a lattice pair: a lattice pair M and an
isomorphism out of M force N to be one.

## Members

### The definitions

| Member | Statement |
|---|---|
| `LatticePairMapsDef` | `lattice_pair_maps(R, V, M, W, N)`: the R-linear maps of the ambients carrying each chart into the same chart |
| `LatticePairHomDef` | `lattice_pair_hom(R, V, M, W, N)`: those maps as a module, with the operations of the linear maps from the ambient of M into W |
| `LatticePairIsomorphismDef` | `lattice_pair_isomorphism(R, V, M, W, N, f)`: a map of lattice pairs, one-to-one, onto each chart |

### Maps of lattice pairs

| Member | Statement |
|---|---|
| `PairMapHomomorphism` | a map of lattice pairs is an R-linear map of the ambient of its source into W |
| `PairMapLinear` | a map of lattice pairs is linear on the ambient of its source over any subring of R |
| `PairMapsLinearSpace` | Hom(M, N) is a submodule of the R-linear maps from the ambient over any subring of both charts |
| `PairMapAmbient` | a map of lattice pairs carries the ambient of M into the ambient of N |
| `PairMapChartSum` | a map of lattice pairs carries M₀ + M₁ into N₀ + N₁ |
| `PairMapCompose` | maps of lattice pairs compose: for f : M → N and g : N → Q maps of lattice pairs, g ∘ f is one M → Q |

### Isomorphisms

| Member | Statement |
|---|---|
| `IsomorphismAmbient` | an isomorphism of lattice pairs carries the ambient of M onto the ambient of N |
| `IsomorphismSameH0` | an isomorphism restricts to an isomorphism of H⁰ over any subring of both charts |
| `IsomorphismSameH1` | an isomorphism induces, on cosets, an isomorphism of H¹ over any subring of both charts |
| `IsomorphismSameEuler` | a pair isomorphic to one with finite cohomology has finite cohomology, with equal h⁰, h¹ and χ |
| `IsomorphismCompose` | isomorphisms of lattice pairs compose — card |
| `IsomorphismInverse` | the preimage on the ambient, zero off it, is an isomorphism back |
| `MapsPostcomposeIsomorphism` | an isomorphism g : N → Q of target pairs gives, by f ↦ g ∘ f, an isomorphism Hom(M, N) → Hom(M, Q) over any subring of both charts |
| `LatticePairFromIsomorphism` | A lattice pair with ambient all of W, carried back along an isomorphism, is a lattice pair isomorphic to it |
