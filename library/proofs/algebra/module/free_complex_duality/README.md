# free_complex_duality — based chain complexes, their duals with coefficients in a module, and the long exact sequence of a split zigzag

A based chain complex `based_chain_complex(R, P, S, e, r)` is a chain
complex P with a chosen basis in every degree: the expansion `e(n)` from
the free module on the generators `S(n)` and the coordinates `r(n)` back
are linear and inverse on the carriers. Nothing asks them to commute with
the boundaries; the boundary read in coordinates is
`r(n) ∘ P.d(n + 1) ∘ e(n + 1)`. A free complex is based by the identity,
and the total complex of a double complex and the cone of a chain map
take bases from their pieces, so the totals and cones built elsewhere
enter without being rewritten as another kind of complex.

The dual with coefficients in a module N, `free_dual_complex(R, N, P, S,
e, r)`, holds in degree n the N-valued functions on `S(n)`, zero off it,
and transposes the boundary read in coordinates. The transpose is
`hom_precompose` of
[`function_module`](../function_module/README.md): a function u on the
target generators goes to `s ↦ Σ_t Φ(δ_s)(t) • u(t)`. Its laws there —
linear, adjoint to Φ under the pairing `free_lift`, contravariant, linear
in Φ, natural in N — are what every statement about the dual reduces to.

Over a based complex lifting along a surjection needs no choice of
complement: a free module lifts generator by generator
(`free_module.FreeModuleLift`). So an acyclic based complex contracts, a
quasi-isomorphism of based complexes has a homotopy inverse (its cone is
acyclic, and a contraction of the cone yields the inverse and both
homotopies), and the dual of a quasi-isomorphism is a cochain homotopy
equivalence. Together with the dual of a degreewise split short exact
sequence this gives the long exact sequence of a split zigzag: a split
short exact sequence of based complexes, joined to a bottom row by three
quasi-isomorphisms and two squares commuting up to homotopy, dualizes to
a long exact sequence of the bottom row's cohomology with its own two
maps, starting injective in degree 0.

## Based chain complexes

| member | statement |
|---|---|
| `BasedChainComplex` | `based_chain_complex(R, P, S, e, r)` ⇔ a chain complex with linear, mutually inverse e(n) and r(n) — a structure, its subject `P` |
| `BasedComplexChain`, `BasedExpandHom`, `BasedCoordinatesHom`, `BasedCoordinatesExpand`, `BasedExpandCoordinates` | its five axioms |
| `FreeComplexBased` | a free complex is based by the identity — card |
| `DoubleTotalBasisDef`, `DoubleTotalExpandDef`, `DoubleTotalCoordinatesDef` | the total's generators `(p, s)` with `p ≤ n`, s a generator of the cell `(p, n − p)`; expansion and coordinates cell by cell |
| `DoubleTotalBased` | a double complex with based cells has a based total — card |
| `chainConeBasisDef`, `chainConeExpandDef`, `chainConeCoordinatesDef` | the cone's generators, the target's under κ and, above degree 0, the shifted source's under ι |
| `ChainConeBased` | the cone of a chain map between based complexes is based — card |

## Contractions and homotopy inverses

| member | statement |
|---|---|
| `BasedAcyclicContractible` | an acyclic based complex has a contraction, degree 0 included — card |
| `BasedQuasiIsomorphismHomotopyEquivalence` | a quasi-isomorphism of based complexes is a chain homotopy equivalence — card |

## The dual complex

| member | statement |
|---|---|
| `FreeDualComplexDef`, `FreeDualMapDef`, `freeDualHomotopyDef` | the dual complex, the transpose of a chain map, the transpose of a homotopy at the index cochain_homotopy reads |
| `FreeDualCochainComplex` | the dual of a based complex is a cochain complex — card |
| `FreeDualMapIdentity`, `FreeDualCochainMap`, `FreeDualMapCompose` | the identity transposes to the identity, a chain map to a cochain map in the opposite direction, a composite to the reversed composite — card |
| `FreeDualHomotopy` | chain homotopies transpose to cochain homotopies — card |
| `FreeDualHomotopyEquivalence` | a chain homotopy equivalence transposes to a cochain homotopy equivalence |
| `FreeDualQuasiIsomorphism` | the dual of a quasi-isomorphism is a cochain homotopy equivalence and an isomorphism on cohomology — card |
| `FreeDualSplitShortExact` | a degreewise split short exact sequence dualizes to a short exact sequence of cochain complexes — card |
| `FreeDualCoefficientShortExact` | a short exact sequence of coefficient modules gives one of the duals of a based complex, with no splitting |

## The long exact sequence of a split zigzag

| member | statement |
|---|---|
| `SplitZigzagDualLongExact` | the cohomology long exact sequence of the bottom row, with the duals of its two maps and the connecting map carried by the vertical isomorphisms — card |

The constitution's §"Structures" has the conventions a structure's axioms
and laws follow.
