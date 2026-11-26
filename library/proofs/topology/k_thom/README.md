# k_thom — Koszul projection triples and the complex Thom isomorphism

The exterior algebra of a finite projection is represented in the binary subset basis of the ambient exterior algebra ([exterior_basis](../../algebra/exterior_basis/README.md)). Its matrix entries are minors. Even and odd degree select two Hermitian projections, and wedge by the fibre vector plus its adjoint gives the Koszul map. The convention uses ΛE rather than ΛE*, so on a trivial complex line the map is z, the Bott representative fixed in bott_periodicity.

For a compact base the Koszul triple has compact support on the zero section. For a locally compact base it is a multiplier: multiplying by the pullback of a compactly supported triple gives compact support over its original support. These are separate maps, and the latter is the compact-support Thom isomorphism.

## Members

| Member | Statement or role |
|---|---|
| `exteriorDef` | Definition of `projection_exterior` |
| `koszulMapDef` | Definition of `koszul_projection_map` |
| `koszulTripleDef` | Definition of `koszul_triple` |
| `CompactThomMapDef` | Definition of `k_thom_map` |
| `ThomMapDef` | Definition of `kc_thom_map` |
| `ExteriorProjection` | Even and odd exterior powers are continuous projection bundles — card |
| `KoszulMap` | The Koszul matrix is a continuous bundle map — card |
| `KoszulInvertible` | The Koszul matrix is invertible away from the zero section — card |
| `KoszulCompactSupport` | Over a compact base the Koszul triple has compact support — card |
| `ThomCompactSupport` | Multiplying a compact relative triple by the Koszul complex preserves compact support — card |
| `ThomHomomorphism` | The compact-support Thom map is a homomorphism — card |
| `ThomIsomorphism` | The compact-support Thom map is an isomorphism — card |
| `CompactThomIsomorphism` | Over a compact base the K0 Thom map is an isomorphism — card |
| `IsomorphismPredicateDef` | Definition of `kc_thom_isomorphism` |
| `TrivialBundleThom` | A bundle isomorphic to a trivial bundle has an invertible Thom map — card |
| `TwoOpenThomGluing` | Thom isomorphisms on a two-open cover and its suspensions glue — card |
| `CompactRelationLocalization` | A relative equality is supported in a single compact set and restricts to its open neighborhoods — card |
| `TrivialExterior` | The exterior bundles of a trivial bundle are the parity diagonals — card |
