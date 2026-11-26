# smooth_singular — smooth singular simplices, chains and simplex integration

Smooth singular simplices are normalized maps which extend smoothly to a neighbourhood of the affine simplex. Their faces and degeneracies are the continuous singular ones. Integration uses the ordered simplex vertices and is independent of the extension; the simplex Stokes formula makes it a cochain map. Smooth subdivision and prism homotopies supply the cover and homotopy interfaces.

A simplex is smooth up to all faces because it extends beyond them. Its stored total map is normalized to junk off the simplex and is not itself required to be globally smooth. The affine coordinates use vertex order 0,1,…,k and the boundary sign (−1)^i.

## Definitions

| Member | Constant |
|---|---|
| `simplexExtensionDef` | `smooth_simplex_extension` |
| `simplicesDef` | `smooth_singular_simplices` |
| `SingularSetDef` | `smooth_singular_set` |
| `ChainComplexDef` | `smooth_singular_complex` |
| `CohomologyModuleDef` | `smooth_singular_cohomology_module` |
| `CohomologyPullbackDef` | `smooth_singular_cohomology_pullback` |
| `affineCoordinatesDef` | `simplex_affine_coordinates` |
| `simplexIntegralDef` | `smooth_simplex_integral` |
| `IntegrationDef` | `de_rham_integration_cochain` |
| `IntegrationClassDef` | `de_rham_integration_class` |

## Members

| Member | Statement |
|---|---|
| `SmoothSingularSet` | Smooth singular simplices form a simplicial subset of the continuous ones — card |
| `OpenSubmanifoldSingularSet` | The smooth singular set of an open submanifold is the smooth singular set restricted to it — card |
| `SmoothSingularMap` | Smooth maps induce maps of smooth singular simplicial sets — card |
| `SimplexIntegralExtension` | The simplex integral is independent of the chosen smooth extension — card |
| `SimplexStokes` | The simplex integral of an exterior derivative is the alternating face integral — card |
| `IntegrationCochain` | Integration is a cochain map from differential forms to smooth singular cochains — card |
| `IntegrationNaturality` | Integration commutes with smooth pullback — card |
| `SmallChainsQuasiIsomorphism` | Smooth small chains compute smooth singular homology — card |
| `SmallCochainsQuasiIsomorphism` | Restriction to an open cover’s small simplices preserves cohomology — card |
| `HomotopyChainHomotopy` | Smooth homotopies induce chain homotopies on smooth singular chains — card |
| `HomotopyInvariance` | Smoothly homotopic maps induce equal smooth singular cohomology maps — card |
| `MayerVietoris` | Two open sets give the full cohomology Mayer–Vietoris sequence — card |

## Cover naturality

| Member | Statement |
|---|---|
| `ConnectingNaturality` | The connecting map commutes with maps preserving both cover pieces — card |
| `MayerVietorisInitial` | The degree-zero restriction into the cover is injective — card |
