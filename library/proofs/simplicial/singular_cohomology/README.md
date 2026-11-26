# singular_cohomology — real singular cochains, cover sequences and evaluation on homology

Real cochains are arbitrary functions on singular simplices, normalized to zero elsewhere. The same construction accepts the smooth singular simplicial subset. Restriction to small simplices gives the two-open Mayer–Vietoris sequence, including its connecting map and naturality. Evaluation identifies cohomology with the real dual of homology.


## Definitions

| Member | Constant |
|---|---|
| `ComplexOfDef` | `singular_cochain_complex_of` |
| `ComplexDef` | `singular_cochain_complex` |
| `PullbackOfDef` | `singular_cochain_pullback_of` |
| `PullbackDef` | `singular_cohomology_pullback` |
| `RestrictedSetDef` | `singular_restricted_set` |
| `SmallSetDef` | `singular_small_set` |
| `RestrictionDef` | `singular_cochain_restriction` |
| `CohomologyRestrictionDef` | `singular_cohomology_restriction` |
| `CoverComplexDef` | `singular_cover_complex` |
| `CoverRestrictionDef` | `singular_cover_restriction` |
| `CoverDifferenceDef` | `singular_cover_difference` |
| `ConnectingDef` | `singular_cohomology_connecting` |
| `EvaluationDef` | `singular_cohomology_evaluation` |
| `BettiDef` | `singular_betti` |
| `EulerDef` | `singular_euler` |

## Members

| Member | Statement |
|---|---|
| `CochainComplex` | Real singular cochains form a cochain complex — card |
| `UniversalCoefficient` | Evaluation identifies cohomology with the full algebraic dual of homology — card |
| `PullbackCochain` | Postcomposition of simplices induces a cochain pullback — card |
| `SmallCochainsQuasiIsomorphism` | Restriction to an open cover’s small simplices preserves cohomology — card |
| `SubspaceSingularSet` | The singular set of a subspace is the singular set restricted to it — card |
| `CoverLongExact` | A small-cochain cover comparison gives all three exactness positions — card |
| `MayerVietoris` | Two open sets give the full cohomology Mayer–Vietoris sequence — card |

## Cover naturality

| Member | Statement |
|---|---|
| `ConnectingNaturality` | The connecting map commutes with maps preserving both cover pieces — card |
| `MayerVietorisInitial` | The degree-zero restriction into the cover is injective — card |
