# de_rham_comparison — natural comparison with real singular cohomology

Integration and restriction from continuous to smooth singular cochains form a natural comparison through smooth singular cohomology. Convex opens give the local calculation, the three Mayer–Vietoris sequences extend it to finite box unions, and smooth retractions give the compact-manifold theorem. Evaluation on homology identifies Betti numbers and gives the topological form of Gauss–Bonnet–Chern.

The comparison is Ω• → C•∞ ← C•. Both arrows are isomorphisms on compact manifolds; restriction points from continuous to smooth cochains. Noncompact comparison, cup products and other coefficient rings are outside these statements.

The general connecting and gluing statements take the de Rham cover sequence’s short exactness as an explicit hypothesis. For finite Euclidean box unions, the existing open-set partition theorem supplies the two weights and hence that sequence. The compact-manifold comparison therefore uses the finite-box and retract route without requiring a general noncompact comparison theorem.

## Definitions

| Member | Constant |
|---|---|
| `ComparisonDef` | `de_rham_comparison` |

## Members

| Member | Statement |
|---|---|
| `RestrictionCochain` | Continuous-to-smooth restriction is a cochain map — card |
| `ComparisonHomomorphisms` | Both intermediate comparison maps are linear on cohomology — card |
| `RestrictionNaturality` | Continuous-to-smooth restriction commutes with smooth maps — card |
| `IntegrationClassNaturality` | Integration commutes with smooth pullback on cohomology classes — card |
| `IntegrationConnecting` | Integration commutes with the Mayer–Vietoris connecting map — card |
| `RestrictionConnecting` | Continuous-to-smooth restriction commutes with connecting maps — card |
| `EmptyComparison` | Both intermediate comparisons are isomorphisms on the empty manifold — card |
| `ConvexComparison` | Both comparisons are isomorphisms on convex Euclidean opens — card |
| `MayerVietorisComparison` | The comparisons glue across a two-open cover — card |
| `FiniteBoxUnionComparison` | Both comparisons are isomorphisms on finite unions of open boxes — card |
| `RetractComparison` | Comparison isomorphisms pass to smooth retracts — card |
| `CompactComparison` | Both intermediate comparisons are isomorphisms on compact manifolds — card |
| `DeRhamTheorem` | Integration and inverse restriction give real singular cohomology — card |
| `ComparisonNaturality` | The de Rham comparison is natural between compact smooth manifolds — card |
| `SingularHomologyFinite` | Compact smooth manifolds have finite-dimensional real singular homology — card |
| `SingularHomologyAboveDimension` | Real singular homology vanishes above the compact manifold dimension — card |
| `BettiComparison` | de Rham and real singular homology Betti numbers coincide — card |
| `EulerComparison` | de Rham and topological Euler characteristics coincide — card |
| `TopologicalGaussBonnetChern` | The Euler-form integral equals the topological Euler characteristic — card |
