# functional_dual — lattice duals from nonzero linear functionals

A K-linear functional l on a field L makes (x,y) ↦ l(xy) a K-bilinear map, and a nondegenerate one when l is nonzero; neither finiteness nor separability enters. `functional_dual(R, l, B, N)` is the set of z in the ring whose products with B have their l-values in N. Its B-stability, the test on generators and its commutation with saturation need only linearity and, for saturation, finite generation. Over a finite free S-lattice B and a nonzero functional the dual is a bounded fractional ideal, and an invertible one when the nonzero ideals of B are invertible.

`pairing.go` holds the multiplication pairing and its dual basis. `lattices.go` holds the dual of a lattice: `FunctionalDualAdditive` is what the two submodule members share, and `FunctionalDualBounded` is one argument in two sections and a close, the dual basis, the span bound and a common denominator of the span. `saturation.go` is `FunctionalDualSaturation`, its two inclusions in order.

## Members

| Member | Statement |
|---|---|
| `FunctionalDualDef` | The elements of the ring whose products with B have their l-values in N. |
| `FunctionalDualMember` | z lies in `functional_dual(R, l, B, N)` exactly when it lies in the ring and every product with a member of B has its l-value in N |
| `MultiplicationFunctionalBilinear` | A K-linear functional on L makes (x, y) ↦ l(xy) a K-bilinear map |
| `MultiplicationFunctionalNondegenerate` | A nonzero K-linear functional on L gives a bilinear, nondegenerate multiplication pairing |
| `MultiplicationFunctionalDualBasis` | A nonzero K-linear functional gives a finite K-basis E of L a dual basis d under l: l(d(e)f) = δ(e, f) on E, and every x is the sum over E of l(xe)d(e) |
| `FunctionalDualGenerators` | Testing on S-module generators of B gives the same functional dual |
| `FunctionalDualAdditive` | Under an additive map fixing zero, the functional dual of any subset of L against a set holding zero and closed under addition holds zero and is closed under addition |
| `FunctionalDualSubmodule` | The functional dual of an S-submodule of K is a B-submodule of L |
| `FunctionalDualOverScalars` | Under an S-linear functional, the functional dual of any subset of L against an S-submodule of K is an S-submodule of L |
| `FunctionalDualBounded` | The dual of a finite free S-lattice B under a nonzero K-linear functional is a bounded fractional ideal of B |
| `FunctionalDualBoundedInvertible` | The dual of a finite free S-lattice B is bounded and invertible when every nonzero integral B-ideal is invertible |
| `FunctionalDualSaturation` | For finitely generated B, the dual of the saturations of B and N at s is the saturation of the dual at s, at every s |
| `FunctionalDualSubset` | The dual of B valued in N lies in the ring |
| `FunctionalDualOnBasis` | The test of the dual need only be run on a basis E of B over S |
| `FunctionalDualChartImage` | The pairing map carries the dual of a chart X valued in P onto the maps taking X into P |
| `FunctionalDualValueScale` | Scaling the target of a dual by a nonzero scalar w of F scales the dual |
| `SubringInFieldSubmodule` | A subring of M inside a subfield F is a submodule of F over itself |
| `FunctionalCoordinates` | For a nonzero functional l, the values z ↦ l(z * e) on a finite F-basis E of L are free coordinates on L |
| `FunctionalPairingInHomSet` | Pairing with a member of the dual, zero off B, is an S-linear map from B into N |
| `FunctionalPairingHomomorphism` | The pairing map is B-linear from the dual into the S-linear maps, B acting through the argument |
| `FunctionalPairingBijective` | On a common basis of B over S and L over F, the pairing map is one-to-one and fills the hom set |
| `FunctionalDualHomIso` | z ↦ (b ↦ l(z * b)) is a B-linear isomorphism of the dual onto the S-linear maps from B into N |
| `NonzeroLinearFunctional` | A finite extension carries a nonzero linear functional |
