# thom_form — angular transgression, compact Thom forms and the diagonal pairing

The curvature Pfaffian transgresses on the punctured tangent bundle. A radial cutoff gives a closed Thom form with compact disk support, fiber integral one and Euler pullback along the zero section. Transport to the diagonal gives a diagonal form; any diagonal form reproduces every de Rham class, and its trace gives Gauss–Bonnet–Chern. The pairing argument also gives Poincaré duality in every dimension.

The construction uses positive orthonormal coordinates and the Pfaffian normalization Ω/(2π). Angular forms have degree n−1 for n=2m+2; GBC includes n=0 separately. Horizontal vectors precede vertical vectors in fiber integration. The finite-rank reproduction sign is (−1)^p: a degree-p second-factor form crosses a degree-p first-factor form.

## Definitions

| Member | Constant |
|---|---|
| `puncturedDef` | `tangent_punctured` |
| `connectionDifferenceDef` | `angular_connection_difference` |
| `transgressionDef` | `angular_transgression` |
| `frameChartDef` | `thom_frame_chart` |
| `localAngularDef` | `riemannian_local_angular` |
| `angularRepresentativeDef` | `riemannian_angular_representative` |
| `angularFormDef` | `riemannian_angular_form` |
| `frameFiberDef` | `thom_frame_fiber` |
| `angularVolumeDef` | `even_angular_volume` |
| `radialCutoffDef` | `thom_radial_cutoff` |
| `thomRepresentativeDef` | `riemannian_thom_representative` |
| `ThomFormDef` | `riemannian_thom_form` |
| `DiagonalFormDef` | `manifold_diagonal_form` |
| `pairingDef` | `de_rham_integral_pairing` |
| `DualityMapDef` | `de_rham_duality_map` |

## Members

| Member | Statement |
|---|---|
| `AngularRepresentativeExistsUnique` | Local transgression determines a unique global angular form — card |
| `AngularFormDerivative` | The angular derivative is the negative pullback of the Euler form — card |
| `AngularFormFiberIntegral` | Restriction to an orthonormal fiber is the normalized radial angular volume — card |
| `RadialCutoffExists` | A smooth cutoff exists between any two positive squared radii — card |
| `ThomRepresentativeExistsUnique` | The punctured and near-zero formulas glue uniquely — card |
| `ThomClosed` | The Thom form is a closed form of the fiber dimension — card |
| `ThomSupport` | The Thom support lies in the closed outer metric disk — card |
| `ThomCompactSupport` | The Thom support is compact over a compact base — card |
| `ThomFiberIntegral` | Every positively oriented fiber integral is one — card |
| `ThomZeroSection` | Zero-section pullback is the Euler form — card |
| `ThomSupportInEmbeddedDisk` | A cutoff can put the support inside any positive ambient differential disk — card |
| `DiagonalFormExists` | Every compact oriented manifold admits a diagonal form — card |
| `DiagonalEulerForm` | In positive even dimension the diagonal form pulls back to the Euler form — card |
| `DiagonalReproducing` | A diagonal form reproduces every de Rham class |
| `IntegralPairingRepresentatives` | The integral pairing agrees with the wedge integral of closed representatives — card |
| `DiagonalPairingNondegenerate` | Vanishing against all complementary classes forces a class to vanish — card |
| `DiagonalTrace` | The diagonal pullback integral is the de Rham Euler characteristic — card |
| `GaussBonnetChernZero` | The zero-dimensional Euler integral counts the points — card |
| `GaussBonnetChern` | The Euler-form integral equals the de Rham Euler characteristic — card |
| `PoincareDuality` | Complementary cohomology is the full real dual under integration — card |
| `OddEulerZero` | A compact oriented odd-dimensional manifold has Euler characteristic zero — card |
| `EulerMetricIndependent` | The Euler cohomology class is independent of the metric — card |

## Finite expansion and trace

| Member | Statement |
|---|---|
| `DiagonalExpansionReproducing` | A homogeneous diagonal expansion gives the signed finite-rank identity — card |
| `DiagonalDegreeTrace` | Its degree-p trace equals the p-th Betti number — card |
