# serre_duality — the dualizing pair of a curve finite over the projective line, Serre duality, and Riemann–Roch

Duality is read off the projective line (scheme/projective_line_duality).
The curve (scheme/algebraic_curve) is finite over the line, f say, so
its dualizing pair ω is $f^!(O(-2))$, built as the coextension dual $\operatorname{Hom}_{k[t, 1/t]}(A_{01}, k[t, 1/t])$: in that module of
k[t, 1/t]-linear maps from the overlap into k[t, 1/t], a module over the
overlap by coextension of scalars, chart 0 is the maps carrying A₀ into
k[t] and chart 1 the maps carrying A₁ into t⁻² · k[1/t]; no trace map is
built. Evaluation at one turns a map M → ω into a map of M, read
on the line, into O(−2), and the line's duality by coefficient
extraction makes Hom(M, ω) the dual of H¹(M) for every lattice pair of
the curve. No splitting into the pairs O(n) and no differential forms
enter, and the curve may be singular: g is then the arithmetic genus.
Riemann–Roch, ℓ(M) − dim Hom(M, ω) = deg M + 1 − g, follows from
χ(M) = deg M + 1 − g (scheme/curve_degree) and Serre duality, every number in it finite
because M is invertible; at the pair O(D) of a divisor, which is invertible
of degree deg D, it reads ℓ(O(D)) − dim Hom(O(D), ω) = deg D + 1 − g. An invertible model N of ω, an invertible pair
onto which an isomorphism carries ω, measures Hom(X, ω) by the sections
of N · X⁻¹, and Riemann–Roch at N gives it degree 2g − 2.

## Members

### The dualizing pair and Serre duality

| Member | Statement |
|---|---|
| `CurveDualizingModuleDef` | `curve_dualizing_module(field_ring(L), k, t, A₀₁)`: the k[t, 1/t]-linear maps from A₀₁ into k[t, 1/t], a module over A₀₁ |
| `CurveDualizingPairDef` | `curve_dualizing_pair(L, k, t, A₀, A₁, A₀₁)`: ω, the maps carrying A₀ into k[t] and A₁ into t⁻² · k[1/t] |
| `CurveDualizingMapsDef` | `curve_dualizing_maps(L, k, t, A₀, A₁, A₀₁, M)`: Hom(M, ω), the maps of lattice pairs from M into ω |
| `DualizingModuleOn` | k[t, 1/t] is a ring inside the overlap, its inclusion there a ring map, the overlap a module over it, and the dualizing container a module over the overlap |
| `DualizingChartSubmodule` | the maps of the container carrying a subring S of the overlap into a set holding zero and closed under sums are a submodule over S |
| `DualBasisSpans` | the coordinate functionals of a finite basis of the overlap over k[t, 1/t] are maps of the container and span it over the overlap |
| `ContainerMapsAgreeOnBasis` | two maps of the container that agree on a finite basis of the overlap over k[t, 1/t] are equal |
| `DualizingChartsSpan` | each chart of ω spans the whole container |
| `DualizingIsLattice` | ω is a lattice pair over the overlap whose ambient is the whole container |
| `HomDualizingSections` | evaluation at one is an isomorphism Hom(O, ω) → H⁰(ω) |
| `DualizingMapsOnLine` | evaluation at one is a k-isomorphism from Hom(M, ω) onto the maps of M on the line into O(−2) |
| `SerreDualityPairing` | for every lattice pair M, Hom(M, ω) is the k-dual of H¹(M) by the coefficient of t⁻¹ of the map read on the line |
| `SerreDuality` | for an invertible pair M, H¹(M) and Hom(M, ω) are finite-dimensional of one dimension |
| `GenusDual` | g = ℓ(ω) |
| `DualizingModelDef` | `dualizing_model(L, k, t, A₀, A₁, A₀₁, N)`: N is an invertible pair and an isomorphism of lattice pairs carries ω onto it |
| `DualizingInvertibleDef` | `dualizing_invertible(L, k, t, A₀, A₁, A₀₁)`: ω has an invertible model |
| `InvertibleEndomorphisms` | End(M) = k: the endomorphisms of an invertible pair M are a space of dimension one over k |
| `DualizingMapsDimension` | for a model N of ω and an invertible pair X, dim Hom(X, ω) = ℓ(N · X⁻¹) |
| `DualizingDegree` | a model of ω has degree 2g − 2 |
| `LineDualizingModel` | on the projective line, O(−2) is a model of ω, by evaluation at one — card |
| `DualizingDegreeLine` | on the projective line, the model O(−2) has degree −2 — card |

### Riemann–Roch

| Member | Statement |
|---|---|
| `RiemannRoch` | ℓ(M) − dim Hom(M, ω) = deg M + 1 − g for an invertible pair M, every number finite |
| `RiemannRochDivisor` | ℓ(O(D)) − dim Hom(O(D), ω) = deg D + 1 − g |
