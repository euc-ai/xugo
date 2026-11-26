# curve_cover — finite separable covers of curves, the inverse different and Riemann–Hurwitz

A cover has two curves over the same k and transcendental coordinate t, with chart inclusions and finite free chart bases that are also bases of the function-field extension. A separable primitive lies in L, and need not be regular on either chart. Pullback extends each chart module by its source chart ring.

The function field is a `field_ops(A)` record F: `curve_cover(F, K, k,
t, A₀, A₁, A₀₁, B₀, B₁, B₀₁)` uses `restrict_field(F, K)` for the
base field. Degree and pullback take the ring record `field_ring(F)`;
the inverse different, different and ramification degree take F itself
because they use its field trace.

The inverse different is the pair C_i={z∈L | Tr(z B_i)⊆A_i}, the trace dual of algebra/field/trace_dual read at the two chart rings: that chapter supplies its module structure, its localization to the overlap, its behaviour under an invertible value module and the derivative formula of the monogenic case. Trace duality identifies it with relative Hom, using precomposition as the source-ring action. A carrier-guarded adjunction identifies ω_X with f*N·C for any invertible model N of ω_Y. If both dualizing pairs admit invertible field-valued models, C is invertible and its degree is the ramification degree.

Riemann–Hurwitz reads 2g_X−2=n(2g_Y−2)+deg C. Every quotient degree uses both charts minus the overlap; the theorem applies to arithmetic genus and does not assume smoothness. A monic presentation uses separate generators on the charts and includes the exact evaluation kernel. Its different is chart-principal; the final Kähler comparison is equality of chart annihilator ideals.

The ramification label does not assert a divisor supported on rational regular points. Splitting fields, trace transitivity, ramification indices, tame/wild formulas and hyperelliptic generalization are outside this chapter. Weierstrass examples are in scheme/elliptic_curve, which imports this chapter.

## Members

### Definitions

| Member | Statement |
|---|---|
| `CurveCoverDef` | A finite free separable covering of two curves over the same line. |
| `CoverDegreeDef` | The degree of the function-field extension. |
| `CoverPullbackDef` | Scalar extension of both chart modules to the source curve. |
| `coverPullbackAmbientDef` | Scalar extension of an overlap module. |
| `InverseDifferentDef` | The pair of trace-dual chart rings. |
| `DifferentDef` | The inverse lattice pair of the inverse different. |
| `coverHomPairDef` | The chartwise relative Hom conditions in an overlap coextension. |
| `RamificationDegreeDef` | The degree of the inverse-different lattice pair. |
| `riemannHurwitzDataDef` | A covering with invertible dualizing models on both curves. |
| `MonicCoverDef` | Two exact monic chart presentations with their own separable generators. |

### Pullback

| Member | Statement |
|---|---|
| `CoverDegreeCharts` | Both extension bases have the positive cover degree as their size. — card |
| `CoverOverlapBasis` | A chart-zero extension basis remains a basis on the overlap. — card |
| `CoverPullbackDirectSum` | A pulled-back chart module has unique coefficients along the extension basis. — card |
| `CoverPullbackLattice` | Pullback is a lattice pair with the scalar-extended overlap ambient. — card |
| `CoverPullbackStructure` | Pullback carries the base structure pair to the source structure pair. — card |
| `CoverPullbackMul` | Pullback preserves products of lattice pairs. — card |
| `CoverPullbackInvertible` | Pullback preserves invertibility and its inverse. — card |
| `CoverPullbackQuotientDim` | Pullback multiplies each finite quotient dimension by the cover degree. — card |
| `CoverPullbackSubpairFinite` | Finiteness descends to a subpair and its pullback through finite chart quotients. — card |
| `CoverPullbackEuler` | Pullback multiplies a finite subpair Euler difference by the cover degree. — card |
| `CoverPullbackFinite` | An invertible pair has finite cohomology after pullback. — card |
| `CoverDegreeMultiplicative` | Pullback multiplies the degree of an invertible pair by the cover degree. — card |

### Trace dual

| Member | Statement |
|---|---|
| `TraceDualSubmodule` | The trace dual is a module under the source chart ring. — card |
| `TraceDualContainsStructure` | The inverse different contains the structure rings on both charts and their overlap. — card |
| `TraceDualHomIso` | Trace pairing identifies a chart trace dual with its coextension Hom module. — card |
| `TraceDualLocalizes` | Both chart trace duals extend to the same overlap trace dual. — card |
| `InverseDifferentLattice` | The inverse different is a lattice pair with the overlap trace dual as ambient. — card |
| `TraceDualOfInvertible` | The trace dual of an invertible base module is its product with the inverse different. — card |

### Duality

| Member | Statement |
|---|---|
| `DualizingAdjunction` | The source dualizing pair is the relative Hom pair of the base dualizing pair. — card |
| `HomToModelIsTraceDual` | A base dualizing model identifies relative Hom with its product with the inverse different. — card |
| `HomPairLocalizes` | The model identification uses a common overlap trace dual. — card |
| `DualizingBridge` | The source dualizing pair is isomorphic to the pulled-back base model times the inverse different. — card |
| `InverseDifferentInvertible` | Invertible dualizing models on both curves make the inverse different invertible. — card |
| `DifferentIsIdeal` | The different consists of chart ideals in the structure pair. — card |
| `InverseDifferentQuotientFinite` | The inverse-different quotients on both charts and the overlap are finite-dimensional. — card |

### Riemann–Hurwitz

| Member | Statement |
|---|---|
| `RamificationDegreeFormula` | The ramification degree is the two chart colengths minus the overlap colength. — card |
| `RamificationDegreeNonneg` | The ramification degree is nonnegative. — card |
| `UnramifiedIff` | Ramification degree zero is equivalent to a trivial inverse different. — card |
| `PullbackDualizingDegree` | The pulled-back dualizing degree is the cover degree times twice the base genus minus two. — card |
| `RiemannHurwitz` | The canonical degree of the source is the pulled-back canonical degree plus ramification. — card |
| `RiemannHurwitzInequality` | The canonical degree inequality and genus monotonicity follow from nonnegative ramification. — card |
| `CoverOfLineUnramifiedTrivial` | An unramified cover of a genus-zero base has degree one and genus zero. — card |

### Monic

| Member | Statement |
|---|---|
| `MonicCoverFree` | The short powers of each monic chart generator form its chart basis. — card |
| `MonicCoverPrimitive` | Each chart generator generates the function field and its chart equation is the separable minimal polynomial. — card |
| `MonicCoverIsCover` | Exact monic presentations supply a covering whose degree is each chart polynomial degree. — card |
| `MonicCoverTraceDual` | The inverse different on a monic chart is the chart ring divided by the derivative value. — card |
| `MonicCoverDifferent` | The different on each monic chart is generated by the derivative value. — card |
| `MonicCoverInvertible` | The inverse different of a monic cover is invertible. — card |
| `MonicCoverDualizingInvertible` | A monic cover carries a base dualizing model to a source dualizing model. — card |
| `MonicCoverOverlapDifferent` | The two derivative ideals agree after extension to the overlap. — card |
| `MonicCoverRamificationDegree` | Derivative quotient dimensions give the monic-cover ramification degree with the overlap subtracted. — card |
| `DifferentIsKaehlerAnnihilator` | The chart different is the annihilator of relative Kähler differentials. — card |
