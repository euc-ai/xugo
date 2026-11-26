# definable_andre_quillen — Polish covers and definable maps for André–Quillen cohomology

The standard cotangent cochain complex and its quotient module are unchanged. Countability is imposed on the ring carriers and coefficients, not on the ambient host type. The host-capacity hypothesis remains explicit. Standard names are countable by induction even when the host is uncountable. Comparisons must be actual regular maps of the cochain models; no arbitrary algebraic isomorphism is promoted to a definable one.

`AndreQuillenPolishModel` uses the existing [cotangent_complex](../cotangent_complex/README.md) interface: `CotangentScalarBased` supplies the based complex and `CotangentDualAgreement` identifies its dual with the stated cotangent cochains. `StandardNamesCountable` and `polish_cohomology.CountableBasedDualPolish` then supply the Polish cochain model. Both cotangent interface entries remain cards, as do all theorem members here.

The shared based-dual argument uses `polish_space.FiniteCoordinateContinuous` for the transpose differential. Coefficient postcomposition also reads one input coordinate at each output, while finite-sum linearity supplies commutation with the differential and preservation of normalized inactive values. `CohomologyDefinableFunctor` then gives the coefficient map on the covered cohomology groups.

## Resolutions and comparisons

`resolutions.go` equips the dual of any polynomial resolution with countable
names with its pointwise Polish model. The underlying scalar complex is
based by those names through `cotangent_complex.DifferentialScalarBased`,
which needs neither countability nor the resolution's acyclicity.
`ResolutionComparisonDefinableIso` uses the transpose of a specified
comparison covering the identity of the augmented algebra. Algebraic
homotopies suffice: only the comparison maps need be continuous.
The comparison theorem makes any two lifts of the identity homotopic,
and the duality and cohomology functors supply identity and composition
compatibility. An arbitrary abstract isomorphism supplies none of these data.

`AQScalarPolishModel` reads standard cochains with coefficients over a ring
beyond the augmented algebra. The scalar ring need not be countable;
countability concerns the names and the coefficient carrier.

## Maps and exact sequences

`functoriality.go` gives the actual right map of a tower its continuous
transpose lift. The continuity statement has no countability assumption.
With countable data it becomes a map of Polish covers. For a localization
the right map has a Borel inverse, and composing this inverse with a
coefficient map gives the existing restriction. The latter is stated on
additive groups because its two cohomology modules have different scalars.

`sequences.go` gives the named arrows of the coefficient and transitivity
long exact sequences their Borel lifts. Relative names and total-degree
bases are countable; dualizing the split sequence of based totals gives the
Polish cochain sequence used for transitivity. The connecting lifts use
Borel sections and the actual edge comparisons. They are not asserted
continuous. Exactness remains the algebraic chapters' theorem.

## Low degrees

`low_degrees.go` identifies the cocycle spaces with concrete pointwise
models. The two conversions of
`cohomology_one` are inverse homeomorphisms, and they carry actual
coboundaries to restrictions of derivations. No closure replaces the
boundary subgroup. Degree-zero cocycles are homeomorphic to derivations
on the algebra carrier, normalized to zero elsewhere; the bare
`derivation_on` predicate does not impose that normalization.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `AQTopologiesDef` | definition | Discrete coefficient values on the standard resolution names in each degree. |
| `StandardNamesCountable` | card | The initial names are the image of the countable target carrier |
| `AndreQuillenPolishModel` | card | Use CotangentScalarBased and CotangentDualAgreement with StandardNamesCountable and CountableBasedDualPolish. Countability concerns carriers; the explicit host capacity also supplies the target-ring host capacity. |
| `AndreQuillenHasPolishCover` | card | Apply CohomologyHasPolishCover to AndreQuillenPolishModel |
| `AndreQuillenCoefficientMapContinuous` | card | Coordinatewise postcomposition is continuous by FiniteCoordinateContinuous and commutes with each finite Jacobian-transpose sum. |
| `AndreQuillenCountableOrContinuum` | card | André–Quillen cohomology of countable rings with countable coefficients is countable or has at least continuum many classes. |
| `PolynomialResolutionDualPolish` | card | A polynomial resolution with countable names and coefficients gives a Polish dual complex and cohomology covers — card |
| `ResolutionComparisonDefinableIso` | card | The transpose of a comparison over the identity is continuous and induces a Borel isomorphism in every degree — card |
| `AQScalarPolishModel` | card | Standard AQ cochains with coefficients over a further scalar ring form a Polish model — card |
| `AQAlgebraMapContinuous` | card | The right map's transpose is continuous without countability assumptions — card |
| `AQAlgebraMapDefinable` | card | The named algebra map on AQ has a Borel lift — card |
| `AQCoefficientSequenceDefinable` | card | Both coefficient arrows and the connecting arrow of the long exact sequence have Borel lifts — card |
| `TriangleNamesCountable` | card | Relative names, column names and the bases of their totals are countable — card |
| `AQTransitivityDefinable` | card | The three named arrows of the transitivity sequence have Borel lifts — card |
| `AQLocalizationDefinable` | card | The localization right map is an isomorphism of Polish covers — card |
| `AQRestrictionDefinable` | card | Localization restriction with a coefficient map has a Borel lift on additive groups — card |
| `ConormalModelHomeomorphism` | card | The explicit degree-one cocycle–conormal conversions are inverse homeomorphisms — card |
| `ConormalCoboundariesCorrespond` | card | The homeomorphism carries coboundaries onto derivation restrictions — card |
| `DerivationModelHomeomorphism` | card | Degree-zero cocycles are homeomorphic to normalized derivations — card |

The [chapter constitution](../../../../chapter_constitution.md) describes
the common card and verification conventions.

## Unions and phantom classes

The increasing-union interface uses images of induced name maps, since independently chosen carrier tags are not literal nested subsets. Stage cochains share the final scalar ring. Their degreewise surjective Polish tower has the global AQ complex as its homeomorphic limit. Milnor connecting maps give the positive-degree exact sequence; degree zero is stated separately. Phantom degree-one classes have the lim-one cover of the normalized derivation tower, with Borel representative maps in both directions and a zero-or-continuum alternative.

| Member | Status | Statement and purpose |
|---|---|---|
| `aqUnionInverseDef` | definition | Glue a compatible sequence of stage cochains to the unique normalized global cochain. |
| `AQPhantomRepresentativesDef` | definition | Global degree-one AQ cocycles whose class restricts to zero at every stage. |
| `PhantomExtensionsDerivedLimit` | card | The lim-one cover is the genuine Polish tower of derivations, not a tower of discrete cochain terms. — card |
| `PhantomZeroOrContinuum` | card | Apply PolishDerivedLimitZeroOrContinuum to the zero-cocycle tower and transfer its two alternatives through the injective phantom comparison. — card |
| `AQUnionTowerDef` | definition | Each stage uses the final coefficient ring S and its module N; the scalar ring is common to the tower. |
| `AQUnionTransitionDef` | definition | Restriction along the injective name map, normalized off the source names. |
| `aqUnionComparisonDef` | definition | The canonical comparison sends a cochain on the union to its compatible stage restrictions. |
| `AQUnionComplexLimit` | card | StandardResolutionUnion gives compatible injective name maps and the union of their images. — card |
| `AQTowerPolishModel` | card | Each stage is countable as a subset of S. — card |
| `AQMilnorSequence` | card | Positive degrees use n+1 so no negative natural-number degree is hidden. — card |
| `AQMilnorDegreeZero` | card | There are no incoming degree-zero boundaries. — card |
