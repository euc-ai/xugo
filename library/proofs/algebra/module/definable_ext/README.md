# definable_ext — Ext with its pointwise Polish cover and comparisons between countable resolutions

The canonical Hom complex and the Ext carrier are those of tor_ext. Their pointwise topology is an additional structure, not a second Ext construction. Countable free resolutions have countable generator sets; comparison maps and homotopies pass through the common Polish cohomology mechanism.

The canonical model and resolution comparisons use `CountableBasedDualPolish` and `BasedDualMapContinuous`. Their continuity comes from `polish_space.FiniteCoordinateContinuous`, which also handles coefficient postcomposition by reading one input coordinate for each output. The ordinary algebraic cochain-map laws and preservation of normalized carriers remain explicit obligations. `ExtResolutionDefinableIso` reads the resolution comparison through `polish_cohomology.HomotopyEquivalenceDefinableIso`: any two countable free resolutions give Borel-isomorphic Ext covers.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `extTopologiesDef` | definition | The canonical resolution fixes the generator carrier; coefficients carry the discrete topology. |
| `CanonicalResolutionCountable` | card | Induct on the canonical resolution: the initial generators are the module carrier, and each later kernel is a subset of a countable finitely supported free module. |
| `ExtPolishModel` | card | The coordinate carrier consists of generator functions normalized to zero off each generator set. Countability and finite generator expansions supply the Polish topology and continuity. |
| `ExtHasPolishCover` | card | CohomologyHasPolishCover supplies the structure and the definition of ext identifies the existing quotient carrier. |
| `ExtResolutionComparison` | card | Lift the identity of M in both directions between the free resolutions |
| `ExtResolutionDefinableIso` | card | One continuous comparison between the Hom complexes of two countable resolutions induces a Borel isomorphism of covers in every degree. |
| `ExtCoefficientMapDefinable` | card | FiniteCoordinateContinuous gives continuity of coefficient postcomposition; CohomologyDefinableFunctor gives the existing ext_map its Borel lift. |
| `ExtFirstVariableMapDefinable` | card | The canonical chain comparison transposes to a continuous map of the Hom complexes, contravariantly in the first module |
| `ExtCountableOrContinuum` | card | Ext of countable modules over a countable ring is countable or has at least continuum many elements. |
