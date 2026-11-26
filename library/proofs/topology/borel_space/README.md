# borel_space — Borel sets and maps on explicit topological carriers

The sigma algebra and the inverse images are relative to the space carrier. A Borel map is a measurable map between the Borel sigma algebras and carries points into the target space. The carrier-relative sigma algebra is defined in `sets/sigma_algebra`. No standard Borel structure on a quotient is presumed.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `BorelSetsDef` | definition | The smallest sigma algebra on the space containing its open sets. |
| `BorelMapDef` | definition | Only the values of f on the source carrier enter measurability. |
| `BorelSigmaAlgebra` | theorem | `sigma_algebra_on(⋃T, borel_sets(T)) ∧ T ⊆ borel_sets(T)`: the Borel sets are a σ-algebra on the union of T holding T, for any family T of sets. |
| `ContinuousMapBorel` | theorem | A continuous map is Borel: the open sets generate the target's Borel sets, and their inverse images are open (measurable_space.MeasurableGenerated). |
| `BorelMapCompose` | theorem | Borel maps compose, as measurable maps do (measurable_space.MeasurableCompose). |
