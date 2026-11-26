# ordered_ring_formula — ordered-ring formulas interpreted over explicit field carriers

An atom is P < 0, so an ordered formula is a formula read through negativity, and its congruence, embedding, invariance and closed quantifier-free transfer are polynomial_formula's statements at that predicate. Interpretation reuses first_order and polynomial_formula, with existential variables restricted to the field carrier. Sentence truth is evaluated at the zero environment; environment independence is a theorem, not an assumption that the host type is the carrier.

| Member | Statement |
|---|---|
| `OrderedRingFormulaAtomDef` | Interpret an integer-polynomial atom as strict negativity. |
| `OrderedRingFormulaEvalDef` | Interpret a formula in an ordered carrier field. |
| `OrderedRingFormulaTruthDef` | Sentence truth at the zero environment. |
| `EnvironmentCongruence` | Only the free-variable environment affects truth. |
| `ClosedEnvironment` | A closed formula has the same truth value in every environment. |
| `OrderedAtomEmbedding` | A ring homomorphism that preserves and reflects the order embeds the ordered atoms; no ordered field is required. |
| `QuantifierFreeEmbedding` | A ring homomorphism that preserves and reflects the order preserves and reflects quantifier-free truth; no ordered field is required. |
| `OntoInvariant` | A ring homomorphism onto the target carrier that preserves and reflects the order preserves every formula; neither an ordered field nor a one-to-one map is required. |
| `TransportOrderedFieldInvariant` | A formula's value in an ordered field at an environment is unchanged by transport along a carrier injection. |
| `TransportRealClosedField` | Real closedness is preserved by transport along a carrier injection. |
| `EliminationAlongInjection` | A quantifier-free equivalent over the real closed fields on one type, each with its order, is one over those on any type that injects into it. |
| `QuantifierFreeSentenceTransfer` | All ordered fields agree on closed quantifier-free ordered-ring formulas. |
