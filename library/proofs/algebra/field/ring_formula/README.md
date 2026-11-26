# ring_formula — ring formulas interpreted over explicit field carriers

The syntax, integer polynomial atoms, variable supports and carrier semantics are shared with the ordered-ring theory. Here an atom means P = 0, so a ring formula is a formula read through vanishing, and its congruence, embedding, invariance and closed quantifier-free transfer are polynomial_formula's statements at that predicate. The closed quantifier-free transfer is between fields of the same characteristic, `same_characteristic` of algebra/field/finite_field, and is distinct from the large-characteristic stability theorem.

| Member | Statement |
|---|---|
| `RingFormulaAtomDef` | Interpret a polynomial atom as equality to zero. |
| `RingFormulaEvalDef` | Interpret a ring formula using carrier-restricted quantifiers. |
| `RingFormulaTruthDef` | Sentence truth at the zero environment. |
| `EnvironmentCongruence` | Only the free-variable environment affects ring-formula truth. |
| `ClosedEnvironment` | A closed formula has the same truth value in every environment. |
| `RingAtomEmbedding` | An injective homomorphism of the underlying commutative rings embeds the ring atoms; neither side need be a field. |
| `QuantifierFreeEmbedding` | An injective homomorphism of the underlying commutative rings preserves and reflects quantifier-free truth. |
| `IsomorphismInvariant` | An isomorphism of the underlying commutative rings preserves every ring formula. An onto homomorphism is not enough, since a ring homomorphism reflects vanishing only when it is one-to-one; the ordered twin, [`OntoInvariant`](../ordered_ring_formula/README.md), reflects negativity through the order and needs no one-to-one map. |
| `TransportFieldInvariant` | A formula's value in a field at an environment is unchanged by transport along a carrier injection. |
| `TransportAlgebraicallyClosed` | Algebraic closedness is preserved by transport along a carrier injection. |
| `EliminationAlongInjection` | A quantifier-free equivalent over the algebraically closed fields on one type is one over those on any type that injects into it. |
| `QuantifierFreeSentenceTransfer` | Fields of the same characteristic agree on closed quantifier-free ring formulas. |
