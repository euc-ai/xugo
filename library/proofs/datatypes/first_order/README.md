# first_order — named-variable first-order formulas with parameterized atoms

The four constructors are atom, negation, conjunction and named existential quantification. Atoms, their free-variable support and their interpretation are parameters. Quantifiers range over an explicit carrier, and variable names are natural numbers rather than binding depths. This makes the syntax reusable for ordered-ring and ring theories.

The chapter proves four groups of facts, each a section below: the syntax and its semantics, with finite support and environment congruence; the environments legal on a support; blocks of consecutive names and finite conjunctions; and quantifier elimination with the transfer it gives along embeddings and between models. [Integer polynomial atoms](../../algebra/ring/polynomial/polynomial_formula/README.md) instantiate the atoms, interpreted over field carriers by [ring formulas](../../algebra/field/ring_formula/README.md) and [ordered-ring formulas](../../algebra/field/ordered_ring_formula/README.md).

The letters are fixed across the chapter: A is the atom type, B and C are element types and D and E model types, T₁ and T₂ are classes of models and K₁ and K₂ families of carriers indexed by the models, written T and K alone where only one class appears, and X and Y are single carriers, a set of B and a set of C. The members on environments alone name no atom, and there A is the type of the values and X a set of A.

## Syntax and semantics

An existential at a name ranges over the carrier values written at that name, the other names keeping theirs. `ExistsQuantifierBridge` and `ForallQuantifierBridge` read such a quantifier, under any evaluator, as a quantifier over the carrier for the elementarity step's bridge proof: "Bridge" in their names marks that one job, where the chapter's other members say …Semantics and Eval…, and the engine cites them by these names. Both take one body hypothesis, which the block bridges of [polynomial_encoding](../../algebra/ring/polynomial/polynomial_encoding/README.md) take on their blocks: at every carrier-valued τ that agrees with σ below the quantified name s and reads x at s, Q(x) holds exactly when the body holds at τ. It is the reifier's increasing-name rule: a quantifier's names lie above every name already in use, so the body reads the names around it below s.

| Member | Statement |
|---|---|
| FormulaInduction / FormulaRecursion / FormulaInjective / FormulaDistinct | The four-constructor datatype principles. |
| `EnvUpdateDef` | Updating one named variable leaves all other names unchanged. |
| `EnvOKDef` | Only variables in the specified support must be assigned carrier elements. |
| `FreeVarsDef` | Free variables are the union of atomic supports with each quantified name removed. |
| `WellFormedDef` | Well-formed formulas have valid atoms. |
| `QuantifierFreeDef` | Quantifier-free formulas contain no existential constructor. |
| `EvalDef` | Semantics use carrier-restricted quantification and ordinary named-variable shadowing. |
| `ForallDef` | Universal quantification is the usual derived connective. |
| `ImpliesDef` | Implication is expressed using negation and conjunction. |
| `OrDef` | Disjunction is expressed using negation and conjunction. |
| `IffDef` | The biconditional is the conjunction of the two implications. |
| `UpdateShadow` | A later binding of the same name overrides the earlier one. |
| `UpdateCommute` | Updates at distinct names commute. |
| `FreeVarsFinite` | Finite atomic supports give finite formula support. |
| `ExistsSupportBelow` | An existential at the name k leaves names below k when its body's lie below k + 1. |
| `WellFormedMono` | A formula valid for one atom predicate is valid for any weaker one. |
| `EvalForall` | The derived universal quantifier ranges over the carrier. |
| `ExistsQuantifierBridge` | An existential quantifier at a name reads as an existential quantifier over the carrier, under any evaluator. |
| `ForallQuantifierBridge` | A universal quantifier at a name reads as a universal quantifier over the carrier, under any evaluator. |
| `OrSemantics` | A disjunction holds exactly when one of its disjuncts does. |
| `ImpliesSemantics` | An implication holds exactly when its antecedent fails or its consequent holds. |
| `IffSemantics` | A biconditional holds exactly when its two sides agree. |
| `ConstantFormula` | Each truth value is the value, under every evaluation, of a closed valid quantifier-free formula built on a valid atom with no free variable. |
| `AtomLocalDef` | An atomic interpretation depends only on the declared variable support. |
| `EvalSimulation` | A simulation between two interpretations — a relation between their environments for each formula that agrees on valid atoms, passes to the parts of a negation or a conjunction, and matches witnesses both ways at an existential — gives every well-formed formula one value at related environments. |
| `EvalCongruence` | Environments agreeing on free variables give the same truth value. |

## Legal environments

An environment is legal on a support when it assigns a carrier element to every name of the support.

| Member | Statement |
|---|---|
| `EnvOKUnion` | An environment is legal on a union of supports exactly when it is legal on each part. |
| `EnvOKSubset` | An environment legal on a support is legal on every part of it. |
| `EnvOKUpdate` | An environment legal on a support away from one name, updated at that name by a carrier element, is legal on the whole support. |
| `EnvOKEmpty` | Every environment is legal on the empty support. |

## Blocks of names and finite conjunctions

A block of consecutive names quantified at once quantifies a tuple of carrier elements, and a finite conjunction with a true seed means bounded universal truth.

| Member | Statement |
|---|---|
| `AllRangeDef` | Universally quantify a consecutive block of distinct names. |
| `ExistsRangeDef` | Existentially quantify a consecutive block of distinct names. |
| `UpdateRangeDef` | Simultaneously update a consecutive variable block from a tuple. |
| `UpdateRangeEmpty` | A block of length zero leaves the environment unchanged. |
| `UpdateRangeLast` | A block of length n + 1 is the update of its last name to the tuple's entry there, followed by the block of length n. |
| `UpdateRangeExtend` | An update at the name after a block, followed by the block, is the one longer block from the tuple extended by the new value. |
| `UpdateRangeEnvironment` | Substituting carrier values at a block keeps an environment carrier-valued. |
| `UpdateRangeOutside` | A range update leaves every name outside its block alone. |
| `UpdateRangeCopy` | Substituting into a block the values another environment holds there makes the update read that environment on the block. |
| `UpdateRangeCommute` | Range updates at disjoint blocks commute. |
| `AllRangeSemantics` | A universal name block quantifies a finite tuple simultaneously. |
| `ExistsRangeSemantics` | An existential name block quantifies a finite tuple simultaneously. |
| `AllRangeFreeVars` | Universally quantifying a block of consecutive names leaves free exactly the body's free variables outside the block. |
| `ExistsRangeFreeVars` | Existentially quantifying a block of consecutive names leaves free exactly the body's free variables outside the block. |
| `AllRangeSupportBelow` | A universal block at s leaves names below s when its body's lie below the block's end. |
| `ExistsRangeSupportBelow` | An existential block at s leaves names below s when its body's lie below the block's end. |
| `AllRangeWellFormed` | A universally quantified block is well formed exactly when its body is. |
| `ExistsRangeWellFormed` | An existentially quantified block is well formed exactly when its body is. |
| `ConjoinDef` | Finite conjunction with an explicit formula for the empty conjunction. |
| `ConjoinSemantics` | A finite conjunction with a true seed means bounded universal truth. |
| `ConjoinFreeVars` | The free variables of a finite conjunction are those of its seed and of its conjuncts. |
| `ConjoinSupportBelow` | A finite conjunction's names lie below k when its base's and its conjuncts' do. |
| `ConjoinWellFormed` | A finite conjunction is well formed exactly when its seed and each conjunct are. |

## Quantifier elimination and transfer

The contracts take the model class, its carriers, the interpretation, the atomic validity and the support as parameters, and a quantifier-free equivalent is one formula serving every model of the class. Quantifier elimination over [algebraically closed](../../algebra/field/algebraically_closed_quantifier_elimination/README.md) and [real closed](../../algebra/field/real_closed_quantifier_elimination/README.md) fields cites QuantifierEliminationFromOne. The formula chapters' EliminationAlongInjection members, [ring](../../algebra/field/ring_formula/README.md) and [ordered-ring](../../algebra/field/ordered_ring_formula/README.md), cite EliminationAlongClassEmbedding, and the two fields' transfer chapters, [algebraically closed](../../algebra/field/algebraically_closed_field_transfer/README.md) and [real closed](../../algebra/field/real_closed_field_transfer/README.md), are built on those members and on the rest.

| Member | Statement |
|---|---|
| `QuantifierFreeEquivalent` | ψ is a quantifier-free equivalent of φ over a class of models: one formula agreeing with φ in every model of the class. It is a structure of four parts, each an axiom below, and a proof reads the part it needs off the fact. |
| `EquivalentWellFormed` | A quantifier-free equivalent is well formed. |
| `EquivalentQuantifierFree` | A quantifier-free equivalent has no quantifier. |
| `EquivalentSupport` | The free variables of a quantifier-free equivalent are among those of the formula. |
| `EquivalentAgreement` | A quantifier-free equivalent takes the formula's value in every model of the class at every environment legal on the formula's free variables. |
| `OneVariableEliminationDef` | One existential over a quantifier-free body has a quantifier-free equivalent over the class. |
| `QuantifierEliminationDef` | Every well-formed formula has a quantifier-free equivalent over the class. |
| `QuantifierEliminationFromOne` | Uniform one-variable elimination implies uniform full quantifier elimination. |
| `AtomicEmbeddingDef` | A carrier map preserves and reflects valid atoms in every legal environment. |
| `QuantifierFreeEmbedding` | Atomic preservation and reflection extend to quantifier-free formulas. |
| `QuantifierFreeAtomAgreement` | Interpretations agreeing on the valid atoms agree on every valid quantifier-free formula. |
| `OntoEmbedding` | An atomic embedding onto the target carrier preserves and reflects every well-formed formula. |
| `EliminationAlongEmbedding` | An equivalent that serves a model serves every model embedded onto it. |
| `EliminationAlongClassEmbedding` | A quantifier-free equivalent of a well-formed formula over the second of two classes of models is one over the first, when every model of the first embeds atomically onto a model of the second. |
| `ElementaryFromCommonEquivalent` | A quantifier-free equivalent common to two classes makes every atomic embedding between their models elementary. |
| `SentenceTransferFromCommonEquivalent` | A quantifier-free equivalent common to two classes lifts agreement on closed quantifier-free formulas to all sentences. |
