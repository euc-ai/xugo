package derived_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/borel_subgroup"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var PolishTowerDef = polishTowerDefThm{family.Define(registry.DefEntry{
	Name:  "PolishTowerDef",
	Key:   "prop_6a6f1b50e5c5e5a7",
	Const: "polish_tower",
	Type:  "ring_ops(A) → (num → module_ops(A, B)) → (num → B → B) → (num → set(set(B))) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B). ∀T:(num → set(set(B))). " +
			"    polish_tower(R, M, f, T) ⇔ " +
			"    tower(R, M, f) ∧ " +
			"    (∀k:num. " +
			"        polish_abelian_group(module_additive_group(M(k)), T(k)) ∧ " +
			"        continuous_map(T(k + 1), T(k), f(k)))",
	},
	Deps: []registry.EntryLike{TowerDef},
	Reading: "A tower of modules whose additive groups " +
		"are Polish and whose transitions are continuous."})}

var PolishTowerTopologiesDef = polishTowerTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "PolishTowerTopologiesDef",
	Key:   "prop_82244ffb1712b8e",
	Const: "polish_tower_topologies",
	Type:  "(num → module_ops(A, B)) → (num → set(set(B))) → num → set(set(num → B))",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀T:(num → set(set(B))). ∀n:num. " +
			"    polish_tower_topologies(M, T, n) = " +
			"    indexed_product_topology(COND(n ≤ 1, 𝕌, ∅), tower_zero(M), T)",
	},
	Deps: []registry.EntryLike{towerZeroDef},
	Reading: "The two nonzero tower degrees use the supplied " +
		"Polish factors; later degrees have only the zero sequence."})}

var PolishTowerModel = polishTowerModelThm{family.Add(registry.ProofEntry{
	Name: "PolishTowerModel",
	Key:  "prop_929f390c61863443",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M:(num → module_ops(A, B)). " +
				"∀f:(num → B → B). " +
				"∀T:(num → set(set(B))).",
			Hypotheses: []string{"polish_tower(R, M, f, T)"},
			Conclusion: "polish_cochain_complex(R, tower_complex(M, f), polish_tower_topologies(M, T)) ∧ " +
				"cohomology_cover(tower_complex(M, f), polish_tower_topologies(M, T), 1)",
		},
		"Products are Polish; id minus shift reads two "+
			"coordinates continuously. Apply CohomologyHasPolishCover."),
	Deps: []registry.EntryLike{
		PolishTowerDef,
		PolishTowerTopologiesDef,
		TowerComplexCochain,
		polish_group.ProductGroupPolish,
		polish_cohomology.CohomologyHasPolishCover,
	},
	Reading: "Products are Polish; id minus shift reads two " +
		"coordinates continuously. Apply CohomologyHasPolishCover.",
})}

var PolishInverseLimitClosed = polishInverseLimitClosedThm{family.Add(registry.ProofEntry{
	Name: "PolishInverseLimitClosed",
	Key:  "prop_533c22437c49b650",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M:(num → module_ops(A, B)). " +
				"∀f:(num → B → B). " +
				"∀T:(num → set(set(B))).",
			Hypotheses: []string{"polish_tower(R, M, f, T)"},
			Conclusion: "closed_in(polish_tower_topologies(M, T, 0), inverse_limit(M, f)) ∧ " +
				"polish_abelian_group( " +
				"    restrict_group(module_additive_group(sequence_module(M)), inverse_limit(M, f)), " +
				"    subtopology(polish_tower_topologies(M, T, 0), inverse_limit(M, f)))",
		},
		"The inverse limit is the closed kernel of the continuous id-minus-shift homomorphism."),
	Deps: []registry.EntryLike{
		PolishTowerModel,
		InverseLimitCocycles,
		polish_group.ClosedSubgroupPolish,
	},
	Reading: "The inverse limit is the closed kernel of the continuous id-minus-shift homomorphism.",
})}

var PolishDerivedLimitZeroOrContinuum = polishDerivedLimitZeroOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "PolishDerivedLimitZeroOrContinuum",
	Key:  "prop_8e0c0295428ac739",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀M:(num → module_ops(A, B)). " +
				"∀f:(num → B → B). " +
				"∀T:(num → set(set(B))).",
			Hypotheses: []string{"polish_tower(R, M, f, T)"},
			Conclusion: "image(tower_shift(M, f), tower_terms(M, 0)) = tower_terms(M, 1) ∨ " +
				"card_le(𝕌⟨A:set(num)⟩, derived_limit(M, f))",
		},
		"FiniteSupportInShiftImage and ProductFiniteSupportDense make the boundary subgroup dense. A "+
			"proper dense Polishable subgroup is not closed, so NonclosedBorelSubgroupContinuumIndex applies."),
	Deps: []registry.EntryLike{
		PolishTowerModel,
		FiniteSupportInShiftImage,
		product_topology.ProductFiniteSupportDense,
		borel_subgroup.NonclosedBorelSubgroupContinuumIndex,
	},
	Reading: "FiniteSupportInShiftImage and ProductFiniteSupportDense " +
		"make the boundary subgroup dense. A proper dense Polishable subgroup " +
		"is not closed, so NonclosedBorelSubgroupContinuumIndex applies.",
})}
