package milnor_sequence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/registry"
)

var PolishComplexTowerDef = polishComplexTowerDefThm{family.Define(registry.DefEntry{
	Name:  "PolishComplexTowerDef",
	Key:   "prop_c5c749e67dca5010",
	Const: "polish_complex_tower",
	Type: "ring_ops(A) → " +
		"(num → complex_ops(A, B)) → " +
		"(num → num → B → B) → " +
		"(num → num → set(set(B))) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀Q:(num → complex_ops(A, B)). " +
			"∀g:(num → num → B → B). " +
			"∀T:(num → num → set(set(B))). " +
			"    polish_complex_tower(R, Q, g, T) ⇔ " +
			"    (∀k:num. " +
			"        polish_cochain_complex(R, Q(k), T(k)) ∧ " +
			"        polish_cochain_map(R, Q(k + 1), T(k + 1), Q(k), T(k), g(k)))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Each stage is a Polish cochain complex " +
		"and each transition is a continuous cochain map."})}

var PolishProductTopologiesDef = polishProductTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "PolishProductTopologiesDef",
	Key:   "prop_2bdfd4d8392f06c7",
	Const: "polish_product_topologies",
	Type:  "(num → complex_ops(A, B)) → (num → num → set(set(B))) → num → set(set(num → B))",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀T:(num → num → set(set(B))). ∀n:num. " +
			"    polish_product_topologies(Q, T, n) = " +
			"    indexed_product_topology(𝕌, complex_zero_sequence(Q), λk:num. T(k, n))",
	},
	Deps:    []registry.EntryLike{complexZeroSequenceDef},
	Reading: "Products use the actual degree topologies, which need not be discrete."})}

var PolishLimitTopologiesDef = polishLimitTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "PolishLimitTopologiesDef",
	Key:   "prop_13d1316d506a3268",
	Const: "polish_limit_topologies",
	Type: "(num → complex_ops(A, B)) → " +
		"(num → num → B → B) → " +
		"(num → num → set(set(B))) → " +
		"num → " +
		"set(set(num → B))",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀T:(num → num → set(set(B))). ∀n:num. " +
			"    polish_limit_topologies(Q, g, T, n) = " +
			"    subtopology(polish_product_topologies(Q, T, n), limit_terms(Q, g, n))",
	},
	Deps:    []registry.EntryLike{limitTermsDef, PolishProductTopologiesDef},
	Reading: "The limit has its closed subspace topology."})}

var PolishComplexTowerModel = polishComplexTowerModelThm{family.Add(registry.ProofEntry{
	Name: "PolishComplexTowerModel",
	Key:  "prop_39eac13dd7579ef7",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀Q:(num → complex_ops(A, B)). " +
				"∀g:(num → num → B → B). " +
				"∀T:(num → num → set(set(B))).",
			Hypotheses: []string{"polish_complex_tower(R, Q, g, T)"},
			Conclusion: "polish_cochain_complex(R, product_complex(Q), polish_product_topologies(Q, T)) ∧ " +
				"polish_cochain_complex(R, limit_complex(Q, g), polish_limit_topologies(Q, g, T)) ∧ " +
				"polish_cochain_map(R, " +
				"    limit_complex(Q, g), " +
				"    polish_limit_topologies(Q, g, T), " +
				"    product_complex(Q), " +
				"    polish_product_topologies(Q, T), " +
				"    λn:num. λs:(num → B). s) ∧ " +
				"polish_cochain_map(R, " +
				"    product_complex(Q), " +
				"    polish_product_topologies(Q, T), " +
				"    product_complex(Q), " +
				"    polish_product_topologies(Q, T), " +
				"    product_shift(Q, g))",
		},
		"Apply ProductGroupPolish degreewise. Shift and differential are continuous "+
			"coordinatewise, and the limit is the closed kernel of the shift."),
	Deps: []registry.EntryLike{
		PolishComplexTowerDef,
		PolishLimitTopologiesDef,
		ProductComplexCochain,
		LimitComplexCochain,
		polish_group.ProductGroupPolish,
		polish_group.ClosedSubgroupPolish,
	},
	Reading: "Apply ProductGroupPolish degreewise. Shift and differential are " +
		"continuous coordinatewise, and the limit is the closed kernel of the shift.",
})}

var PolishMilnorConnectingDefinable = polishMilnorConnectingDefinableThm{family.Add(registry.ProofEntry{
	Name: "PolishMilnorConnectingDefinable",
	Key:  "prop_3e6c7661fe19ca1c",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀Q:(num → complex_ops(A, B)). " +
				"∀g:(num → num → B → B). " +
				"∀T:(num → num → set(set(B))). " +
				"∀n:num.",
			Hypotheses: []string{"polish_complex_tower(R, Q, g, T)", "complex_tower_onto(Q, g)"},
			Conclusion: "cohomology_borel_map(product_complex(Q), " +
				"    polish_product_topologies(Q, T), " +
				"    n, " +
				"    limit_complex(Q, g), " +
				"    polish_limit_topologies(Q, g, T), " +
				"    n + 1, " +
				"    coconnecting_hom(limit_complex(Q, g), " +
				"        product_complex(Q), " +
				"        λj:num. λs:(num → B). s, " +
				"        product_shift(Q, g), " +
				"        n)) ∧ " +
				"cohomology_borel_map(limit_complex(Q, g), " +
				"    polish_limit_topologies(Q, g, T), " +
				"    n, " +
				"    product_complex(Q), " +
				"    polish_product_topologies(Q, T), " +
				"    n, " +
				"    cohomology_map(product_complex(Q), λj:num. λs:(num → B). s, n))",
		},
		"Apply ConnectingMapDefinable to the degreewise short exact Polish sequence. MilnorLimitImage "+
			"and MilnorDerivedLimitKernel identify its exact sequence with the algebraic Milnor sequence."),
	Deps: []registry.EntryLike{
		PolishComplexTowerModel,
		ComplexTowerShortExact,
		MilnorLimitImage,
		MilnorDerivedLimitKernel,
		polish_cohomology.ConnectingMapDefinable,
		polish_cohomology.CohomologyDefinableFunctor,
	},
	Reading: "The cohomology tower need not consist of Polish groups. Its derived-limit term is " +
		"presented by the product-complex connecting map, not by an unjustified quotient topology.",
})}
