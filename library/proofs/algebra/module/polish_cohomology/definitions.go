package polish_cohomology

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolishCochainComplexDef — Each degree topology is on exactly that degree carrier; scalar multiplication need not be jointly continuous in the scalars.
var PolishCochainComplexDef = polishCochainComplexDefThm{family.Define(registry.DefEntry{
	Name:  "PolishCochainComplexDef",
	Key:   "prop_48597e0d480d5940",
	Const: "polish_cochain_complex",
	Type:  "ring_ops(A) → complex_ops(A, B) → (num → set(set(B))) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). " +
			"    polish_cochain_complex(R, Q, T) ⇔ " +
			"    cochain_complex(R, Q) ∧ " +
			"    (∀n:num. " +
			"        polish_abelian_group(module_additive_group(complex_module(Q, n)), T(n)) ∧ " +
			"        continuous_map(T(n), T(n + 1), Q.d(n)))",
	},
	Reading: "Each degree topology is on exactly that degree carrier; " +
		"scalar multiplication need not be jointly continuous in the scalars.",
})}

// PolishCochainMapDef — A cochain map continuous in every degree.
var PolishCochainMapDef = polishCochainMapDefThm{family.Define(registry.DefEntry{
	Name:  "PolishCochainMapDef",
	Key:   "prop_a54d277e038b9a9e",
	Const: "polish_cochain_map",
	Type: "ring_ops(A) → " +
		"complex_ops(A, B) → " +
		"(num → set(set(B))) → " +
		"complex_ops(A, C) → " +
		"(num → set(set(C))) → " +
		"(num → B → C) → " +
		"bool",
	Equations: []string{
		"∀R:ring_ops(A). " +
			"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀f:(num → B → C). " +
			"    polish_cochain_map(R, Q, T, P, U, f) ⇔ " +
			"    polish_cochain_complex(R, Q, T) ∧ " +
			"    polish_cochain_complex(R, P, U) ∧ " +
			"    cochain_map(R, Q, P, f) ∧ " +
			"    (∀n:num. continuous_map(T(n), U(n), f(n)))",
	},
	Deps:    []registry.EntryLike{PolishCochainComplexDef},
	Reading: "A cochain map continuous in every degree.",
})}

// CocycleGroupDef — The additive group of cocycles, with the ambient complex operations.
var CocycleGroupDef = cocycleGroupDefThm{family.Define(registry.DefEntry{
	Name:  "CocycleGroupDef",
	Key:   "prop_61c06471cb6dd1fb",
	Const: "cocycle_group",
	Type:  "complex_ops(A, B) → num → group_ops(B)",
	Equations: []string{
		"∀Q:complex_ops(A, B). ∀n:num. " +
			"    cocycle_group(Q, n) = " +
			"    restrict_group(module_additive_group(complex_module(Q, n)), cocycles(Q, n))",
	},
	Reading: "The additive group of cocycles, with the ambient complex operations.",
})}

// CocycleTopologyDef — Cocycles carry the subspace topology of the degree term.
var CocycleTopologyDef = cocycleTopologyDefThm{family.Define(registry.DefEntry{
	Name:  "CocycleTopologyDef",
	Key:   "prop_49880a9efecdf0db",
	Const: "cocycle_topology",
	Type:  "complex_ops(A, B) → (num → set(set(B))) → num → set(set(B))",
	Equations: []string{
		"∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num. " +
			"    cocycle_topology(Q, T, n) = subtopology(T(n), cocycles(Q, n))",
	},
	Reading: "Cocycles carry the subspace topology of the degree term.",
})}

// CohomologyCoverDef — The covering group is the cocycle group and the denominator is the actual coboundary subgroup.
var CohomologyCoverDef = cohomologyCoverDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyCoverDef",
	Key:   "prop_8bd4aab74e08b388",
	Const: "cohomology_cover",
	Type:  "complex_ops(A, B) → (num → set(set(B))) → num → bool",
	Equations: []string{
		"∀Q:complex_ops(A, B). ∀T:(num → set(set(B))). ∀n:num. " +
			"    cohomology_cover(Q, T, n) ⇔ " +
			"    polish_cover_on(cocycle_group(Q, n), cocycle_topology(Q, T, n), coboundaries(Q, n))",
	},
	Deps: []registry.EntryLike{CocycleGroupDef, CocycleTopologyDef},
	Reading: "The covering group is the cocycle group " +
		"and the denominator is the actual coboundary subgroup.",
})}

// CohomologyBorelMapDef — A Borel-liftable homomorphism between two cohomology covers, allowing a change of degree.
var CohomologyBorelMapDef = cohomologyBorelMapDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyBorelMapDef",
	Key:   "prop_d093ae95751994c0",
	Const: "cohomology_borel_map",
	Type: "complex_ops(A, B) → " +
		"(num → set(set(B))) → " +
		"num → " +
		"complex_ops(A, C) → " +
		"(num → set(set(C))) → " +
		"num → " +
		"(set(B) → set(C)) → " +
		"bool",
	Equations: []string{
		"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀n:num. " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀m:num. " +
			"∀h:(set(B) → set(C)). " +
			"    cohomology_borel_map(Q, T, n, P, U, m, h) ⇔ " +
			"    borel_cover_map(cocycle_group(Q, n), " +
			"        cocycle_topology(Q, T, n), " +
			"        coboundaries(Q, n), " +
			"        cocycle_group(P, m), " +
			"        cocycle_topology(P, U, m), " +
			"        coboundaries(P, m), " +
			"        h)",
	},
	Deps: []registry.EntryLike{CocycleGroupDef, CocycleTopologyDef},
	Reading: "A Borel-liftable homomorphism between " +
		"two cohomology covers, allowing a change of degree.",
})}

// CohomologyBorelIsoDef — A comparison with Borel lifts in both directions.
var CohomologyBorelIsoDef = cohomologyBorelIsoDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyBorelIsoDef",
	Key:   "prop_99b6df8bcd2125a",
	Const: "cohomology_borel_iso",
	Type: "complex_ops(A, B) → " +
		"(num → set(set(B))) → " +
		"num → " +
		"complex_ops(A, C) → " +
		"(num → set(set(C))) → " +
		"num → " +
		"(set(B) → set(C)) → " +
		"bool",
	Equations: []string{
		"∀Q:complex_ops(A, B). " +
			"∀T:(num → set(set(B))). " +
			"∀n:num. " +
			"∀P:complex_ops(A, C). " +
			"∀U:(num → set(set(C))). " +
			"∀m:num. " +
			"∀h:(set(B) → set(C)). " +
			"    cohomology_borel_iso(Q, T, n, P, U, m, h) ⇔ " +
			"    borel_cover_iso(cocycle_group(Q, n), " +
			"        cocycle_topology(Q, T, n), " +
			"        coboundaries(Q, n), " +
			"        cocycle_group(P, m), " +
			"        cocycle_topology(P, U, m), " +
			"        coboundaries(P, m), " +
			"        h)",
	},
	Deps:    []registry.EntryLike{CocycleGroupDef, CocycleTopologyDef},
	Reading: "A comparison with Borel lifts in both directions.",
})}

// DualPointwiseTopologiesDef — In each degree, the dual is a product of discrete copies of N on its generators.
var DualPointwiseTopologiesDef = dualPointwiseTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "DualPointwiseTopologiesDef",
	Key:   "prop_287a45f481111508",
	Const: "dual_pointwise_topologies",
	Type:  "module_ops(A, C) → (num → set(I)) → num → set(set(I → C))",
	Equations: []string{
		"∀N:module_ops(A, C). ∀S:(num → set(I)). ∀n:num. " +
			"    dual_pointwise_topologies(N, S, n) = " +
			"    indexed_discrete_topology(S(n), λi:I. N.zero, λi:I. N.carrier)",
	},
	Reading: "In each degree, the dual is a product of discrete copies of N on its generators.",
})}
