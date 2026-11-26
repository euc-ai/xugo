package milnor_sequence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	"github.com/euc-ai/xugo/library/registry"
)

var ZeroCocycleTowerDef = zeroCocycleTowerDefThm{family.Define(registry.DefEntry{
	Name:  "ZeroCocycleTowerDef",
	Key:   "prop_cd3e883796363843",
	Const: "zero_cocycle_tower",
	Type:  "(num → complex_ops(A, B)) → num → module_ops(A, B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀k:num. " +
			"    zero_cocycle_tower(Q, k) = " +
			"    mk_module(Q(k).add, Q(k).zero, Q(k).neg, Q(k).smul, cocycles(Q(k), 0))",
	},
	Deps: []registry.EntryLike{},
	Reading: "Degree-zero cocycles with their actual additive and " +
		"scalar operations. There are no incoming boundaries in degree zero."})}

var MilnorZeroConnectingDef = milnorZeroConnectingDefThm{family.Define(registry.DefEntry{
	Name:  "MilnorZeroConnectingDef",
	Key:   "prop_5e29466b0f08cdbe",
	Const: "milnor_zero_connecting",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → set(num → B) → set(num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). " +
			"    milnor_zero_connecting(Q, g) = " +
			"    induced_map(λa:(num → B). " +
			"            coconnecting_hom(limit_complex(Q, g), " +
			"                product_complex(Q), " +
			"                λn:num. λs:(num → B). s, " +
			"                product_shift(Q, g), " +
			"                0)(left_coset(product_complex(Q).add, a, coboundaries(product_complex(Q), 0))))",
	},
	Deps: []registry.EntryLike{LimitComplexDef, ProductComplexDef, ProductShiftDef},
	Reading: "The Milnor connecting map on the lim-one presentation of the " +
		"zero-cocycle tower; well-definedness and injectivity are theorem conclusions."})}

var milnorPhantomRepresentativesDef = milnorPhantomRepresentativesDefThm{family.Define(registry.DefEntry{
	Name:  "milnorPhantomRepresentativesDef",
	Key:   "prop_bc7e8aca2a6c4e7a",
	Const: "milnor_phantom_representatives",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → set(num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). " +
			"    milnor_phantom_representatives(Q, g) = " +
			"    {z:(num → B) | z ∈ cocycles(limit_complex(Q, g), 1) ∧ (∀k:num. z(k) ∈ coboundaries(Q(k), 1))}",
	},
	Deps:    []registry.EntryLike{LimitComplexDef},
	Reading: "Compatible degree-one cocycles that are boundaries at every stage."})}

var ZeroCocyclePolishTower = zeroCocyclePolishTowerThm{family.Add(registry.ProofEntry{
	Name: "ZeroCocyclePolishTower",
	Key:  "prop_832b055d769e40db",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀Q:(num → complex_ops(A, B)). " +
				"∀g:(num → num → B → B). " +
				"∀T:(num → num → set(set(B))).",
			Hypotheses: []string{"polish_complex_tower(R, Q, g, T)"},
			Conclusion: "polish_tower(R, " +
				"    zero_cocycle_tower(Q), " +
				"    λk:num. g(k, 0), " +
				"    λk:num. cocycle_topology(Q(k), T(k), 0))",
		},
		"Zero cocycles are closed kernels in every stage "+
			"and the transition maps preserve them continuously."),
	Deps: []registry.EntryLike{
		ZeroCocycleTowerDef,
		PolishComplexTowerDef,
		polish_group.ClosedSubgroupPolish,
	},
	Reading: "Zero cocycles are closed kernels in every " +
		"stage and the transition maps preserve them continuously.",
})}

var PolishMilnorPhantom = polishMilnorPhantomThm{family.Add(registry.ProofEntry{
	Name: "PolishMilnorPhantom",
	Key:  "prop_efa02ef721491944",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀Q:(num → complex_ops(A, B)). " +
				"∀g:(num → num → B → B). " +
				"∀T:(num → num → set(set(B))).",
			Hypotheses: []string{"polish_complex_tower(R, Q, g, T)", "complex_tower_onto(Q, g)"},
			Conclusion: "borel_cover_map( " +
				"    cocycle_group(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), 1), " +
				"    cocycle_topology(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), " +
				"        polish_tower_topologies(zero_cocycle_tower(Q), " +
				"            λk:num. cocycle_topology(Q(k), T(k), 0)), " +
				"        1), " +
				"    coboundaries(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), 1), " +
				"    cocycle_group(limit_complex(Q, g), 1), " +
				"    cocycle_topology(limit_complex(Q, g), polish_limit_topologies(Q, g, T), 1), " +
				"    coboundaries(limit_complex(Q, g), 1), " +
				"    milnor_zero_connecting(Q, g)) ∧ " +
				"injective_on(cohomology(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), 1), " +
				"    milnor_zero_connecting(Q, g)) ∧ " +
				"image(milnor_zero_connecting(Q, g), " +
				"    cohomology(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), 1)) = " +
				"image( " +
				"    λz:(num → B). left_coset(limit_complex(Q, g).add, z, coboundaries(limit_complex(Q, g), 1)), " +
				"    milnor_phantom_representatives(Q, g))",
		},
		"MilnorDerivedLimitKernel identifies exactly the shift denominator in the "+
			"product of zero cocycles. Long exactness identifies the image with locally "+
			"exact cocycles. PolishMilnorConnectingDefinable supplies the Borel lift."),
	Deps: []registry.EntryLike{
		ZeroCocyclePolishTower,
		MilnorZeroConnectingDef,
		milnorPhantomRepresentativesDef,
		MilnorDerivedLimitKernel,
		PolishMilnorConnectingDefinable,
		derived_limit.PolishTowerModel,
	},
	Reading: "MilnorDerivedLimitKernel identifies exactly the shift denominator in " +
		"the product of zero cocycles. Long exactness identifies the image with locally " +
		"exact cocycles. PolishMilnorConnectingDefinable supplies the Borel lift.",
})}

var PolishMilnorPhantomInverse = polishMilnorPhantomInverseThm{family.Add(registry.ProofEntry{
	Name: "PolishMilnorPhantomInverse",
	Key:  "prop_207773b3b3339799",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀Q:(num → complex_ops(A, B)). " +
				"∀g:(num → num → B → B). " +
				"∀T:(num → num → set(set(B))).",
			Hypotheses: []string{"polish_complex_tower(R, Q, g, T)", "complex_tower_onto(Q, g)"},
			Conclusion: "milnor_phantom_representatives(Q, g) ∈ " +
				"borel_sets(cocycle_topology(limit_complex(Q, g), polish_limit_topologies(Q, g, T), 1)) ∧ " +
				"(∃s:((num → B) → num → B). " +
				"    borel_map(subtopology( " +
				"            cocycle_topology(limit_complex(Q, g), polish_limit_topologies(Q, g, T), 1), " +
				"            milnor_phantom_representatives(Q, g)), " +
				"        cocycle_topology(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), " +
				"            polish_tower_topologies(zero_cocycle_tower(Q), " +
				"                λk:num. cocycle_topology(Q(k), T(k), 0)), " +
				"            1), " +
				"        s) ∧ " +
				"    (∀z:(num → B). " +
				"        z ∈ milnor_phantom_representatives(Q, g) ⇒ " +
				"        milnor_zero_connecting(Q, g)(left_coset( " +
				"                tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)).add, " +
				"                s(z), " +
				"                coboundaries(tower_complex(zero_cocycle_tower(Q), λk:num. g(k, 0)), 1))) = " +
				"        left_coset(limit_complex(Q, g).add, z, coboundaries(limit_complex(Q, g), 1))))",
		},
		"Each stage boundary image is Borel and Polishable. Choose Borel preimages a_k of "+
			"the local boundaries z_k; id-minus-shift of a is a sequence of zero cocycles. Its "+
			"connecting class is z, so it gives the inverse lift on phantom representatives."),
	Deps: []registry.EntryLike{
		PolishMilnorPhantom,
		polish_group.ContinuousHomImagePolishable,
		polish_group.ContinuousSurjectionBorelSection,
	},
	Reading: "The phantom representative set need not be closed or Polish in its " +
		"subspace topology. Its Polish cover is transported from the zero-cocycle " +
		"tower, with both directions of the representative comparison stated.",
})}
