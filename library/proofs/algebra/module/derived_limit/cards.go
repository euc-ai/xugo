package derived_limit

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/sets/num_segment"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// TowerComplexCochain — The two-term complex of a tower is a cochain complex.
var TowerComplexCochain = towerComplexCochainThm{family.Add(registry.ProofEntry{
	Name: "TowerComplexCochain",
	Key:  "prop_517fe964a1f656d0",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
		},
		Conclusion: "cochain_complex(R, tower_complex(M, f))",
	},
		"Each degree is a module: the sequence module on the active carriers in degrees "+
			"zero and one, the zero module above. id − shift is a homomorphism because each "+
			"f(k) is one, and it lands in the sequences; the later differentials are the zero "+
			"maps. Both composites of consecutive differentials vanish since the second is zero."),
	Deps: []registry.EntryLike{chain_complex.CochainComplex},
	Reading: "The zero sequence lies in every carrier, so the degrees above one are " +
		"the zero module. The ring is read only through module_on and the homomorphism laws.",
})}

// InverseLimitCocycles — The 0-cocycles of the tower complex are the compatible sequences.
var InverseLimitCocycles = inverseLimitCocyclesThm{family.Add(registry.ProofEntry{
	Name: "InverseLimitCocycles",
	Key:  "prop_e4093b7ca5eadeaa",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
		},
		Conclusion: "cocycles(tower_complex(M, f), 0) = inverse_limit(M, f)",
	},
		"A 0-cochain s has differential zero exactly when s(k) − f(k)(s(k+1)) is "+
			"the zero of M(k) at every k, which in a group is s(k) = f(k)(s(k+1))."),
	Deps: []registry.EntryLike{chain_complex.CocyclesDef},
	Reading: "Both sides are subsets of the degree-zero " +
		"carrier, the sequences with every coordinate in its module.",
})}

// TowerOneCocycles — Every 1-cochain is a cocycle and the 1-coboundaries are the image of id − shift.
var TowerOneCocycles = towerOneCocyclesThm{family.Add(registry.ProofEntry{
	Name: "TowerOneCocycles",
	Key:  "prop_ab9ec2e25eeee2b9",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
		},
		Conclusion: "cocycles(tower_complex(M, f), 1) = tower_terms(M, 1) ∧ " +
			"coboundaries(tower_complex(M, f), 1) = image(tower_shift(M, f), tower_terms(M, 0))",
	},
		"The differential out of degree one is the zero map, and "+
			"the one into it is id − shift on the degree-zero sequences."),
	Deps: []registry.EntryLike{chain_complex.CocyclesDef, chain_complex.CoboundariesDef},
	Reading: "So derived_limit(M, f) is left_cosets of the image of id − " +
		"shift in the sequences: the cokernel of id − shift, as a set of cosets.",
})}

// CountableTowerPolishModel — A tower of countable modules gives a Polish cochain model.
var CountableTowerPolishModel = countableTowerPolishModelThm{family.Add(registry.ProofEntry{
	Name: "CountableTowerPolishModel",
	Key:  "prop_f5f19adaa41f9977",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
			"∀k:num. countable(M(k).carrier)",
		},
		Conclusion: "polish_cochain_complex(R, tower_complex(M, f), tower_topologies(M))",
	},
		"TowerComplexCochain gives the complex. Each degree is a countable product of countable "+
			"discrete groups with pointwise operations, a Polish abelian group by "+
			"DiscreteProductGroupPolish; above degree one the index set is empty and the product is "+
			"the one-point group. id − shift reads the coordinates k and k+1 at output k and the "+
			"zero differentials are constant, so FiniteCoordinateContinuous gives their continuity."),
	Deps: []registry.EntryLike{
		TowerComplexCochain,
		polish_group.DiscreteProductGroupPolish,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Countability is of the coordinate carriers; the host type and the ring may be larger. " +
		"The scalar action is not asked to be continuous, as PolishCochainComplexDef does not read it.",
})}

// DerivedLimitHasPolishCover — lim¹ of a tower of countable modules has a Polish cover.
var DerivedLimitHasPolishCover = derivedLimitHasPolishCoverThm{family.Add(registry.ProofEntry{
	Name: "DerivedLimitHasPolishCover",
	Key:  "prop_5d5926baa40d0d26",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
			"∀k:num. countable(M(k).carrier)",
		},
		Conclusion: "cohomology_cover(tower_complex(M, f), tower_topologies(M), 1)",
	},
		"CohomologyHasPolishCover in degree one of the Polish model. By TowerOneCocycles the "+
			"covering group is the whole sequence group and the denominator the image of id − shift."),
	Deps: []registry.EntryLike{
		CountableTowerPolishModel,
		TowerOneCocycles,
		polish_cohomology.CohomologyHasPolishCover,
	},
	Reading: "The denominator is the actual image of id − shift, Polishable " +
		"but in general not closed; the cover retains it, not its closure.",
})}

// FiniteSupportInShiftImage — A finitely supported sequence is in the image of id − shift.
var FiniteSupportInShiftImage = finiteSupportInShiftImageThm{family.Add(registry.ProofEntry{
	Name: "FiniteSupportInShiftImage",
	Key:  "prop_c6b434b07d49ff61",
	Deps: []registry.EntryLike{
		num_segment.FiniteIffBounded,
		module_homomorphism.HomZero,
		module_homomorphism.HomIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B). ∀s:(num → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
			"s ∈ tower_terms(M, 1)",
			"finite({k:num | ¬(s(k) = M(k).zero)})",
		},
		Conclusion: "s ∈ image(tower_shift(M, f), tower_terms(M, 0))",
	},
		"Let m bound the support (FiniteIffBounded). Set a(k) = 0 above m and descend, "+
			"a(k) = s(k) + f(k)(a(k+1)), each a(k) in M(k) by HomIn; then a(k) − f(k)(a(k+1)) "+
			"= s(k) at every k, each f(k) carrying zero to zero above the support (HomZero)."),
	Reading: "The preimage is chosen by a downward recursion from the top " +
		"of the support, so it needs no surjectivity of the transition maps.",
})}

// TowerOntoShiftOnto — For a tower of surjections, id − shift is onto the sequences.
var TowerOntoShiftOnto = towerOntoShiftOntoThm{family.Add(registry.ProofEntry{
	Name: "TowerOntoShiftOnto",
	Key:  "prop_fadecdc164a5c070",
	Deps: []registry.EntryLike{module_homomorphism.HomIn},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
			"tower_onto(M, f)",
		},
		Conclusion: "image(tower_shift(M, f), tower_terms(M, 0)) = tower_terms(M, 1)",
	},
		"Solve a(k) − f(k)(a(k+1)) = s(k) upward: a(0) is the zero of M(0), and a(k+1) is any preimage "+
			"under the surjection f(k) of a(k) − s(k), chosen by ε. The image lies in the sequences "+
			"coordinatewise: a(k) − f(k)(a(k+1)) is in M(k), f(k) carrying M(k+1) into M(k) by HomIn."),
	Reading: "So the derived limit of a tower of surjections is the one class of the " +
		"zero sequence. The choice of preimages is a choice, made once per coordinate upward.",
})}

// DerivedLimitZeroOrContinuum — Gray: lim¹ of a tower of countable modules is zero or has at least continuum many elements.
var DerivedLimitZeroOrContinuum = derivedLimitZeroOrContinuumThm{family.Add(registry.ProofEntry{
	Name: "DerivedLimitZeroOrContinuum",
	Key:  "prop_ee67650169b8d3ef",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B).",
		Hypotheses: []string{
			"tower(R, M, f)",
			"∀k:num. countable(M(k).carrier)",
		},
		Conclusion: "image(tower_shift(M, f), tower_terms(M, 0)) = tower_terms(M, 1) ∨ " +
			"card_le(𝕌⟨A:set(num)⟩, derived_limit(M, f))",
	},
		"The image of id − shift contains the finitely supported sequences by "+
			"FiniteSupportInShiftImage, and those are dense in the sequence group by FiniteSupportDense. "+
			"If the derived limit is countable, CountableCohomologyClosedCoboundaries makes the image "+
			"closed in the cocycles, which are all the sequences by TowerOneCocycles, so the image is "+
			"everything; otherwise CohomologyCountableOrContinuum gives the continuum."),
	Deps: []registry.EntryLike{
		FiniteSupportInShiftImage,
		TowerOneCocycles,
		CountableTowerPolishModel,
		polish_space.FiniteSupportDense,
		polish_cohomology.CountableCohomologyClosedCoboundaries,
		polish_cohomology.CohomologyCountableOrContinuum,
	},
	Reading: "Gray's theorem, with the continuum in place of uncountable. " +
		"The first alternative says id − shift is onto, which is lim¹ = 0 as " +
		"a statement about sets; the two alternatives exclude each other.",
})}
