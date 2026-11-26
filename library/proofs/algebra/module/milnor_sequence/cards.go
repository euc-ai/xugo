package milnor_sequence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/polish_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/derived_limit"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ProductComplexCochain — The product of cochain complexes is a cochain complex.
var ProductComplexCochain = productComplexCochainThm{family.Add(registry.ProofEntry{
	Name: "ProductComplexCochain",
	Key:  "prop_46e76fba8560c4ab",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)).",
		Hypotheses: []string{
			"∀k:num. cochain_complex(R, Q(k))",
		},
		Conclusion: "cochain_complex(R, product_complex(Q))",
	},
		"Every law of a cochain complex is read coordinatewise: the degree-n "+
			"module is the sequence module of the degree-n modules, the "+
			"differential is a homomorphism and squares to zero at every coordinate."),
	Deps:    []registry.EntryLike{chain_complex.CochainComplex, derived_limit.SequenceModuleDef},
	Reading: "No transition maps enter; the hypothesis is only that each complex is one.",
})}

// LimitComplexCochain — The limit complex is a cochain complex.
var LimitComplexCochain = limitComplexCochainThm{family.Add(registry.ProofEntry{
	Name: "LimitComplexCochain",
	Key:  "prop_7ecbb6f0709997d0",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
		},
		Conclusion: "cochain_complex(R, limit_complex(Q, g))",
	},
		"The compatible sequences form a submodule in each degree because the transition components "+
			"are homomorphisms, and the differential preserves compatibility because they are cochain "+
			"maps: g(k)(n+1) of the (k+1)-st differential is the k-th differential of g(k)(n)."),
	Deps: []registry.EntryLike{ProductComplexCochain, chain_complex.CochainComplex},
	Reading: "The operations are the product's, so the laws " +
		"hold on the subcomplex once it is closed under them.",
})}

// LimitInclusionCochainMap — The inclusion of the limit complex into the product is a cochain map.
var LimitInclusionCochainMap = limitInclusionCochainMapThm{family.Add(registry.ProofEntry{
	Name: "LimitInclusionCochainMap",
	Key:  "prop_57ba8871fd034d1d",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
		},
		Conclusion: "cochain_map(R, limit_complex(Q, g), product_complex(Q), λj:num. λs:(num → B). s)",
	},
		"The identity in every degree is a homomorphism of the restricted module "+
			"into the product module and commutes with the shared differential."),
	Deps:    []registry.EntryLike{LimitComplexCochain, ProductComplexCochain},
	Reading: "The inclusion is spelled as the identity map in every degree; no constant names it.",
})}

// ProductShiftCochainMap — id − shift is a cochain map of the product complex to itself.
var ProductShiftCochainMap = productShiftCochainMapThm{family.Add(registry.ProofEntry{
	Name: "ProductShiftCochainMap",
	Key:  "prop_a9db4eb669ba02f7",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
		},
		Conclusion: "cochain_map(R, product_complex(Q), product_complex(Q), product_shift(Q, g))",
	},
		"At each coordinate s(k) − g(k)(n)(s(k+1)) is linear in s, and the "+
			"differential commutes with it since each g(k) is a cochain map."),
	Deps:    []registry.EntryLike{ProductComplexCochain},
	Reading: "In degree n this is derived_limit's tower_shift of the tower of degree-n modules.",
})}

// ComplexTowerShortExact — For a tower of surjections, the limit, the product and id − shift form a short exact sequence of complexes.
var ComplexTowerShortExact = complexTowerShortExactThm{family.Add(registry.ProofEntry{
	Name: "ComplexTowerShortExact",
	Key:  "prop_d40df85be7bc7395",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"complex_tower_onto(Q, g)",
		},
		Conclusion: "short_exact_cochain_complexes(R, " +
			"    limit_complex(Q, g), " +
			"    product_complex(Q), " +
			"    product_complex(Q), " +
			"    λj:num. λs:(num → B). s, " +
			"    product_shift(Q, g))",
	},
		"Degreewise: the inclusion is injective, its image is the kernel of id − shift by the "+
			"definition of the compatible sequences, and id − shift is onto by TowerOntoShiftOnto "+
			"applied to the tower of degree-n modules, surjective by complex_tower_onto."),
	Deps: []registry.EntryLike{
		LimitInclusionCochainMap,
		ProductShiftCochainMap,
		derived_limit.TowerOntoShiftOnto,
		chain_complex.ShortExactCochainComplexes,
	},
	Reading: "Surjectivity of the transition maps is what makes " +
		"id − shift onto; without it the sequence is only left exact.",
})}

// ProductCohomologyClasses — The cohomology of the product is the product of the cohomologies.
var ProductCohomologyClasses = productCohomologyClassesThm{family.Add(registry.ProofEntry{
	Name: "ProductCohomologyClasses",
	Key:  "prop_6dadee7c546a49b9",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀n:num.",
		Hypotheses: []string{
			"∀k:num. cochain_complex(R, Q(k))",
		},
		Conclusion: "module_isomorphism(R, " +
			"    cohomology_module(product_complex(Q), n), " +
			"    sequence_module(cohomology_tower(Q, n)), " +
			"    product_class_map(Q, n))",
	},
		"The cocycles and coboundaries of the product are the products of the coordinate "+
			"cocycles and coboundaries, the differential acting coordinatewise. So the class of a "+
			"sequence is determined by the sequence of coordinate classes and determines it: the "+
			"map is well defined, injective, and onto the sequences of classes, a representative "+
			"being chosen in each coordinate; it is linear since the operations are coordinatewise."),
	Deps: []registry.EntryLike{
		ProductComplexCochain,
		chain_complex.CohomologyMapCoset,
		derived_limit.SequenceModuleDef,
	},
	Reading: "The target carrier is every sequence of classes, with no compatibility: this is " +
		"the product, not the limit. The isomorphism needs no transition maps, and the sequence " +
		"module of the cohomology modules is a module by a coordinatewise argument, not by a tower.",
})}

// ProductShiftCohomology — Under the class map, id − shift on the cohomology of the product is id − shift on the product of cohomologies.
var ProductShiftCohomology = productShiftCohomologyThm{family.Add(registry.ProofEntry{
	Name: "ProductShiftCohomology",
	Key:  "prop_be93de9e777dfa6a",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:(num → complex_ops(A, B)). " +
			"∀g:(num → num → B → B). " +
			"∀n:num. " +
			"∀c:set(num → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"c ∈ cohomology(product_complex(Q), n)",
		},
		Conclusion: "product_class_map(Q, " +
			"    n, " +
			"    cohomology_map(product_complex(Q), product_shift(Q, g), n, c)) = " +
			"tower_shift(cohomology_tower(Q, n), cohomology_tower_maps(Q, g, n), product_class_map(Q, n, c))",
	},
		"Both sides read s(k) − g(k)(n)(s(k+1)) on a representative s of c and pass to the class "+
			"coordinatewise; CohomologyMapCoset and the quotient operations identify the two readings."),
	Deps: []registry.EntryLike{
		ProductCohomologyClasses,
		ProductShiftCochainMap,
		chain_complex.CohomologyMapCoset,
	},
	Reading: "The right side is derived_limit's tower_shift for the tower " +
		"of cohomology modules, whose operations are the quotient module's.",
})}

// MilnorLimitImage — The image of the limit cohomology in the product cohomology is the inverse limit of the cohomology tower.
var MilnorLimitImage = milnorLimitImageThm{family.Add(registry.ProofEntry{
	Name: "MilnorLimitImage",
	Key:  "prop_d0b9d9b5cc7e34d5",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num.",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"complex_tower_onto(Q, g)",
		},
		Conclusion: "image(product_class_map(Q, n), " +
			"    image(cohomology_map(product_complex(Q), λj:num. λs:(num → B). s, n), " +
			"        cohomology(limit_complex(Q, g), n))) = " +
			"inverse_limit(cohomology_tower(Q, n), cohomology_tower_maps(Q, g, n))",
	},
		"By CoLongExactMiddle at the short exact sequence of ComplexTowerShortExact, the image of "+
			"the inclusion on cohomology is the kernel of id − shift on cohomology. Under the bijective "+
			"class map, ProductShiftCohomology turns that kernel into the kernel of tower_shift on the "+
			"sequences of classes, which is the inverse limit of the cohomology tower."),
	Deps: []registry.EntryLike{
		ComplexTowerShortExact,
		ProductCohomologyClasses,
		ProductShiftCohomology,
		chain_complex.CoLongExactMiddle,
	},
	Reading: "This is the right end of Milnor's sequence: H^n of the limit maps onto lim H^n " +
		"of the tower. Surjectivity of the transition maps enters through the short exact sequence.",
})}

// MilnorDerivedLimitKernel — The connecting map kills a product class exactly when its class sequence lies in the image of id − shift.
var MilnorDerivedLimitKernel = milnorDerivedLimitKernelThm{family.Add(registry.ProofEntry{
	Name: "MilnorDerivedLimitKernel",
	Key:  "prop_cc2ad6b5aff0b1de",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀Q:(num → complex_ops(A, B)). " +
			"∀g:(num → num → B → B). " +
			"∀n:num. " +
			"∀c:set(num → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"complex_tower_onto(Q, g)",
			"c ∈ cohomology(product_complex(Q), n)",
		},
		Conclusion: "coconnecting_hom(limit_complex(Q, g), " +
			"    product_complex(Q), " +
			"    λj:num. λs:(num → B). s, " +
			"    product_shift(Q, g), " +
			"    n, " +
			"    c) = " +
			"coboundaries(limit_complex(Q, g), n + 1) ⇔ " +
			"product_class_map(Q, n, c) ∈ " +
			"image(tower_shift(cohomology_tower(Q, n), cohomology_tower_maps(Q, g, n)), " +
			"    tower_terms(cohomology_tower(Q, n), 0))",
	},
		"By CoLongExactQuotient the kernel of the connecting map is the image of id − "+
			"shift on the cohomology of the product; the zero class of H^(n+1) of the limit "+
			"is its coboundaries. ProductShiftCohomology and the surjectivity of the class "+
			"map carry that image to the image of tower_shift on the sequences of classes."),
	Deps: []registry.EntryLike{
		ComplexTowerShortExact,
		ProductCohomologyClasses,
		ProductShiftCohomology,
		chain_complex.CoLongExactQuotient,
	},
	Reading: "This is the left end of Milnor's sequence: the connecting map " +
		"induces an injection of lim¹ H^n of the tower into H^(n+1) of the limit, " +
		"whose image CoLongExactSub identifies with the kernel of the inclusion. The " +
		"zero class is spelled as the coboundaries, the coset of the zero sequence.",
})}

// CountableComplexTowerPolishModel — A tower of complexes with countable terms gives Polish product and limit models with continuous inclusion and shift.
var CountableComplexTowerPolishModel = countableComplexTowerPolishModelThm{family.Add(registry.ProofEntry{
	Name: "CountableComplexTowerPolishModel",
	Key:  "prop_f00f2f8a1754daac",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B).",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"∀k n:num. countable(Q(k).terms(n))",
		},
		Conclusion: "polish_cochain_complex(R, product_complex(Q), product_topologies(Q)) ∧ " +
			"polish_cochain_complex(R, limit_complex(Q, g), limit_topologies(Q, g)) ∧ " +
			"polish_cochain_map(R, " +
			"    limit_complex(Q, g), " +
			"    limit_topologies(Q, g), " +
			"    product_complex(Q), " +
			"    product_topologies(Q), " +
			"    λj:num. λs:(num → B). s) ∧ " +
			"polish_cochain_map(R, " +
			"    product_complex(Q), " +
			"    product_topologies(Q), " +
			"    product_complex(Q), " +
			"    product_topologies(Q), " +
			"    product_shift(Q, g))",
	},
		"DiscreteProductGroupPolish gives each product degree; the compatible sequences are "+
			"closed, each compatibility equation being a continuous finite-coordinate condition "+
			"into a discrete space, so ClosedSubgroupPolish gives each limit degree. The "+
			"differential, the inclusion and id − shift read one or two coordinates at each output, "+
			"so FiniteCoordinateContinuous gives their continuity, into the subspace where needed."),
	Deps: []registry.EntryLike{
		LimitComplexCochain,
		LimitInclusionCochainMap,
		ProductShiftCochainMap,
		polish_group.DiscreteProductGroupPolish,
		polish_group.ClosedSubgroupPolish,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Countability is of every term of every complex. The limit topologies are " +
		"subspaces of the product topologies, so the inclusion is continuous by the subspace laws.",
})}

// MilnorConnectingDefinable — The connecting map and the inclusion of a countable tower of surjections have Borel lifts.
var MilnorConnectingDefinable = milnorConnectingDefinableThm{family.Add(registry.ProofEntry{
	Name: "MilnorConnectingDefinable",
	Key:  "prop_35804d6638a19bc5",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num.",
		Hypotheses: []string{
			"complex_tower(R, Q, g)",
			"complex_tower_onto(Q, g)",
			"∀k m:num. countable(Q(k).terms(m))",
		},
		Conclusion: "cohomology_borel_map(product_complex(Q), " +
			"    product_topologies(Q), " +
			"    n, " +
			"    limit_complex(Q, g), " +
			"    limit_topologies(Q, g), " +
			"    n + 1, " +
			"    coconnecting_hom(limit_complex(Q, g), " +
			"        product_complex(Q), " +
			"        λj:num. λs:(num → B). s, " +
			"        product_shift(Q, g), " +
			"        n)) ∧ " +
			"cohomology_borel_map(limit_complex(Q, g), " +
			"    limit_topologies(Q, g), " +
			"    n, " +
			"    product_complex(Q), " +
			"    product_topologies(Q), " +
			"    n, " +
			"    cohomology_map(product_complex(Q), λj:num. λs:(num → B). s, n))",
	},
		"ConnectingMapDefinable and CohomologyDefinableFunctor at the short exact sequence of "+
			"Polish models that CountableComplexTowerPolishModel and ComplexTowerShortExact supply."),
	Deps: []registry.EntryLike{
		CountableComplexTowerPolishModel,
		ComplexTowerShortExact,
		polish_cohomology.ConnectingMapDefinable,
		polish_cohomology.CohomologyDefinableFunctor,
	},
	Reading: "So both maps of Milnor's sequence that leave or enter the cohomology of the limit are " +
		"Borel-liftable between the covers of the limit and product complexes. The lim¹ term is read " +
		"through MilnorDerivedLimitKernel; its own cover as a cover of the cohomology tower is not stated.",
})}
