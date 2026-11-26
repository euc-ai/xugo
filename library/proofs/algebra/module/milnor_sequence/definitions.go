package milnor_sequence

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// ComplexTowerDef — A descending sequence of cochain complexes on one host type with cochain maps from each to the one below.
var ComplexTowerDef = complexTowerDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexTowerDef",
	Key:   "prop_f192dde58cfeb08d",
	Const: "complex_tower",
	Type:  "ring_ops(A) → (num → complex_ops(A, B)) → (num → num → B → B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). " +
			"    complex_tower(R, Q, g) ⇔ " +
			"    (∀k:num. cochain_complex(R, Q(k))) ∧ (∀k:num. cochain_map(R, Q(k + 1), Q(k), g(k)))",
	},
	Reading: "g(k) is the cochain map from the (k+1)-st " +
		"complex to the k-th, g(k)(n) its degree-n component.",
})}

// ComplexTowerOntoDef — Every transition map is onto in every degree.
var ComplexTowerOntoDef = complexTowerOntoDefThm{family.Define(registry.DefEntry{
	Name:  "ComplexTowerOntoDef",
	Key:   "prop_e4056e43fc2b38ed",
	Const: "complex_tower_onto",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → bool",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). " +
			"    complex_tower_onto(Q, g) ⇔ ∀k n:num. image(g(k)(n), Q(k + 1).terms(n)) = Q(k).terms(n)",
	},
	Reading: "Degreewise surjectivity, the hypothesis under which " +
		"the limit, the product and id − shift form a short exact sequence.",
})}

// complexZeroSequenceDef — The sequence of the coordinate zeroes of the complexes.
var complexZeroSequenceDef = complexZeroSequenceDefThm{family.Define(registry.DefEntry{
	Name:  "complexZeroSequenceDef",
	Key:   "prop_7e6c22b2129b0264",
	Const: "complex_zero_sequence",
	Type:  "(num → complex_ops(A, B)) → num → B",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀k:num. complex_zero_sequence(Q, k) = Q(k).zero",
	},
	Reading: "The zero of the product complex in every degree.",
})}

// productTermsDef — The sequences with the k-th coordinate in the degree-n term of the k-th complex.
var productTermsDef = productTermsDefThm{family.Define(registry.DefEntry{
	Name:  "productTermsDef",
	Key:   "prop_69de95c5dc7ec8b2",
	Const: "product_terms",
	Type:  "(num → complex_ops(A, B)) → num → set(num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀n:num. " +
			"    product_terms(Q, n) = indexed_functions(𝕌, complex_zero_sequence(Q), λk:num. Q(k).terms(n))",
	},
	Deps: []registry.EntryLike{complexZeroSequenceDef},
	Reading: "Every coordinate is active; the prescribed " +
		"value is never used but fixes the normalized product.",
})}

// ProductComplexDef — The product of the sequence of complexes, with pointwise operations and differential.
var ProductComplexDef = productComplexDefThm{family.Define(registry.DefEntry{
	Name:  "ProductComplexDef",
	Key:   "prop_4c9f2b12335b7bb0",
	Const: "product_complex",
	Type:  "(num → complex_ops(A, B)) → complex_ops(A, num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). " +
			"    product_complex(Q) = " +
			"    pack_complex(λs:(num → B). λt:(num → B). λk:num. Q(k).add(s(k), t(k)), " +
			"        complex_zero_sequence(Q), " +
			"        λs:(num → B). λk:num. Q(k).neg(s(k)), " +
			"        λa:A. λs:(num → B). λk:num. Q(k).smul(a, s(k)), " +
			"        product_terms(Q), " +
			"        λn:num. λs:(num → B). λk:num. Q(k).d(n)(s(k)))",
	},
	Deps: []registry.EntryLike{complexZeroSequenceDef, productTermsDef},
	Reading: "Its degree-n module is the sequence module of the degree-n modules " +
		"of the complexes; its cocycles and coboundaries are the products of the " +
		"coordinate cocycles and coboundaries, since the differential acts coordinatewise.",
})}

// ProductShiftDef — id − shift on the product complex, read at one degree and coordinate.
var ProductShiftDef = productShiftDefThm{family.Define(registry.DefEntry{
	Name:  "ProductShiftDef",
	Key:   "prop_62740db30f526574",
	Const: "product_shift",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → num → (num → B) → num → B",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num. ∀s:(num → B). ∀k:num. " +
			"    product_shift(Q, g, n, s, k) = Q(k).add(s(k), Q(k).neg(g(k)(n)(s(k + 1))))",
	},
	Reading: "In each degree the tower shift of the tower of degree-n " +
		"modules; it is a cochain map of the product complex to itself.",
})}

// limitTermsDef — The compatible sequences in degree n.
var limitTermsDef = limitTermsDefThm{family.Define(registry.DefEntry{
	Name:  "limitTermsDef",
	Key:   "prop_b9e1789d96421d3c",
	Const: "limit_terms",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → num → set(num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num. " +
			"    limit_terms(Q, g, n) = " +
			"    {s:num → B | s ∈ product_terms(Q, n) ∧ (∀k:num. s(k) = g(k)(n)(s(k + 1)))}",
	},
	Deps: []registry.EntryLike{productTermsDef},
	Reading: "The kernel of id − shift in degree n: " +
		"the inverse limit of the tower of degree-n modules.",
})}

// LimitComplexDef — The limit complex: the compatible sequences with the operations and differential of the product.
var LimitComplexDef = limitComplexDefThm{family.Define(registry.DefEntry{
	Name:  "LimitComplexDef",
	Key:   "prop_7d4603abbcb71872",
	Const: "limit_complex",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → complex_ops(A, num → B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). " +
			"    limit_complex(Q, g) = " +
			"    pack_complex(product_complex(Q).add, " +
			"        product_complex(Q).zero, " +
			"        product_complex(Q).neg, " +
			"        product_complex(Q).smul, " +
			"        limit_terms(Q, g), " +
			"        product_complex(Q).d)",
	},
	Deps: []registry.EntryLike{limitTermsDef, ProductComplexDef},
	Reading: "A subcomplex of the product: the differential preserves compatibility because " +
		"the transition maps are cochain maps. Its inclusion is the identity in every degree.",
})}

// productTopologiesDef — The product of the discrete degree-n terms of the complexes.
var productTopologiesDef = productTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "productTopologiesDef",
	Key:   "prop_582ed8558482b8c4",
	Const: "product_topologies",
	Type:  "(num → complex_ops(A, B)) → num → set(set(num → B))",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀n:num. " +
			"    product_topologies(Q, n) = " +
			"    indexed_discrete_topology(𝕌, complex_zero_sequence(Q), λk:num. Q(k).terms(n))",
	},
	Deps:    []registry.EntryLike{complexZeroSequenceDef},
	Reading: "Its carrier is product_terms(Q, n).",
})}

// limitTopologiesDef — The subspace topology of the compatible sequences.
var limitTopologiesDef = limitTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "limitTopologiesDef",
	Key:   "prop_7c354d96f1575198",
	Const: "limit_topologies",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → num → set(set(num → B))",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num. " +
			"    limit_topologies(Q, g, n) = subtopology(product_topologies(Q, n), limit_terms(Q, g, n))",
	},
	Deps: []registry.EntryLike{limitTermsDef, productTopologiesDef},
	Reading: "Its carrier is limit_terms(Q, g, n), a " +
		"closed set of the product when the terms are discrete.",
})}

// CohomologyTowerDef — The tower of degree-n cohomology modules of the complexes.
var CohomologyTowerDef = cohomologyTowerDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyTowerDef",
	Key:   "prop_955946a3f653c386",
	Const: "cohomology_tower",
	Type:  "(num → complex_ops(A, B)) → num → num → module_ops(A, set(B))",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀n:num. ∀k:num. " +
			"    cohomology_tower(Q, n, k) = cohomology_module(Q(k), n)",
	},
	Reading: "A tower on the host type set(B), the " +
		"classes; its transition maps are cohomology_tower_maps.",
})}

// CohomologyTowerMapsDef — The maps on degree-n cohomology induced by the transition maps.
var CohomologyTowerMapsDef = cohomologyTowerMapsDefThm{family.Define(registry.DefEntry{
	Name:  "CohomologyTowerMapsDef",
	Key:   "prop_5e476f574f8fe7d5",
	Const: "cohomology_tower_maps",
	Type:  "(num → complex_ops(A, B)) → (num → num → B → B) → num → num → set(B) → set(B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀g:(num → num → B → B). ∀n:num. ∀k:num. " +
			"    cohomology_tower_maps(Q, g, n, k) = cohomology_map(Q(k), g(k), n)",
	},
	Reading: "cohomology_map(Q(k), g(k), n) carries the classes of Q(k+1) to " +
		"those of Q(k), the target complex named first as CohomologyMapDef reads it.",
})}

// ProductClassMapDef — A class of the product complex read as the sequence of its coordinate classes.
var ProductClassMapDef = productClassMapDefThm{family.Define(registry.DefEntry{
	Name:  "ProductClassMapDef",
	Key:   "prop_6c3570053d95b3ed",
	Const: "product_class_map",
	Type:  "(num → complex_ops(A, B)) → num → set(num → B) → num → set(B)",
	Equations: []string{
		"∀Q:(num → complex_ops(A, B)). ∀n:num. ∀c:set(num → B). " +
			"    product_class_map(Q, n, c) = " +
			"    induced_map(λs:(num → B). λk:num. left_coset(Q(k).add, s(k), coboundaries(Q(k), n)), c)",
	},
	Reading: "Evaluated on a representative of the class; well defined on classes because " +
		"the coboundaries of the product are the products of the coordinate coboundaries.",
})}
