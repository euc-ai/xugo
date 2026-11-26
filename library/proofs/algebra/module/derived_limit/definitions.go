package derived_limit

import (
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_record"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/comm_ring"
	_ "github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinal"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	_ "github.com/euc-ai/xugo/library/proofs/sets/indexed_functions"
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// TowerDef — A descending sequence of modules on one host type with homomorphisms from each to the one below.
var TowerDef = towerDefThm{family.Define(registry.DefEntry{
	Name:  "TowerDef",
	Key:   "prop_797d85ce733b999d",
	Const: "tower",
	Type:  "ring_ops(A) → (num → module_ops(A, B)) → (num → B → B) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀M:(num → module_ops(A, B)). ∀f:(num → B → B). " +
			"    tower(R, M, f) ⇔ " +
			"    (∀k:num. module_on(R, M(k))) ∧ (∀k:num. module_homomorphism(R, M(k + 1), M(k), f(k)))",
	},
	Reading: "The tower descends: f(k) maps the (k+1)-st module to the k-th. Every module " +
		"lives in the one host type B; a tower of abelian groups is the case of the ring of integers.",
})}

// TowerOntoDef — Every transition map of the tower is onto.
var TowerOntoDef = towerOntoDefThm{family.Define(registry.DefEntry{
	Name:  "TowerOntoDef",
	Key:   "prop_a38a7305a7d2a22c",
	Const: "tower_onto",
	Type:  "(num → module_ops(A, B)) → (num → B → B) → bool",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀f:(num → B → B). " +
			"    tower_onto(M, f) ⇔ ∀k:num. image(f(k), M(k + 1).carrier) = M(k).carrier",
	},
	Reading: "The strongest Mittag-Leffler condition; " +
		"it makes id − shift onto and the derived limit vanish.",
})}

// towerZeroDef — The sequence of the coordinate zeroes.
var towerZeroDef = towerZeroDefThm{family.Define(registry.DefEntry{
	Name:      "towerZeroDef",
	Key:       "prop_14245493ff6dc1ea",
	Const:     "tower_zero",
	Type:      "(num → module_ops(A, B)) → num → B",
	Equations: []string{"∀M:(num → module_ops(A, B)). ∀k:num. tower_zero(M, k) = M(k).zero"},
	Reading: "The zero of the sequence module and the prescribed " +
		"inactive value of every normalized product over the tower.",
})}

// SequenceModuleDef — The product of the sequence of modules, with pointwise operations; every coordinate is active.
var SequenceModuleDef = sequenceModuleDefThm{family.Define(registry.DefEntry{
	Name:  "SequenceModuleDef",
	Key:   "prop_a71ee313fb3bc8b3",
	Const: "sequence_module",
	Type:  "(num → module_ops(A, B)) → module_ops(A, num → B)",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). " +
			"    sequence_module(M) = " +
			"    mk_module(λs:(num → B). λt:(num → B). λk:num. M(k).add(s(k), t(k)), " +
			"        tower_zero(M), " +
			"        λs:(num → B). λk:num. M(k).neg(s(k)), " +
			"        λa:A. λs:(num → B). λk:num. M(k).smul(a, s(k)), " +
			"        indexed_functions(𝕌, tower_zero(M), λk:num. M(k).carrier))",
	},
	Deps: []registry.EntryLike{towerZeroDef},
	Reading: "The carrier is the normalized product on every index, so " +
		"no coordinate is inactive. The transition maps do not enter the module.",
})}

// TowerShiftDef — The map id − shift of a tower, read at one coordinate.
var TowerShiftDef = towerShiftDefThm{family.Define(registry.DefEntry{
	Name:  "TowerShiftDef",
	Key:   "prop_6a42befa467ef0e1",
	Const: "tower_shift",
	Type:  "(num → module_ops(A, B)) → (num → B → B) → (num → B) → num → B",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀f:(num → B → B). ∀s:(num → B). ∀k:num. " +
			"    tower_shift(M, f, s, k) = M(k).add(s(k), M(k).neg(f(k)(s(k + 1))))",
	},
	Reading: "At coordinate k the value is s(k) minus the image of s(k+1) under the " +
		"transition map; its kernel is the inverse limit and its cokernel the derived limit.",
})}

// TowerTermsDef — Degrees zero and one are the sequences; above, only the zero sequence.
var TowerTermsDef = towerTermsDefThm{family.Define(registry.DefEntry{
	Name:  "TowerTermsDef",
	Key:   "prop_64ec6d5b1fe835a5",
	Const: "tower_terms",
	Type:  "(num → module_ops(A, B)) → num → set(num → B)",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀n:num. " +
			"    tower_terms(M, n) = indexed_functions(COND(n ≤ 1, 𝕌, ∅), tower_zero(M), λk:num. M(k).carrier)",
	},
	Deps: []registry.EntryLike{towerZeroDef},
	Reading: "The empty index set leaves only the prescribed function, " +
		"the zero sequence, so the complex is zero above degree one.",
})}

// TowerComplexDef — The two-term cochain complex of a tower: id − shift in degree zero, zero above.
var TowerComplexDef = towerComplexDefThm{family.Define(registry.DefEntry{
	Name:  "TowerComplexDef",
	Key:   "prop_48689a078ab012a5",
	Const: "tower_complex",
	Type:  "(num → module_ops(A, B)) → (num → B → B) → complex_ops(A, num → B)",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀f:(num → B → B). " +
			"    tower_complex(M, f) = " +
			"    pack_complex(sequence_module(M).add, " +
			"        sequence_module(M).zero, " +
			"        sequence_module(M).neg, " +
			"        sequence_module(M).smul, " +
			"        tower_terms(M), " +
			"        λn:num. λs:(num → B). COND(n = 0, tower_shift(M, f, s), tower_zero(M)))",
	},
	Deps: []registry.EntryLike{SequenceModuleDef, TowerShiftDef, TowerTermsDef, towerZeroDef},
	Reading: "The operations are those of the sequence module in every degree; only " +
		"the carriers and the one differential vary. The complex does not read the ring.",
})}

// TowerTopologiesDef — The product of the discrete coordinate modules in degrees zero and one, the one-point topology above.
var TowerTopologiesDef = towerTopologiesDefThm{family.Define(registry.DefEntry{
	Name:  "TowerTopologiesDef",
	Key:   "prop_5b8043e188e4b21c",
	Const: "tower_topologies",
	Type:  "(num → module_ops(A, B)) → num → set(set(num → B))",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀n:num. " +
			"    tower_topologies(M, n) = " +
			"    indexed_discrete_topology(COND(n ≤ 1, 𝕌, ∅), tower_zero(M), λk:num. M(k).carrier)",
	},
	Deps: []registry.EntryLike{towerZeroDef},
	Reading: "Its carrier in each degree is tower_terms(M, n). Above degree one the index " +
		"set is empty and the topology is that of the one-point space on the zero sequence.",
})}

// InverseLimitDef — The compatible sequences, as a set.
var InverseLimitDef = inverseLimitDefThm{family.Define(registry.DefEntry{
	Name:  "InverseLimitDef",
	Key:   "prop_5e301e8ccfeebd50",
	Const: "inverse_limit",
	Type:  "(num → module_ops(A, B)) → (num → B → B) → set(num → B)",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀f:(num → B → B). " +
			"    inverse_limit(M, f) = " +
			"    {s:num → B | " +
			"        s ∈ indexed_functions(𝕌, tower_zero(M), λk:num. M(k).carrier) ∧ " +
			"        (∀k:num. s(k) = f(k)(s(k + 1)))}",
	},
	Deps: []registry.EntryLike{towerZeroDef},
	Reading: "A subset of the sequence carrier, not a module record; restrict_module " +
		"and restrict_group cut the structures on it. It is the kernel of id − shift.",
})}

// DerivedLimitDef — lim¹ as the first cohomology of the two-term complex.
var DerivedLimitDef = derivedLimitDefThm{family.Define(registry.DefEntry{
	Name:  "DerivedLimitDef",
	Key:   "prop_4f3a3e251c5c7397",
	Const: "derived_limit",
	Type:  "(num → module_ops(A, B)) → (num → B → B) → set(set(num → B))",
	Equations: []string{
		"∀M:(num → module_ops(A, B)). ∀f:(num → B → B). " +
			"    derived_limit(M, f) = cohomology(tower_complex(M, f), 1)",
	},
	Deps: []registry.EntryLike{TowerComplexDef},
	Reading: "Every 1-cochain is a cocycle, so this is the set of " +
		"cosets of the image of id − shift in the sequences: the cokernel of " +
		"id − shift. Its Polish cover is the cohomology cover in degree one.",
})}
