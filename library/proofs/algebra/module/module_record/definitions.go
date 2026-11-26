// definitions.go — the chapter's definitional layer: the two record
// types a module's structure is held in.
//
// A structure's components are one value: `ring_ops(A)` holds a ring's
// six operations and its carrier, `module_ops(A, B)` a module's own
// four and its carrier. Each is a record — a datatype with one
// constructor, its parts read off by projections — so that a statement
// binds `∀R:ring_ops(A)` and reads a component as a field of the value,
// `R.zero`, `M.carrier`, and an operation by its symbol, `c + d`,
// `c • u`. The record door mints the type, the constructor and the
// projections, and registers each projection's equation at the
// constructor (`ring_add(mk_ring(a, …, g)) = a`, under the projection's
// name), the record's extensionality, injectivity, induction and
// recursion.

package module_record

import (
	"github.com/euc-ai/xugo/library/proofs/cartesian/pairs"
	"github.com/euc-ai/xugo/library/proofs/datatypes/datatype_universe"
	// set_product mints set_cross, the carrier ProductModuleDef spells:
	// the import initializes that mint before the equation is read.
	_ "github.com/euc-ai/xugo/library/proofs/sets/set_product"
	"github.com/euc-ai/xugo/library/registry"
	"github.com/euc-ai/xugo/prover/proof"
)

// recordRows are the recursive-type universe's rows a record's
// derivations read, and the pair rows its multi-part payload needs.
var recordRows = []registry.EntryLike{
	datatype_universe.Recursion,
	datatype_universe.FamilyCons,
	datatype_universe.NodeInjective,
	pairs.PairEq,
	pairs.Fst,
	pairs.Snd,
}

// RingOpsData — the record `ring_ops(A)`: `mk_ring(add, zero, neg, mul,
// one, sub, c)` packs a ring's operations and the set it is on; the
// constructions over it are restrict_ring, additive_group and
// regular_module. Under
// a binder R of the type, `R.add` is `ring_add(R)` and `c + d` at
// members of A is `ring_add(R)(c, d)`; likewise `-`, `*` and the binary
// `-`.
var RingOpsData = family.DefineData(registry.DataEntry{
	Name:   "RingOps",
	Type:   "ring_ops",
	Params: []string{"A"},
	Constructors: []proof.DataConstructorSpec{
		{
			Name: "mk_ring",
			Args: []string{"A → A → A", "A", "A → A", "A → A → A", "A", "A → A → A", "set(A)"},
		},
	},
	Fields: []registry.DataField{
		{Name: "RingAddDef", Const: "ring_add", Field: "add", Symbol: "+"},
		{Name: "RingZeroDef", Const: "ring_zero", Field: "zero"},
		{Name: "RingNegDef", Const: "ring_neg", Field: "neg", Symbol: "-"},
		{Name: "RingMulDef", Const: "ring_mul", Field: "mul", Symbol: "*"},
		{Name: "RingOneDef", Const: "ring_one", Field: "one"},
		{Name: "RingSubDef", Const: "ring_sub", Field: "sub", Symbol: "-"},
		{Name: "RingCarrierDef", Const: "ring_carrier", Field: "carrier"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "RingOpsInduction",
		Recursion:      "RingOpsRecursion",
		Injective:      "MkRingInjective",
		Extensionality: "RingOpsEq",
	},
	Deps: recordRows,
})

// ModuleOpsData — the record `module_ops(A, B)`: `mk_module(add, zero,
// neg, smul, c)` packs a module's vector addition, zero, negation, its
// scaling by A and the set of vectors. Under a binder M of the type,
// `u + v` at vectors is `mod_add(M)(u, v)` and `c • u` is
// `mod_smul(M)(c, u)`.
var ModuleOpsData = family.DefineData(registry.DataEntry{
	Name:   "ModuleOps",
	Type:   "module_ops",
	Params: []string{"A", "B"},
	Constructors: []proof.DataConstructorSpec{
		{Name: "mk_module", Args: []string{"B → B → B", "B", "B → B", "A → B → B", "set(B)"}},
	},
	Fields: []registry.DataField{
		{Name: "ModAddDef", Const: "mod_add", Field: "add", Symbol: "+"},
		{Name: "ModZeroDef", Const: "mod_zero", Field: "zero"},
		{Name: "ModNegDef", Const: "mod_neg", Field: "neg", Symbol: "-"},
		{Name: "ModSmulDef", Const: "mod_smul", Field: "smul", Symbol: "•"},
		{Name: "ModCarrierDef", Const: "mod_carrier", Field: "carrier"},
	},
	Principles: registry.DataPrinciples{
		Induction:      "ModuleOpsInduction",
		Recursion:      "ModuleOpsRecursion",
		Injective:      "MkModuleInjective",
		Extensionality: "ModuleOpsEq",
	},
	Deps: recordRows,
})

// RestrictModuleDef — keep a module's operations and replace its carrier.
var RestrictModuleDef = restrictModuleDefThm{family.Define(registry.DefEntry{
	Name: "RestrictModuleDef", Const: "restrict_module",
	Key:  "prop_dd10751a6bf8a4f8",
	Type: "module_ops(A, B) → set(B) → module_ops(A, B)",
	Equations: []string{
		"∀M:module_ops(A, B). ∀S:set(B). " +
			"    restrict_module(M, S) = mk_module(M.add, M.zero, M.neg, M.smul, S)",
	},
	Deps: []registry.EntryLike{ModAddDef, ModZeroDef, ModNegDef, ModSmulDef, ModCarrierDef},
})}

// ScalarRestrictionDef — restriction of scalars along f: a module over the
// scalars of type C, read over the scalars of type A, each scalar r acting
// as f(r) does. The addition, the zero, the negation and the carrier stay.
// A ring S read as a module over R along f is
// `scalar_restriction(f, regular_module(S))`.
var ScalarRestrictionDef = scalarRestrictionDefThm{family.Define(registry.DefEntry{
	Name:  "ScalarRestrictionDef",
	Key:   "prop_329b2baedb1702dd",
	Const: "scalar_restriction",
	Type:  "(A → C) → module_ops(C, B) → module_ops(A, B)",
	Equations: []string{"∀f:(A → C). ∀M:module_ops(C, B). " +
		"    scalar_restriction(f, M) = " +
		"    mk_module(M.add, M.zero, M.neg, λr:A. λx:B. M.smul(f(r), x), M.carrier)"},
	Deps: []registry.EntryLike{ModAddDef, ModZeroDef, ModNegDef, ModSmulDef, ModCarrierDef},
})}

// ProductModuleDef — `product_module(M, N)`: the product M ⊕ N — the pairs
// of M's carrier and N's, added, negated and scaled componentwise.
var ProductModuleDef = productModuleDefThm{family.Define(registry.DefEntry{
	Name:  "ProductModuleDef",
	Key:   "prop_d470b0e57620e959",
	Const: "product_module",
	Type:  "module_ops(A, B) → module_ops(A, C) → module_ops(A, prod(B, C))",
	Equations: []string{
		"∀M:module_ops(A, B). ∀N:module_ops(A, C). " +
			"    product_module(M, N) = " +
			"    mk_module(λz:prod(B, C). λw:prod(B, C). (M.add(fst(z), fst(w)), N.add(snd(z), snd(w))), " +
			"        (M.zero, N.zero), " +
			"        λz:prod(B, C). (M.neg(fst(z)), N.neg(snd(z))), " +
			"        λc:A. λz:prod(B, C). (M.smul(c, fst(z)), N.smul(c, snd(z))), " +
			"        set_cross(M.carrier, N.carrier))",
	},
	Reading: "It is a module over R when M and N are; u ↦ (u, 0), n ↦ " +
		"(0, n) and z ↦ fst(z) are homomorphisms. The operations are written " +
		"through fst and snd, so they reduce at a pair by β and the pair laws.",
	Deps: []registry.EntryLike{ModAddDef, ModZeroDef, ModNegDef, ModSmulDef, ModCarrierDef},
})}

// RestrictRingDef — keep a ring's operations and replace its carrier: a
// subring, or a subfield acting as scalars, as a ring record of its own.
var RestrictRingDef = restrictRingDefThm{family.Define(registry.DefEntry{
	Name: "RestrictRingDef", Const: "restrict_ring",
	Key:  "prop_7fff8bd02f3d8e56",
	Type: "ring_ops(A) → set(A) → ring_ops(A)",
	Equations: []string{
		"∀R:ring_ops(A). ∀S:set(A). " +
			"    restrict_ring(R, S) = mk_ring(R.add, R.zero, R.neg, R.mul, R.one, R.sub, S)",
	},
	Deps: []registry.EntryLike{
		RingAddDef,
		RingZeroDef,
		RingNegDef,
		RingMulDef,
		RingOneDef,
		RingSubDef,
		RingCarrierDef,
	},
})}

// RegularModuleDef — a ring as a module over itself: its addition, zero
// and negation, scaled by its product, on its carrier.
var RegularModuleDef = regularModuleDefThm{family.Define(registry.DefEntry{
	Name: "RegularModuleDef", Const: "regular_module",
	Key:  "prop_78c6d2401add4ba9",
	Type: "ring_ops(A) → module_ops(A, A)",
	Equations: []string{
		"∀R:ring_ops(A). regular_module(R) = mk_module(R.add, R.zero, R.neg, R.mul, R.carrier)",
	},
	Deps: []registry.EntryLike{RingAddDef, RingZeroDef, RingNegDef, RingMulDef, RingCarrierDef},
})}
