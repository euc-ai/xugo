// definitions.go — the chapter's definitional layer: ℝ itself, and
// the six constants the axioms are stated in.
//
// A REAL is an equivalence class of pre-reals: the quotient of
// `prod(hreal, hreal)` by `treal_eq`, whose class map `real_of_treal`
// — written ⁅p⁆, the class of the pair p — takes a pre-real to its
// class. The quotient door mints the type over the class shape
// (mk_real / dest_real the bijection underneath) and gives the seven
// facts a quotient comes with; inhabitation is immediate, so the type
// costs the chapter no theorem beyond nonneg_real_formal_diff's TrealEqEquivalence.
//
// Each operation is defined AT CLASSES, by what it does to
// representatives, exactly as the layer below defines the hreals: the
// sum of the classes of x and y is the class of x + y, and the
// respectfulness the lift door asks for is the nonneg_real_formal_diff chapter's
// well-definedness law, cited. The order descends the same way, to a
// truth value. Everything else about ℝ in this corpus is derived from
// the axioms this chapter states over these six names.

package real_construction

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/nonneg_real_formal_diff"
	"github.com/euc-ai/xugo/library/registry"
)

// RealDef — the type ℝ: the treal_eq-classes, made a type, with
// `real_of_treal` the class map (⁅p⁆) and mk_real / dest_real the
// bijection underneath. Its seven facts (RealDef.Surjectivity,
// .Induct, .Sound, .Exact, .Eq, .ForallOnImage, .ExistsOnImage) are
// the chapter's whole bridge.
var RealDef = family.DefineQuotient(registry.QuotientEntry{
	Name:        "Real",
	Type:        "real",
	Mk:          "real_of_treal",
	Abs:         "mk_real",
	Rep:         "dest_real",
	Relation:    "treal_eq",
	Equivalence: nonneg_real_formal_diff.TrealEqEquivalence,
	Deps:        []registry.EntryLike{nonneg_real_formal_diff.TrealEqDef},
})

// RealOfNumDef — a number as a real: the class of its pre-real.
var RealOfNumDef = realOfNumDefThm{family.Define(registry.DefEntry{
	Name:  "RealOfNumDef",
	Key:   "prop_c2c9d6af0da8e8be",
	Const: "real_of_num",
	// The DSL keeps `real_of_num` for its own `&` embedding surface, so
	// the equation spells the definiendum by a stand-in.
	Spelled:   "realOfNum",
	Type:      "num → real",
	Equations: []string{"∀m:num. realOfNum(m) = ⁅treal_of_num(m)⁆"},
	Deps:      []registry.EntryLike{RealDef.Surjectivity},
})}

// RealAddDef — the sum of two classes is the class of the sum of
// representatives; nonneg_real_formal_diff.AddWellDef is the respectfulness.
var RealAddDef = realAddDefThm{family.Define(registry.DefEntry{
	Name:      "RealAddDef",
	Key:       "prop_e0ab4159d857728e",
	Const:     "real_add",
	Type:      "real → real → real",
	Equations: []string{"∀a b:prod(hreal, hreal). real_add(⁅a⁆, ⁅b⁆) = ⁅a + b⁆"},
	Respects:  []Action{Cite(nonneg_real_formal_diff.AddWellDef)},
	Deps: []registry.EntryLike{
		nonneg_real_formal_diff.TrealAddDef,
		nonneg_real_formal_diff.AddWellDef,
	},
})}

// RealMulDef — the product of two classes is the class of the product
// of representatives; nonneg_real_formal_diff.MulWellDef is the respectfulness.
var RealMulDef = realMulDefThm{family.Define(registry.DefEntry{
	Name:      "RealMulDef",
	Key:       "prop_584447356d477681",
	Const:     "real_mul",
	Type:      "real → real → real",
	Equations: []string{"∀a b:prod(hreal, hreal). real_mul(⁅a⁆, ⁅b⁆) = ⁅a * b⁆"},
	Respects:  []Action{Cite(nonneg_real_formal_diff.MulWellDef)},
	Deps: []registry.EntryLike{
		nonneg_real_formal_diff.TrealMulDef,
		nonneg_real_formal_diff.MulWellDef,
	},
})}

// RealNegDef — the negation of a class is the class of the negation
// of a representative; nonneg_real_formal_diff.NegWellDef is the respectfulness.
var RealNegDef = realNegDefThm{family.Define(registry.DefEntry{
	Name:      "RealNegDef",
	Key:       "prop_a7aff7f9b535a7a6",
	Const:     "real_neg",
	Type:      "real → real",
	Equations: []string{"∀a:prod(hreal, hreal). real_neg(⁅a⁆) = ⁅treal_neg(a)⁆"},
	Respects:  []Action{Cite(nonneg_real_formal_diff.NegWellDef)},
	Deps: []registry.EntryLike{
		nonneg_real_formal_diff.TrealNegDef,
		nonneg_real_formal_diff.NegWellDef,
	},
})}

// RealInvDef — the inverse of a class is the class of the inverse of
// a representative; nonneg_real_formal_diff.InvWellDef is the respectfulness.
var RealInvDef = realInvDefThm{family.Define(registry.DefEntry{
	Name:      "RealInvDef",
	Key:       "prop_ae057c83ba9a4aef",
	Const:     "real_inv",
	Type:      "real → real",
	Equations: []string{"∀a:prod(hreal, hreal). real_inv(⁅a⁆) = ⁅treal_inv(a)⁆"},
	Respects:  []Action{Cite(nonneg_real_formal_diff.InvWellDef)},
	Deps: []registry.EntryLike{
		nonneg_real_formal_diff.TrealInvDef,
		nonneg_real_formal_diff.InvWellDef,
	},
})}

// RealLeDef — the order at classes is the order of representatives,
// a truth value the same for any representatives
// (nonneg_real_formal_diff.LessEqWellDef).
var RealLeDef = realLeDefThm{family.Define(registry.DefEntry{
	Name:      "RealLeDef",
	Key:       "prop_e016407c919430e2",
	Const:     "real_le",
	Type:      "real → real → bool",
	Equations: []string{"∀a b:prod(hreal, hreal). real_le(⁅a⁆, ⁅b⁆) ⇔ a ≤ b"},
	Respects:  []Action{Cite(nonneg_real_formal_diff.LessEqWellDef)},
	Deps: []registry.EntryLike{
		nonneg_real_formal_diff.TrealLeDef,
		nonneg_real_formal_diff.LessEqWellDef,
	},
})}
