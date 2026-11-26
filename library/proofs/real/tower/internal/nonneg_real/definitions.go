// definitions.go — the chapter's definitional layer: the
// non-negative reals as slopes modulo bounded difference, and the
// arithmetic that descends to them.
//
// An `hreal` is an EQUIVALENCE CLASS of slopes: the quotient of `nadd`
// by `nadd_eq`, whose class map `hreal_of_nadd` — written ⁅x⁆, the
// class of the slope x — takes a slope to its class. The quotient door
// mints the type over the class shape (mk_hreal / dest_hreal the
// bijection underneath) and gives the seven facts a quotient comes
// with; inhabitation is immediate, so the type costs the chapter no
// theorem beyond slope's NaddEqEquivalence.
//
// Each operation is defined AT CLASSES, by what it does to
// representatives: the sum of the classes of x and y is the class of
// x + y. That such a rule defines a function is the respectfulness the
// lift door asks for, and the slope chapter's well-definedness laws
// are exactly that obligation, so each definition cites its law and
// nothing more. The order descends the same way, to a truth value.

package nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/internal/eudoxus_slope"
	"github.com/euc-ai/xugo/library/registry"
)

// HrealDef — the type of non-negative reals: the nadd_eq-classes, made
// a type, with `hreal_of_nadd` the class map (⁅x⁆) and mk_hreal /
// dest_hreal the bijection underneath. Its seven facts
// (HrealDef.Surjectivity, .Induct, .Sound, .Exact, .Eq, .ForallOnImage,
// .ExistsOnImage) are the chapter's whole bridge: a law over hreal
// inducts to representatives, the operations below compute at classes,
// and Eq reads class equality as nadd_eq.
var HrealDef = family.DefineQuotient(registry.QuotientEntry{
	Name:        "Hreal",
	Type:        "hreal",
	Mk:          "hreal_of_nadd",
	Abs:         "mk_hreal",
	Rep:         "dest_hreal",
	Relation:    "nadd_eq",
	Equivalence: eudoxus_slope.NaddEqEquivalence,
	Deps:        []registry.EntryLike{eudoxus_slope.NaddEqDef},
})

// HrealOfNumDef — a number as a non-negative real: the class of the
// ray of that gradient.
var HrealOfNumDef = hrealOfNumDefThm{family.Define(registry.DefEntry{
	Name:      "HrealOfNumDef",
	Key:       "prop_5fe7cd7eab3703ed",
	Const:     "hreal_of_num",
	Type:      "num → hreal",
	Equations: []string{"∀m:num. hreal_of_num(m) = ⁅nadd_of_num(m)⁆"},
	Deps:      []registry.EntryLike{HrealDef.Surjectivity},
})}

// HrealAddDef — the sum of two classes is the class of the sum of
// representatives; eudoxus_slope.AddWellDef is the respectfulness that makes
// it a function.
var HrealAddDef = hrealAddDefThm{family.Define(registry.DefEntry{
	Name:      "HrealAddDef",
	Key:       "prop_aac3e97a58e82af2",
	Const:     "hreal_add",
	Type:      "hreal → hreal → hreal",
	Equations: []string{"∀a b:nadd. hreal_add(⁅a⁆, ⁅b⁆) = ⁅a + b⁆"},
	Respects:  []Action{Cite(eudoxus_slope.AddWellDef)},
	Deps:      []registry.EntryLike{eudoxus_slope.NaddAddDef, eudoxus_slope.AddWellDef},
})}

// HrealMulDef — the product of two classes is the class of the product
// of representatives; eudoxus_slope.MulWellDef is the respectfulness.
var HrealMulDef = hrealMulDefThm{family.Define(registry.DefEntry{
	Name:      "HrealMulDef",
	Key:       "prop_8b3912e97ff54113",
	Const:     "hreal_mul",
	Type:      "hreal → hreal → hreal",
	Equations: []string{"∀a b:nadd. hreal_mul(⁅a⁆, ⁅b⁆) = ⁅a * b⁆"},
	Respects:  []Action{Cite(eudoxus_slope.MulWellDef)},
	Deps:      []registry.EntryLike{eudoxus_slope.NaddMulDef, eudoxus_slope.MulWellDef},
})}

// HrealLeDef — the order at classes is the order of representatives:
// not a class but a truth value, which eudoxus_slope.LessEqWellDef shows is
// the same for any representatives.
var HrealLeDef = hrealLeDefThm{family.Define(registry.DefEntry{
	Name:      "HrealLeDef",
	Key:       "prop_b8105162635cec8d",
	Const:     "hreal_le",
	Type:      "hreal → hreal → bool",
	Equations: []string{"∀a b:nadd. hreal_le(⁅a⁆, ⁅b⁆) ⇔ a ≤ b"},
	Respects:  []Action{Cite(eudoxus_slope.LessEqWellDef)},
	Deps:      []registry.EntryLike{eudoxus_slope.NaddLeDef, eudoxus_slope.LessEqWellDef},
})}

// HrealInvDef — the reciprocal of a class is the class of the
// reciprocal of a representative; eudoxus_slope.InvWellDef is the
// respectfulness.
var HrealInvDef = hrealInvDefThm{family.Define(registry.DefEntry{
	Name:      "HrealInvDef",
	Key:       "prop_a5b79063a0b4980",
	Const:     "hreal_inv",
	Type:      "hreal → hreal",
	Equations: []string{"∀a:nadd. hreal_inv(⁅a⁆) = ⁅nadd_inv(a)⁆"},
	Respects:  []Action{Cite(eudoxus_slope.InvWellDef)},
	Deps:      []registry.EntryLike{eudoxus_slope.NaddInvDef, eudoxus_slope.InvWellDef},
})}
