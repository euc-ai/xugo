// definitions.go — the chapter's definitional layer: the type of
// slopes and the arithmetic written on it, minted here.
//
// A SLOPE is a function ℕ → ℕ that is additive up to a bounded
// defect: `is_nadd(x)` says some B bounds `nat_dist(m·x(n), n·x(m))` by
// `B·(m + n)` at every m and n. The type `nadd` is the functions of
// that shape, in bijection with them via mk_nadd / dest_nadd, stamped
// against the constantly-zero function (ZeroIsSlope, toolkit.go) —
// the inhabitant a type definition must be shown before it may be
// made.
//
// The operations are all written through the bijection: a slope is
// taken down to its function, the ℕ-arithmetic is done there, and the
// result is brought back up. Equality and order are not the type's
// own — two slopes are EQUAL when their functions stay a bounded
// distance apart, and one is BELOW another when it stays under it up
// to a bound — so the chapter's `nadd_eq` is a relation, not `=`, and
// the layer above quotients by it.

package eudoxus_slope

import (
	"github.com/euc-ai/xugo/library/registry"
)

// IsNaddDef — the defining bound: x is nearly additive when one B
// bounds the defect `nat_dist(m·x(n), n·x(m))` by `B·(m + n)` everywhere.
var IsNaddDef = isNaddDefThm{family.Define(registry.DefEntry{
	Name:  "IsNaddDef",
	Key:   "prop_97475a74660636ce",
	Const: "is_nadd",
	Type:  "(num → num) → bool",
	Equations: []string{
		"∀x:(num → num). is_nadd(x) ⇔ ∃B:num. ∀m n:num. dist((m * x(n), n * x(m))) ≤ B * (m + n)",
	},
})}

// NaddDef — the type of slopes: the nearly-additive functions made a
// type, the bijection the pair mk_nadd / dest_nadd, stamped against
// the constantly-zero function. The two facts it comes with:
//
//   - NaddDef.Retraction: `mk_nadd(dest_nadd(x)) = x` — a slope taken
//     down to its function and brought back up is itself, which is what
//     lets an argument drop to ℕ and return.
//   - NaddDef.Membership: `is_nadd(r) ⇔ dest_nadd(mk_nadd(r)) = r` — a
//     function is nearly additive exactly when it survives the opposite
//     round trip, which is the discharge every operation below owes.
var NaddDef = family.DefineType(registry.TypeEntry{
	Name:      "Nadd",
	Type:      "nadd",
	Abs:       "mk_nadd",
	Rep:       "dest_nadd",
	Pred:      "is_nadd",
	Existence: ZeroIsSlope,
	Witness:   "λn:num. 0",
	Deps:      []registry.EntryLike{IsNaddDef},
})

// NaddEqDef — two slopes are equal when their functions stay a
// bounded distance apart. This is the chapter's equality; `=` on nadd
// is finer than the mathematics wants.
var NaddEqDef = naddEqDefThm{family.Define(registry.DefEntry{
	Name:  "NaddEqDef",
	Key:   "prop_5dc30cb658ae0bdf",
	Const: "nadd_eq",
	Type:  "nadd → nadd → bool",
	Equations: []string{
		"∀x y:nadd. nadd_eq(x, y) ⇔ ∃B:num. ∀n:num. dist((dest_nadd(x, n), dest_nadd(y, n))) ≤ B",
	},
	Deps: []registry.EntryLike{NaddDef.Retraction},
})}

// NaddLeDef — one slope is below another when it stays under it up to
// a bound.
var NaddLeDef = naddLeDefThm{family.Define(registry.DefEntry{
	Name:  "NaddLeDef",
	Key:   "prop_8f6636670bb9e587",
	Const: "nadd_le",
	Type:  "nadd → nadd → bool",
	Equations: []string{
		"∀x y:nadd. nadd_le(x, y) ⇔ ∃B:num. ∀n:num. dest_nadd(x, n) ≤ dest_nadd(y, n) + B",
	},
	Deps: []registry.EntryLike{NaddDef.Retraction},
})}

// NaddOfNumDef — a number as a slope: the ray of that gradient.
var NaddOfNumDef = naddOfNumDefThm{family.Define(registry.DefEntry{
	Name:      "NaddOfNumDef",
	Key:       "prop_88b26190f9a7fedb",
	Const:     "nadd_of_num",
	Type:      "num → nadd",
	Equations: []string{"∀k:num. nadd_of_num(k) = mk_nadd(λn:num. k * n)"},
	Deps:      []registry.EntryLike{NaddDef.Retraction},
})}

// NaddAddDef — slopes add pointwise.
var NaddAddDef = naddAddDefThm{family.Define(registry.DefEntry{
	Name:  "NaddAddDef",
	Key:   "prop_eaf5e28983bb4f7a",
	Const: "nadd_add",
	Type:  "nadd → nadd → nadd",
	Equations: []string{
		"∀x y:nadd. nadd_add(x, y) = mk_nadd(λn:num. dest_nadd(x, n) + dest_nadd(y, n))",
	},
	Deps: []registry.EntryLike{NaddDef.Retraction},
})}

// NaddMulDef — slopes multiply by composition: a gradient of a
// gradient.
var NaddMulDef = naddMulDefThm{family.Define(registry.DefEntry{
	Name:      "NaddMulDef",
	Key:       "prop_626edc7ddaa50455",
	Const:     "nadd_mul",
	Type:      "nadd → nadd → nadd",
	Equations: []string{"∀x y:nadd. nadd_mul(x, y) = mk_nadd(λn:num. dest_nadd(x, dest_nadd(y, n)))"},
	Deps:      []registry.EntryLike{NaddDef.Retraction},
})}

// naddRinvDef — the candidate reciprocal function: n ↦ n²/x(n), whose
// gradient is the reciprocal of x's. It is a bare ℕ → ℕ function, not
// yet a slope: that it IS one is the chapter's work.
var naddRinvDef = naddRinvDefThm{family.Define(registry.DefEntry{
	Name:      "naddRinvDef",
	Key:       "prop_70e0bcf7b2848ac1",
	Const:     "nadd_rinv",
	Type:      "nadd → num → num",
	Equations: []string{"∀x:nadd. ∀n:num. nadd_rinv(x, n) = div(n * n, dest_nadd(x, n))"},
	Deps:      []registry.EntryLike{NaddDef.Retraction},
})}

// NaddInvDef — the reciprocal slope, with zero sent to zero: the
// reciprocal of a null gradient is not a slope, so the definition
// splits on nadd_eq against zero rather than leaving the value
// unspecified.
var NaddInvDef = naddInvDefThm{family.Define(registry.DefEntry{
	Name:  "NaddInvDef",
	Key:   "prop_2c6ea32a6abff09d",
	Const: "nadd_inv",
	Type:  "nadd → nadd",
	Equations: []string{
		"∀x:nadd. nadd_inv(x) = COND(nadd_eq(x, nadd_of_num(0)), nadd_of_num(0), mk_nadd(nadd_rinv(x)))",
	},
	Deps: []registry.EntryLike{NaddEqDef, NaddOfNumDef, naddRinvDef},
})}
