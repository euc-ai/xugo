// definitions.go — the chapter's definitional layer: the type ⟦0, ∞⟧
// and its embedding of the reals, order, addition and multiplication.
//
// An extended nonnegative real is an optional real: absent for ∞, and
// present for a finite value, which is then nonnegative. The type is
// carved out of option(real) by that one condition. Only ∞ and the
// embedding of the reals read the representation; every other
// operation is defined on the type through those two and the finite
// value `extended_to_real`, by cases on whether an argument is ∞, so the
// chapter's laws are argued from a handful of facts about the embedding
// and never open the representation again.

package extended_nonneg_real

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/datatypes/option"
	"github.com/euc-ai/xugo/library/registry"
)

// ExtendedNonnegRealInhabited — some optional real is absent or
// nonnegative: none is, being no some at all.
var ExtendedNonnegRealInhabited = extendedNonnegRealInhabitedThm{family.Add(registry.ProofEntry{
	Name: "ExtendedNonnegRealInhabited",
	Key:  "prop_9122c3016ef5c97d",
	Build: family.Theorem("∃o:option(real). ∀r:real. o = some(r) ⇒ &0 ≤ r",
		func(a *Argument) {
			a.Take(a.TermAs[option.Option[Real]]("none"))
			a.Show(
				"none is no some(r), so it carries no negative value",
				By(option.NoneNotSome))
		}),
})}

// ExtendedNonnegRealDef — the type ⟦0, ∞⟧: the optional reals whose
// value, when present, is nonnegative, with extended_of_option /
// option_of_extended the bijection.
var ExtendedNonnegRealDef = family.DefineType(registry.TypeEntry{
	Name:      "ExtendedNonnegReal",
	Type:      "extended_nonneg_real",
	Abs:       "extended_of_option",
	Rep:       "option_of_extended",
	Pred:      "λo:option(real). ∀r:real. o = some(r) ⇒ &0 ≤ r",
	Existence: ExtendedNonnegRealInhabited,
})

// The type's two facts, as typed citation surfaces: an extended value is
// the image of its own representative, and an optional real is the
// representative of its image exactly when its value, if any, is
// nonnegative.
var (
	ExtendedNonnegRealRetraction = extendedNonnegRealRetractionThm{ExtendedNonnegRealDef.Retraction}
	ExtendedNonnegRealMembership = extendedNonnegRealMembershipThm{ExtendedNonnegRealDef.Membership}
)

// ExtendedInfinityDef — ∞ is the absent value.
var ExtendedInfinityDef = extendedInfinityDefThm{family.Define(registry.DefEntry{
	Name:      "ExtendedInfinityDef",
	Key:       "prop_f20610b184042ad4",
	Const:     "extended_infinity",
	Type:      "extended_nonneg_real",
	Equations: []string{"extended_infinity = extended_of_option(none)"},
	Deps:      []registry.EntryLike{ExtendedNonnegRealDef.Retraction},
})}

// ExtendedOfRealDef — a real seen in ⟦0, ∞⟧, clamped at zero: a
// nonnegative real is itself, and every negative real is 0, so the
// embedding is total and monotone. At a numeral it is written `&n`
// (`&0`, `&1`); applied to a real, which may be negative, it keeps its
// name.
var ExtendedOfRealDef = extendedOfRealDefThm{family.Define(registry.DefEntry{
	Name:            "ExtendedOfRealDef",
	Key:             "prop_6b3010de0c00b843",
	Const:           "extended_of_real",
	Type:            "real → extended_nonneg_real",
	NumeralCoercion: true,
	Equations:       []string{"∀r:real. extended_of_real(r) = extended_of_option(some(max(r, &0)))"},
	Deps:            []registry.EntryLike{ExtendedNonnegRealDef.Retraction},
})}

// ExtendedToRealDef — the finite value: 0 at ∞, and otherwise the
// nonnegative real whose image the argument is.
var ExtendedToRealDef = extendedToRealDefThm{family.Define(registry.DefEntry{
	Name:  "ExtendedToRealDef",
	Key:   "prop_284ae7e1ebd381fd",
	Const: "extended_to_real",
	Type:  "extended_nonneg_real → real",
	Equations: []string{"∀x:extended_nonneg_real. " +
		"    extended_to_real(x) = " +
		"    COND(x = extended_infinity, &0, εr:real. &0 ≤ r ∧ extended_of_real(r) = x)"},
	Deps: []registry.EntryLike{ExtendedInfinityDef, ExtendedOfRealDef},
})}

// ExtendedLeDef — the order, written x ≤ y: everything lies below ∞,
// and two finite values compare as their reals do.
var ExtendedLeDef = extendedLeDefThm{family.Define(registry.DefEntry{
	Name:     "ExtendedLeDef",
	Key:      "prop_f7fd6b44f193b1f4",
	Const:    "extended_le",
	Type:     "extended_nonneg_real → extended_nonneg_real → bool",
	Notation: "x ≤ y",
	Equations: []string{"∀x y:extended_nonneg_real. " +
		"    extended_le(x, y) ⇔ " +
		"    y = extended_infinity ∨ x ≠ extended_infinity ∧ extended_to_real(x) ≤ extended_to_real(y)"},
	Deps: []registry.EntryLike{ExtendedInfinityDef, ExtendedToRealDef},
})}

// ExtendedLtDef — the strict order, written x < y: below and not equal.
var ExtendedLtDef = extendedLtDefThm{family.Define(registry.DefEntry{
	Name:      "ExtendedLtDef",
	Key:       "prop_198b1d49b768e7e9",
	Const:     "extended_lt",
	Type:      "extended_nonneg_real → extended_nonneg_real → bool",
	Notation:  "x < y",
	Equations: []string{"∀x y:extended_nonneg_real. extended_lt(x, y) ⇔ x ≤ y ∧ x ≠ y"},
	Deps:      []registry.EntryLike{ExtendedLeDef},
})}

// ExtendedAddDef — addition, written x + y: ∞ as soon as one summand
// is ∞, and otherwise the sum of the finite values.
var ExtendedAddDef = extendedAddDefThm{family.Define(registry.DefEntry{
	Name:     "ExtendedAddDef",
	Key:      "prop_e03c94c98e000ada",
	Const:    "extended_add",
	Type:     "extended_nonneg_real → extended_nonneg_real → extended_nonneg_real",
	Notation: "x + y",
	Equations: []string{"∀x y:extended_nonneg_real. " +
		"    extended_add(x, y) = " +
		"    COND(x = extended_infinity ∨ y = extended_infinity, " +
		"        extended_infinity, " +
		"        extended_of_real(extended_to_real(x) + extended_to_real(y)))"},
	Deps: []registry.EntryLike{ExtendedInfinityDef, ExtendedOfRealDef, ExtendedToRealDef},
})}

// ExtendedMulDef — multiplication, written x * y, with measure theory's
// convention 0 · ∞ = ∞ · 0 = 0: 0 as soon as one factor is 0, then ∞
// as soon as one factor is ∞, and otherwise the product of the finite
// values. The first branch spells extended_of_real(&0): the branch of a
// COND standing first has no partner to read a bare &0 into ⟦0, ∞⟧.
var ExtendedMulDef = extendedMulDefThm{family.Define(registry.DefEntry{
	Name:     "ExtendedMulDef",
	Key:      "prop_f534ea46201fbb1a",
	Const:    "extended_mul",
	Type:     "extended_nonneg_real → extended_nonneg_real → extended_nonneg_real",
	Notation: "x * y",
	Equations: []string{"∀x y:extended_nonneg_real. " +
		"    extended_mul(x, y) = " +
		"    COND(x = &0 ∨ y = &0, " +
		"        extended_of_real(&0), " +
		"        COND(x = extended_infinity ∨ y = extended_infinity, " +
		"            extended_infinity, " +
		"            extended_of_real(extended_to_real(x) * extended_to_real(y))))"},
	Deps: []registry.EntryLike{ExtendedInfinityDef, ExtendedOfRealDef, ExtendedToRealDef},
})}
