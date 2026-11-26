// definitions.go — the chapter's definitional layer: the pre-reals,
// signed differences of non-negative reals, and the arithmetic on
// them.
//
// Every operation but the embedding is written through fst and snd
// rather than by matching a pair pattern: the constants minted are
// identical (a pattern definition reduces to exactly this).
//
// A PRE-REAL is a pair (p, q) of hreals read as the difference p − q.
// Nothing is quotiented yet — the same difference has many pairs — so
// the type is just `prod(hreal, hreal)` and the chapter's own equality
// `treal_eq` is the one that matters: two pairs name the same
// difference when `p + q' = p' + q`, the cross-addition that avoids
// subtracting where subtraction is not defined. Order is read the same
// way.
//
// Negation swaps the two components, and multiplication is the
// familiar expansion of (p − q)(p' − q') collected into a positive and
// a negative part. Inversion is the one definition that must look at
// the sign: it splits on which component dominates, and sends zero to
// zero.

package nonneg_real_formal_diff

import (
	"github.com/euc-ai/xugo/library/registry"
)

// TrealOfNumDef — a number as a pre-real: itself, less nothing.
var TrealOfNumDef = trealOfNumDefThm{family.Define(registry.DefEntry{
	Name:      "TrealOfNumDef",
	Key:       "prop_b9a6abff44023d6c",
	Const:     "treal_of_num",
	Type:      "num → prod(hreal, hreal)",
	Equations: []string{"∀m:num. treal_of_num(m) = (hreal_of_num(m), hreal_of_num(0))"},
})}

// TrealNegDef — negation swaps the two components.
var TrealNegDef = trealNegDefThm{family.Define(registry.DefEntry{
	Name:      "TrealNegDef",
	Key:       "prop_17c3313fe39a4420",
	Const:     "treal_neg",
	Type:      "prod(hreal, hreal) → prod(hreal, hreal)",
	Equations: []string{"∀x:prod(hreal, hreal). treal_neg(x) = (snd(x), fst(x))"},
})}

// TrealAddDef — differences add componentwise.
var TrealAddDef = trealAddDefThm{family.Define(registry.DefEntry{
	Name:  "TrealAddDef",
	Key:   "prop_82f65bccae12e6a1",
	Const: "treal_add",
	Type:  "prod(hreal, hreal) → prod(hreal, hreal) → prod(hreal, hreal)",
	Equations: []string{
		"∀x y:prod(hreal, hreal). treal_add(x, y) = (fst(x) + fst(y), snd(x) + snd(y))",
	},
})}

// TrealMulDef — the expansion of (p − q)(p' − q'), collected into the
// part that adds and the part that subtracts.
var TrealMulDef = trealMulDefThm{family.Define(registry.DefEntry{
	Name:  "TrealMulDef",
	Key:   "prop_fe2100865e23cbba",
	Const: "treal_mul",
	Type:  "prod(hreal, hreal) → prod(hreal, hreal) → prod(hreal, hreal)",
	Equations: []string{
		"∀x y:prod(hreal, hreal). " +
			"    treal_mul(x, y) = (fst(x) * fst(y) + snd(x) * snd(y), fst(x) * snd(y) + snd(x) * fst(y))",
	},
})}

// TrealLeDef — one difference is below another by cross-addition,
// which asks nothing of subtraction.
var TrealLeDef = trealLeDefThm{family.Define(registry.DefEntry{
	Name:      "TrealLeDef",
	Key:       "prop_b074b25bda9ec994",
	Const:     "treal_le",
	Type:      "prod(hreal, hreal) → prod(hreal, hreal) → bool",
	Equations: []string{"∀x y:prod(hreal, hreal). treal_le(x, y) ⇔ fst(x) + snd(y) ≤ fst(y) + snd(x)"},
})}

// TrealEqDef — and two name the same difference by the same
// cross-addition, with equality in place of order.
var TrealEqDef = trealEqDefThm{family.Define(registry.DefEntry{
	Name:      "TrealEqDef",
	Key:       "prop_6195a5013b3c372c",
	Const:     "treal_eq",
	Type:      "prod(hreal, hreal) → prod(hreal, hreal) → bool",
	Equations: []string{"∀x y:prod(hreal, hreal). treal_eq(x, y) ⇔ fst(x) + snd(y) = fst(y) + snd(x)"},
})}

// TrealInvDef — inversion, the one operation that must know the sign:
// zero inverts to zero, and otherwise the dominating component's
// excess is inverted and placed on the matching side. The excess is
// named by choice — the d with fst(x) = snd(x) + d — since hreals
// carry no subtraction.
var TrealInvDef = trealInvDefThm{family.Define(registry.DefEntry{
	Name:  "TrealInvDef",
	Key:   "prop_3f22c31f71837b1f",
	Const: "treal_inv",
	Type:  "prod(hreal, hreal) → prod(hreal, hreal)",
	Equations: []string{"∀x:prod(hreal, hreal). " +
		"    treal_inv(x) = " +
		"    COND(fst(x) = snd(x), " +
		"        (hreal_of_num(0), hreal_of_num(0)), " +
		"        COND(snd(x) ≤ fst(x), " +
		"            (hreal_inv(εd:hreal. fst(x) = snd(x) + d), hreal_of_num(0)), " +
		"            (hreal_of_num(0), hreal_inv(εd:hreal. snd(x) = fst(x) + d))))"},
})}
