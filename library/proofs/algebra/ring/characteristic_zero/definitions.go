package characteristic_zero

import (
	_ "github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	_ "github.com/euc-ai/xugo/library/proofs/real/rational"
	"github.com/euc-ai/xugo/library/registry"
)

var IntegerMapDef = integerMapDefThm{family.Define(registry.DefEntry{
	Name:  "IntegerMapDef",
	Key:   "prop_df64b9cb7313a2d6",
	Deps:  []registry.EntryLike{},
	Const: "integer_map",
	Type:  "ring_ops(A) → int → A",
	Equations: []string{
		"∀R:ring_ops(A). ∀z:int. " +
			"    integer_map(R, z) = " +
			"    COND(0 ≤ z, " +
			"        monoid_pow(R.add, R.zero, R.one, num_of_int(z)), " +
			"        R.neg(monoid_pow(R.add, R.zero, R.one, num_of_int(-z))))",
	},
})}

var IntegerImageDef = integerImageDefThm{family.Define(registry.DefEntry{
	Name:      "IntegerImageDef",
	Key:       "prop_b306508d0691b279",
	Deps:      []registry.EntryLike{IntegerMapDef},
	Const:     "integer_image",
	Type:      "ring_ops(A) → set(A)",
	Equations: []string{"∀R:ring_ops(A). integer_image(R) = image(integer_map(R), 𝕌)"},
})}

var rationalMapDef = rationalMapDefThm{family.Define(registry.DefEntry{
	Name:  "rationalMapDef",
	Key:   "prop_ac9fc07ddee5edc3",
	Deps:  []registry.EntryLike{IntegerMapDef},
	Const: "rational_map",
	Type:  "field_ops(A) → real → A",
	Equations: []string{
		"∀F:field_ops(A). ∀r:real. " +
			"    rational_map(F, r) = " +
			"    COND(rational(r), " +
			"        εa:A. ∃m n:int. " +
			"            n ≠ 0 ∧ " +
			"            r = real_of_int(m) / real_of_int(n) ∧ " +
			"            a = F.mul(integer_map(field_ring(F), m), F.inv(integer_map(field_ring(F), n))), " +
			"        F.zero)",
	},
})}

var RationalImageDef = rationalImageDefThm{family.Define(registry.DefEntry{
	Name:  "RationalImageDef",
	Key:   "prop_fb4109a08c9f5b40",
	Deps:  []registry.EntryLike{rationalMapDef},
	Const: "rational_image",
	Type:  "field_ops(A) → set(A)",
	Equations: []string{
		"∀F:field_ops(A). rational_image(F) = image(rational_map(F), {r:real | rational(r)})",
	},
})}

var RationalValueDef = rationalValueDefThm{family.Define(registry.DefEntry{
	Name: "RationalValueDef",
	Key:  "prop_1f580467fd6216f3",
	Reading: "Inverse to the rational embedding only on " +
		"its image; no assertion about arbitrary host elements.",
	Deps:  []registry.EntryLike{rationalMapDef},
	Const: "rational_value",
	Type:  "field_ops(A) → A → real",
	Equations: []string{
		"∀F:field_ops(A). ∀a:A. rational_value(F, a) = εr:real. rational(r) ∧ rational_map(F, r) = a",
	},
})}

var IntegerValueDef = integerValueDefThm{family.Define(registry.DefEntry{
	Name:      "IntegerValueDef",
	Key:       "prop_27754ace2cf9d2fa",
	Deps:      []registry.EntryLike{IntegerMapDef},
	Const:     "integer_value",
	Type:      "ring_ops(A) → A → int",
	Equations: []string{"∀R:ring_ops(A). ∀a:A. integer_value(R, a) = εz:int. integer_map(R, z) = a"},
})}
