package constant_twist

import (
	"github.com/euc-ai/xugo/library/registry"
)

var constantFrobeniusLiftDef = constantFrobeniusLiftDefThm{family.Define(registry.DefEntry{
	Name: "constantFrobeniusLiftDef",
	Key:  "prop_8c134b40e113458d",
	Reading: "With e the order of s and l the field of |k|^e elements, an automorphism of " +
		"the composite of L and l over L raising each constant of l to its |k|-th power, chosen. " +
		"It fixes L, hence t; it is not the absolute power map on the whole function field.",
	Deps:  []registry.EntryLike{},
	Const: "constant_frobenius_lift",
	Type:  "field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀L:set(A). ∀s:permutation(A). " +
			"    constant_frobenius_lift(R, k, L, s) = " +
			"    εu:permutation(A). " +
			"        u ∈ " +
			"        field_automorphisms(R, " +
			"            L, " +
			"            constant_composite(R, " +
			"                L, " +
			"                finite_constants(field_ring(R), card(k), permutation_order(s)))) ∧ " +
			"        (∀c:A. " +
			"            c ∈ finite_constants(field_ring(R), card(k), permutation_order(s)) ⇒ " +
			"            permutation_map(u, c) = monoid_pow(R.mul, R.one, c, card(k)))",
	},
})}

var constantAutomorphismLiftDef = constantAutomorphismLiftDefThm{family.Define(registry.DefEntry{
	Name: "constantAutomorphismLiftDef",
	Key:  "prop_2e456622091fde26",
	Reading: "With e the order of s and l the field of |k|^e elements, an " +
		"automorphism of the composite of L and l over l agreeing with s on L, chosen.",
	Deps:  []registry.EntryLike{},
	Const: "constant_automorphism_lift",
	Type:  "field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀L:set(A). ∀s:permutation(A). " +
			"    constant_automorphism_lift(R, k, L, s) = " +
			"    εu:permutation(A). " +
			"        u ∈ " +
			"        field_automorphisms(R, " +
			"            finite_constants(field_ring(R), card(k), permutation_order(s)), " +
			"            constant_composite(R, " +
			"                L, " +
			"                finite_constants(field_ring(R), card(k), permutation_order(s)))) ∧ " +
			"        (∀x:A. x ∈ L ⇒ permutation_map(u, x) = permutation_map(s, x))",
	},
})}

var ConstantTwistAutomorphismDef = constantTwistAutomorphismDefThm{family.Define(registry.DefEntry{
	Name: "ConstantTwistAutomorphismDef",
	Key:  "prop_d3714cc6c2494a1",
	Reading: "The twisted automorphism φ of the composite of " +
		"L and l: the lift of s after the constant Frobenius lift.",
	Deps:  []registry.EntryLike{constantAutomorphismLiftDef, constantFrobeniusLiftDef},
	Const: "constant_twist_automorphism",
	Type:  "field_ops(A) → set(A) → set(A) → permutation(A) → permutation(A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀L:set(A). ∀s:permutation(A). " +
			"    constant_twist_automorphism(R, k, L, s) = " +
			"    permutation_compose(constant_automorphism_lift(R, k, L, s), " +
			"        constant_frobenius_lift(R, k, L, s))",
	},
})}

var ConstantTwistFieldDef = constantTwistFieldDefThm{family.Define(registry.DefEntry{
	Name: "ConstantTwistFieldDef",
	Key:  "prop_b2e5709134db1cc9",
	Reading: "The constant twist of L by s: the subfield of the " +
		"composite of L and l fixed by the powers of φ below the order e of s.",
	Deps:  []registry.EntryLike{ConstantTwistAutomorphismDef},
	Const: "constant_twist_field",
	Type:  "field_ops(A) → set(A) → set(A) → permutation(A) → set(A)",
	Equations: []string{
		"∀R:field_ops(A). ∀k:set(A). ∀L:set(A). ∀s:permutation(A). " +
			"    constant_twist_field(R, k, L, s) = " +
			"    fixed_field(constant_composite(R, " +
			"            L, " +
			"            finite_constants(field_ring(R), card(k), permutation_order(s))), " +
			"        {monoid_pow⟨A:permutation(A)⟩( " +
			"                (λp:permutation(A). λq:permutation(A). permutation_compose(p, q)), " +
			"                permutation_identity⟨A:A⟩, " +
			"                constant_twist_automorphism(R, k, L, s), " +
			"                j) | " +
			"            j:num | " +
			"            j < permutation_order(s)})",
	},
})}
