package fixed_twist_models

import (
	"github.com/euc-ai/xugo/library/registry"
)

var FixedTwistModelsDef = fixedTwistModelsDefThm{family.Define(registry.DefEntry{
	Name: "FixedTwistModelsDef",
	Key:  "prop_438e0cdbfb14138",
	Reading: "(C, a) is a good open, and every s in the group has an integral " +
		"plane model (z(s), F(s), b(s)) of its twist field over k(t) whose affine " +
		"chart, with a(t) inverted, has over the constants l the same chart as C.",
	Deps:  []registry.EntryLike{},
	Const: "fixed_twist_models",
	Type: "field_ops(A) → " +
		"set(A) → " +
		"set(A) → " +
		"A → " +
		"set(A) → " +
		"(num → A) → " +
		"(permutation(A) → A) → " +
		"(permutation(A) → num → A) → " +
		"(permutation(A) → num) → " +
		"bool",
	Equations: []string{
		"∀R:field_ops(A). " +
			"∀k:set(A). " +
			"∀L:set(A). " +
			"∀C:set(A). " +
			"∀t:A. " +
			"∀a:(num → A). " +
			"∀z:(permutation(A) → A). " +
			"∀F:(permutation(A) → num → A). " +
			"∀b:(permutation(A) → num). " +
			"    fixed_twist_models(R, k, L, t, C, a, z, F, b) ⇔ " +
			"    galois_good_open(R, k, L, t, C, a) ∧ " +
			"    (∀s:permutation(A). " +
			"        s ∈ field_automorphisms(R, field_adjoin(R, k, {t}), L) ⇒ " +
			"        integral_plane_model(restrict_field(R, constant_twist_field(R, k, L, s)), " +
			"            k, " +
			"            t, " +
			"            z(s), " +
			"            F(s), " +
			"            b(s)) ∧ " +
			"        constant_chart(field_ring(R), " +
			"            finite_constants(field_ring(R), card(k), permutation_order(s)), " +
			"            C) = " +
			"        constant_chart(field_ring(R), " +
			"            finite_constants(field_ring(R), card(k), permutation_order(s)), " +
			"            ring_away(field_ring(R), " +
			"                plane_chart_zero( " +
			"                    restrict_ring(field_ring(R), constant_twist_field(R, k, L, s)), " +
			"                    k, " +
			"                    t, " +
			"                    z(s)), " +
			"                polynomial_eval(R.add, R.zero, R.mul, R.one, a, t))))",
	},
})}
