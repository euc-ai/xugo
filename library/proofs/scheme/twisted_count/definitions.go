package twisted_count

import (
	"github.com/euc-ai/xugo/library/registry"
)

var TwistedEvaluationsDef = twistedEvaluationsDefThm{family.Define(registry.DefEntry{
	Name: "TwistedEvaluationsDef",
	Key:  "prop_e8070dc53403c1ff",
	Reading: "The geometric points ev of C twisted by s at Q: ev(f)^Q " +
		"= ev(s f) on C. For the left action by inverse precomposition this " +
		"says Frobenius(ev) = s⁻¹·ev, and inversion keeps every subgroup sum.",
	Deps:  []registry.EntryLike{},
	Const: "twisted_evaluations",
	Type:  "field_ops(A) → set(A) → set(A) → num → permutation(A) → (set(A → A))",
	Equations: []string{
		"∀R:field_ops(A). ∀k C:set(A). ∀Q:num. ∀s:permutation(A). " +
			"    twisted_evaluations(R, k, C, Q, s) = " +
			"    {ev:(A → A) | " +
			"        ev ∈ geometric_evaluation_points(R, k, C) ∧ " +
			"        (∀x:A. x ∈ C ⇒ monoid_pow(R.mul, R.one, ev(x), Q) = ev(permutation_map(s, x)))}",
	},
})}

var TwistedEvaluationCountDef = twistedEvaluationCountDefThm{family.Define(registry.DefEntry{
	Name:  "TwistedEvaluationCountDef",
	Key:   "prop_3b05ae2683e0cb2",
	Deps:  []registry.EntryLike{TwistedEvaluationsDef},
	Const: "twisted_evaluation_count",
	Type:  "field_ops(A) → set(A) → set(A) → num → permutation(A) → num",
	Equations: []string{
		"∀R:field_ops(A). ∀k C:set(A). ∀Q:num. ∀s:permutation(A). " +
			"    twisted_evaluation_count(R, k, C, Q, s) = card(twisted_evaluations(R, k, C, Q, s))",
	},
})}

var GoodBaseCountDef = goodBaseCountDefThm{family.Define(registry.DefEntry{
	Name:  "GoodBaseCountDef",
	Key:   "prop_edb352edc0a84fe6",
	Deps:  []registry.EntryLike{},
	Const: "good_base_count",
	Type:  "ring_ops(A) → set(A) → (num → A) → num → num",
	Equations: []string{
		"∀R:ring_ops(A). ∀k:set(A). ∀a:(num → A). ∀Q:num. " +
			"    good_base_count(R, k, a, Q) = " +
			"    card({x:A | " +
			"            x ∈ R.carrier ∧ " +
			"            monoid_pow(R.mul, R.one, x, Q) = x ∧ " +
			"            polynomial_eval(R.add, R.zero, R.mul, R.one, a, x) ≠ R.zero})",
	},
})}
